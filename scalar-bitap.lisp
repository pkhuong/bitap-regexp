(defpackage "SCALAR-BITAP"
  (:use "CL")
  (:import-from "REGEXP-TO-NFA"
                "COMPRESSED-NFA" "COMPRESSED-NFA-ID-COUNT"
                "COMPRESSED-NFA-CHARACTER-TRANSITIONS" "COMPRESSED-NFA-EPSILONS-ADJACENCY"
                "COMPRESSED-NFA-START-IDS" "COMPRESSED-NFA-ACCEPT-IDS")
  (:import-from "ALEXANDRIA" "HASH-TABLE-ALIST")
  (:export "MAKE-MATCHER" "MAKE-NFA-LOOP" "MAKE-NFA-BODY" "BASE-CHAR-TABLE"))

(in-package "SCALAR-BITAP")

(declaim (optimize debug))

(defun group-masks (adjacencies)
  (let ((groups (make-hash-table :test 'equal))) ; adjacency lists are sorted
    ;; merge identical rows (modulo diagonal)
    (loop for i upfrom 0
          for adjacency in adjacencies
          for key = adjacency #+nil (remove i adjacency)
          when (not (equal key (list i)))
          do (push i (gethash key groups)))
    ;; Try to merge in patterns like
    ;; i -> {j, k}
    ;; x -> {i, j, k}
    (loop for i upfrom 0
          for adjacency in adjacencies
          for key = (remove i adjacency)
          for new-key = (sort (copy-list (adjoin i adjacency)) #'<)
          when (and key ; not a noop
                    (null (cdr (gethash key groups))) ; alone
                    (gethash new-key groups)) ; and could be coupled
          do (remhash key groups)
             (push i (gethash new-key groups)))
    (let ((masks '())
          (remainder '()))
      (maphash (lambda (mask keys)
                 (if (rest keys)
                     (push (cons mask (sort keys #'<)) masks)
                     (push (cons mask (car keys)) remainder)))
               groups)
      (values (sort masks #'< :key #'second)
              (sort remainder #'< :key #'cdr)))))

(defun group-shifts (singletons)
  ; map shift amount -> origin states
  (let ((shifts (make-hash-table))
        (others '()))
    (loop for entry in singletons
          for ((dst . rest) . src) = entry
          do (if rest
                 (push entry others)
                 (push src (gethash (- dst src) shifts))))
    (values (sort (hash-table-alist shifts) #'<
                  :key (lambda (x)
                         (car (last x))))
            (nreverse others))))

;; if t, higher-valued states are at lower order bits
;; and flipped by that bitwidth
(defvar *flip*)
(defvar *bitwidth* nil)

(defun mask-from-indices (indices)
  (let ((mask 0))
    (dolist (index indices mask)
      (let ((index (if *flip*
                       (- *bitwidth* 1 index)
                       index)))
        (setf (ldb (byte 1 index) mask) 1)))))

(defun emit-group (group)
  (destructuring-bind (mask . states)
      group
    `(lambda (source)
       (if (logtest source ,(mask-from-indices states))
           ,(mask-from-indices mask)
           0))))

(defun emit-shift (shift)
  (destructuring-bind (amount . indices)
      shift
    (when *flip*
      (setf amount (- amount)))
    `(lambda (source)
       (ash (logand source ,(mask-from-indices indices))
            ,amount))))

(defun emit-singleton (singleton)
  (destructuring-bind (mask . index)
      singleton
    (when *flip*
      (setf index (- *bitwidth* 1 index)))
    `(lambda (source)
       (if (logbitp ,index source)
           ,(mask-from-indices mask)
           0))))

(defun interleave (&rest lists)
  (loop while (some #'identity lists)
        nconc (loop for list-head on lists
                    for list = (first list-head)
                    when list
                      collect (pop (first list-head)))))

(defun epsilon-function (adjacency)
  (multiple-value-bind (groups remainder)
      (group-masks adjacency)
    (multiple-value-bind (shifts singletons)
        (group-shifts remainder)
      (let ((transitions (interleave (mapcar #'emit-group groups)
                                     (mapcar #'emit-shift shifts)
                                     (mapcar #'emit-singleton singletons))))
        `(lambda (source)
           (let* ((acc source)
                  ,@(mapcar (lambda (function)
                              `(acc (logior acc
                                            (,function source))))
                            transitions))
             acc))))))

(defun base-char-table (character-transitions element-type
                        &key (bitwidth *bitwidth*)
                          (flip *flip*))
  (let ((result (make-array 256 :element-type element-type
                                :initial-element 0)))
    (loop for (chars from to) in character-transitions
          do (assert (= (1+ from) to))
             (when flip
               (setf to (- bitwidth 1 to)))
             (dolist (char chars)
               (setf (ldb (byte 1 to) (aref result (char-code char)))
                     1)))
    result))

(defun make-nfa-body (nfa &key ((:bitwidth *bitwidth*) (compressed-nfa-id-count nfa))
                            (element-type `(unsigned-byte ,*bitwidth*))
                            ((:flip *flip*))
                            &allow-other-keys)
  (let ((epsilon (epsilon-function (compressed-nfa-epsilons-adjacency nfa))))
    (values `(lambda (state char)
               (declare (type base-char char))
               (let* ((table (load-time-value
                              (the (simple-array ,element-type (256))
                                   (base-char-table ',(compressed-nfa-character-transitions
                                                       nfa)
                                                    ',element-type
                                                    :bitwidth ',*bitwidth*
                                                    :flip ',*flip*))
                              t))
                      (state (logand (ash state ,(if *flip* -1 1))
                                     (aref table (char-code char)))))
                 (,epsilon state)))
            (mask-from-indices (compressed-nfa-start-ids nfa))
            (mask-from-indices (compressed-nfa-accept-ids nfa)))))

(defun make-nfa-loop (nfa &key ((:bitwidth *bitwidth*) (compressed-nfa-id-count nfa))
                            (element-type `(unsigned-byte ,*bitwidth*))
                            ((:flip *flip*))
                            ignore-prefix
                            policy
                            &allow-other-keys)
  (let ((min-width (compressed-nfa-id-count nfa)))
    (setf *bitwidth* (max min-width *bitwidth*)))
  (let ((least-type `(unsigned-byte ,*bitwidth*)))
    (unless (subtypep least-type element-type)
      (setf element-type least-type)))
  (multiple-value-bind (body start accept)
      (make-nfa-body nfa :bitwidth *bitwidth*
                         :element-type element-type
                         :flip *flip*)
    (let ((advance `(,body state (aref string i))))
      (when ignore-prefix
        (setf advance `(logior ,advance ,start)))
      `(lambda (string start end)
         (declare (type simple-base-string string)
                  (type (mod ,most-positive-fixnum) start)
                  (type (or null (mod ,most-positive-fixnum)) end))
         (let ((i start)
               (end (let ((length (length string)))
                      (if (or (null end)
                              (< length end))
                          length
                          end)))
               (state ,start))
           (declare (type (mod ,most-positive-fixnum) i end)
                    (type ,element-type state)
                    #+sbcl (optimize (sb-c::insert-array-bounds-checks 0)))
           ,policy
           (loop
            (when ,(if (= 1 (logcount accept))
                       `(logbitp ,(1- (integer-length accept)) state)
                       `(logtest state ,accept))
              (return (values i t)))
            (when (>= i end)
              (return (values i nil)))
            (setf state ,advance)
            ,(unless ignore-prefix
               `(when (zerop state)
                  (return (values i nil))))
            (incf i)))))))

(defun make-matcher (regexp &rest args
                     &key
                       (max-width #+sbcl sb-vm:n-word-bits
                                  #-sbcl (integer-length most-positive-fixnum))
                       bitwidth element-type
                       flip ignore-prefix policy
                       (compile t))
  (declare (ignore element-type flip ignore-prefix policy))
  (when bitwidth
    (setf max-width (max max-width bitwidth)))
  (let* ((nfa (regexp-to-nfa:convert-regexp regexp))
         (state-count (compressed-nfa-id-count nfa)))
    (cond ((and bitwidth (> state-count bitwidth))
           (cerror "Ignore bitwidth limit"
                   "Converting ~S to an NFA results in ~A states (greater than ~(~S~) ~A)"
                   regexp state-count :bitwidth max-width)
           (setf args `(,@args :bitwidth ,state-count)))
          ((> state-count max-width)
           (warn "Converting ~S to an NFA results in ~A states (greater than ~A)"
                 regexp state-count max-width)))
    (let ((source (apply 'make-nfa-loop nfa args)))
      (if compile
          (compile nil source)
          source))))
