(defstruct (node
            (:constructor nil))
  (number nil :type (or list index))
  (successor nil :type (or boolean node))
  (accept-state nil :type boolean)
  (direct-predecessors nil :type boolean))

(defstruct (accept-node
            (:include node)))

(defstruct (char-node
            (:include node))
  (chars nil :type cons :read-only t))

(defstruct (choice-node
            (:include node))
  (allow-empty t :type boolean)
  (choices nil :type cons :read-only t))

(defstruct (repeat-node
            (:include choice-node)))

(defun filter-choices (choices &key allow-empty)
  (let ((chars '())
        (acc '()))
    (dolist (choice choices
                    (values (append (and chars
                                         (list (make-char-node
                                                :chars chars
                                                :successor (make-accept-node
                                                            :direct-predecessors t))))
                                    (nreverse acc))
                            allow-empty))
      (typecase choice
        (accept-node
         (setf allow-empty t))
        (char-node
         (if (accept-node-p (node-successor choice))
             (setf chars (append (char-node-chars choice)
                                 chars))
             (push choice acc)))
        (null)
        (t
         (when (and (choice-node-p choice)
                    (accept-node-p (node-successor choice))
                    (choice-node-allow-empty choice))
           (setf allow-empty t))
         (push choice acc))))))

(defun find-next-to-last (node)
  (loop until (accept-node-p (node-successor node))
        do (setf node (node-successor node))
        finally (return node)))

;; nil: fail
(defun parse-regexp (regexp)
  (declare (optimize debug))
  (when (null regexp)
    (return-from parse-regexp (make-accept-node)))
  (destructuring-bind (head . tail) regexp
    (if (stringp head)
        (parse-regexp (concatenate 'list head tail))
        (let ((successor (parse-regexp tail)))
          (unless successor
            (return-from parse-regexp nil))
          (etypecase head
            (character
             (setf (node-direct-predecessors successor) t)
             (make-char-node :chars (list head)
                             :successor successor))
            ((cons (eql ?))
             (let ((choice (parse-regexp `((or ,(rest head))))))
               (cond ((choice-node-p choice)
                      (setf (choice-node-allow-empty choice) t
                            (choice-node-successor choice) successor)
                      choice)
                     (t
                      (make-choice-node :choices (list choice)
                                        :successor successor
                                        :allow-empty t)))))
            ((cons (eql or))
             (let* ((choices (remove-duplicates
                              (loop for choice in (rest head)
                                    for parse = (parse-regexp choice)
                                    append (if (and (choice-node-p parse)
                                                    (not (repeat-node-p parse))
                                                    (accept-node-p
                                                     (node-successor parse)))
                                               (choice-node-choices parse)
                                               (list parse))))))
               (multiple-value-bind (choices allow-empty)
                   (filter-choices choices)
                 (cond ((null choices)
                        (and allow-empty successor))
                       ((null (rest choices))
                        (let* ((choice (first choices))
                               (last (find-next-to-last choice)))
                          (when (char-node-p last)
                            (setf (node-direct-predecessors successor) t))
                          (setf (node-successor last) successor)
                          choice))
                       (t
                        (make-choice-node :choices choices
                                          :allow-empty allow-empty
                                          :successor successor))))))
            ((cons (member + *))
             (let* ((allow-empty (eql (first head) '*))
                    (body (parse-regexp (rest head)))
                    (choices (if (accept-node-p (node-successor body))
                                 (typecase body
                                   (repeat-node
                                    (setf allow-empty (or allow-empty
                                                          (repeat-node-allow-empty body)))
                                    (repeat-node-choices body))
                                   (choice-node
                                    (choice-node-choices body))
                                   (null nil)
                                   (t (list body)))
                                 (list body))))
               (multiple-value-bind (choices allow-empty)
                   (filter-choices choices :allow-empty allow-empty)
                 (if choices
                     (make-repeat-node :choices choices
                                       :allow-empty allow-empty
                                       :successor successor)
                     (and allow-empty successor))))))))))

(defvar *counter*)
(defvar *reuse*)
(defvar *tail-position-p*)

(defun counter ()
  (or (shiftf *reuse* nil)
      (prog1 (the (mod 128) *counter*)
        (when (= *counter* 63)
          (incf *counter*))
        (incf *counter*))))

(defun adjacent-numbers (from to)
  (and (integerp from)
       (integerp to)
       (or (= (1+ from) to)
           (and (= 63 from)
                (= 65 to)))))

(defgeneric %dfo (node))
(defmethod %dfo :before ((node node))
  (assert (not (node-number node))))
(defmethod %dfo ((node node))
  (when (repeat-node-p node)
    (setf *reuse* nil))
  (when (node-direct-predecessors node)
    (setf (node-number node) (counter))))

(defmethod %dfo ((node accept-node))
  (setf (node-number node) (counter)))

(defmethod %dfo ((node char-node))
  (setf (node-number node) (counter))
  (%dfo (node-successor node))
  (assert (adjacent-numbers (node-number node)
                            (node-number (node-successor node)))))

(defmethod %dfo ((node choice-node))
  (call-next-method)
  (let ((*reuse* (or (node-number node)
                     *reuse*))
        (reused nil))
    (when *reuse*
      (block out
        (flet ((try (choice)
                 (unless (repeat-node-p choice)
                   (%dfo choice)
                   (setf reused choice)
                   (return-from out))))
          (let ((*tail-position-p* nil))
            (mapc #'try (choice-node-choices node)))
          (when (choice-node-allow-empty node)
            (let ((*tail-position-p* (and *tail-position-p*
                                          (choice-node-allow-empty node))))
              (try (node-successor node)))))))
    (flet ((maybe-dfo (node)
             (unless (eql node reused)
               (%dfo node))))
      (let ((*tail-position-p* nil))
        (mapc #'maybe-dfo (choice-node-choices node)))
      (let ((*tail-position-p* (and *tail-position-p*
                                    (choice-node-allow-empty node))))
        (maybe-dfo (node-successor node))))))

(defmethod %dfo :after ((node choice-node))
  (unless (node-number node)
    (let ((number '()))
      (flet ((walk (succ)
               (setf number (union number
                                   (alexandria:ensure-list
                                    (node-number succ))))))
        (mapc #'walk (choice-node-choices node))
        (when (choice-node-allow-empty node)
          (walk (node-successor node))))
      (setf (node-number node) (sort number #'<)))))

(defun dfo (node)
  (let ((*counter* 1) ;; 0: accept state
        (*reuse* nil)
        (*tail-position-p* t))
    (%dfo node)
    node))

(defvar *self-loops*)

(defgeneric %nontrivial-transitions (node))
(defmethod %nontrivial-transitions ((node node)))
(defmethod %nontrivial-transitions ((node char-node))
  (push (list (char-node-chars node)
              (node-number (node-successor node)))
        *transitions*)
  (%nontrivial-transitions (node-successor node)))

(defmethod %nontrivial-transitions ((node choice-node))
  (mapc #'%nontrivial-transitions (choice-node-choices node))
  (%nontrivial-transitions (node-successor node)))

(defun nontrivial-transitions (regexp)
  (let ((*transitions* '())
        (*self-loops* '()))
    (%nontrivial-transitions regexp)
    (nreverse *transitions*)))

(defvar *continuation*)
(defvar *transitions*)
(defvar *accept*)

(defun register-epsilons (from continuation)
  (mapc (lambda (k)
          (push (cons from k) *transitions*))
        continuation))

(defgeneric %epsilon-transitions (node))
(defmethod %epsilon-transitions ((node char-node))
  (%epsilon-transitions (node-successor node)))

(defmethod %epsilon-transitions ((node accept-node))
  (let ((number (node-number node)))
    (when number
      (if (equal *continuation* '(0))
          (push number *accept*)
          (register-epsilons number *continuation*)))))

(defmethod %epsilon-transitions ((node choice-node))
  (let ((number (node-number node))
        (successor (node-successor node)))
    (when (integerp number)
      (let ((continuation (reduce #'union (choice-node-choices node)
                                  :key (lambda (x)
                                         (alexandria:ensure-list (node-number x))))))
        (when (choice-node-allow-empty node)
          (setf continuation
                (union continuation
                       (if (accept-node-p successor)
                           *continuation*
                           (alexandria:ensure-list (node-number successor))))))
        (register-epsilons number continuation))))
  (let* ((successor (node-successor node))
         (*continuation* (if (accept-node-p successor)
                             *continuation*
                             (alexandria:ensure-list (node-number successor)))))
    (when (repeat-node-p node)
      (setf *continuation* (union *continuation*
                                  (alexandria:ensure-list (node-number node)))))
    (mapc #'%epsilon-transitions (choice-node-choices node)))
  (%epsilon-transitions (node-successor node)))

(defun epsilon-transitions (regexp)
  (let ((*continuation* (list 0))
        (*transitions* '())
        (*accept* (list 0)))
    (%epsilon-transitions regexp)
    (values (nreverse *transitions*)
            (nreverse *accept*))))

(defun build-transition-table (nontrivial-transitions)
  (let ((table (make-array (* 2 +state-size+)
                           :element-type '(unsigned-byte 64)
                           :initial-element 0)))
    (loop for (chars number) in nontrivial-transitions
          for chunk = (truncate number +chunk-size+)
          for mask = (ash 1 (mod number +chunk-size+))
          do (dolist (char chars)
               (let ((index (+ chunk (* (char-code char) 2))))
                 (setf (aref table index) (logior mask
                                                  (aref table index))))))
    table))

(defun regexp-code (regexp)
  (let* ((regexp (dfo (parse-regexp regexp)))
         (nontrivial (nontrivial-transitions regexp)))
    (multiple-value-bind (epsilon accept)
        (epsilon-transitions regexp)
      (setf epsilon (transitive-closure epsilon))
      (when (some (lambda (nontrivial)
                    ;; 63 expects to be able to shift
                    ;; into 65
                    (= 65 (second nontrivial)))
                  nontrivial)
        (push (cons 63 64) epsilon))
      (let ((accept-mask 0))
        (dolist (accept accept)
          (setf (logbitp accept accept-mask) 1))
        (multiple-value-bind (body around)
            (compile-adjacency epsilon 'state :raw t)
          (values `(lambda (state char)
                     (declare (type (simd-pack integer) state)
                              (type base-char char))
                     (let* ((table (load-time-value (the (simple-array (unsigned-byte 64)
                                                                       (256))
                                                         (build-transition-table ',nontrivial))
                                                    t))
                            (mask (vref table (char-code char)))
                            (state (pand mask (psllq state 1)))
                            (state ,body))
                       state))
                  around
                  accept-mask
                  (let ((mask 2)
                        (transitions (transpose epsilon)))
                    (dolist (i (alexandria:ensure-list (node-number regexp))
                               mask)
                      (setf (logbitp i mask) 1)
                      (dolist (i (aref transitions i))
                        (setf (logbitp i mask) 1))))))))))

(defun regexp-loop (regexp &key ignore-prefix)
  (multiple-value-bind (body around accept-mask start-mask)
      (regexp-code regexp)
    `(lambda (string)
       (declare (type simple-base-string string))
       (let* (,@(and ignore-prefix
                     `((initial (to-simd-pack-integer
                                 ,(%make-simd-pack-ub128 start-mask)))))
              (state ,(if ignore-prefix
                          'initial
                          (%make-simd-pack-ub128 start-mask)))
              (idx 0)
              (length (length string)))
         (declare (type (simd-pack integer) state)
                  (type (mod ,most-positive-fixnum) idx length)
                  (optimize speed (safety 0)))
         (,@(or around '(progn))
          (block nil
            (loop
             (when (ptest state ,(%make-simd-pack-ub128 accept-mask))
               (return (values t idx)))
             (when (>= idx length)
               (return (values nil idx)))
             (setf state ,(let ((transition `(,body state (aref string idx))))
                            (if ignore-prefix
                                `(por ,transition initial)
                                transition)))
             (unless (ptest state state)
               (return (values nil idx)))
             (incf idx))))))))
