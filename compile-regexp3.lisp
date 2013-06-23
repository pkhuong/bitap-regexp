(defpackage "REGEXP-TO-NFA"
  (:use "CL")
  (:export "PARSE-REGEXP"
           "DFO"
           "DRAW-REGEXP"
           
           "CONVERT-REGEXP-TO-COMPRESSED-NFA"
           "REMOVE-USELESS-STATES"
           "ENSURE-STATE-NUMBER-GAPS"
           "REMOVE-USELESS-EPSILONS"

           "CONVERT-REGEXP"
           
           "DRAW-COMPRESSED-NFA"
           "COMPRESSED-NFA" "COMPRESSED-NFA-ID-COUNT"
           "COMPRESSED-NFA-CHARACTER-TRANSITIONS" "COMPRESSED-NFA-EPSILONS-ADJACENCY"
           "COMPRESSED-NFA-START-IDS" "COMPRESSED-NFA-ACCEPT-IDS"))

(in-package "REGEXP-TO-NFA")

(defstruct (node
            (:constructor nil))
  id)

(defstruct (accept-node
            (:include node))
  repeat-predecessor-p)

(defstruct (nonterminal-node
            (:include node)
            (:constructor nil))
  successor)

(defstruct (char-node
            (:include nonterminal-node))
  chars)

(defstruct (choice-node
            (:include nonterminal-node))
  choices)

(defstruct (repeat-node
            (:include nonterminal-node))
  body)

(defun ?-p (x)
  (and (symbolp x)
       (string-equal x "?")))

(defun parse-regexp (regexp)
  (when (typep regexp `(or character string
                           (cons (member or ? * +))))
    ;; regexp designator.
    (return-from parse-regexp (parse-regexp (list regexp))))
  (assert (listp regexp))
  (when (null regexp)
    (return-from parse-regexp (make-accept-node)))
  (destructuring-bind (pattern . regexp) regexp
    (etypecase pattern
      (null
       (parse-regexp regexp))
      ((cons (satisfies ?-p))
       (parse-regexp `((or () ,(rest pattern)) ,@regexp)))
      ((cons (eql *))
       (parse-regexp `((+ (or () ,(rest pattern))) ,@regexp))
       #+nil
       (parse-regexp `((or () ((+ ,@(rest pattern)))) ,@regexp)))
      (string
       (parse-regexp `(,@(coerce pattern 'list) ,@regexp)))
      (character
       (make-char-node :chars (list pattern)
                       :successor (parse-regexp regexp)))
      ((cons (eql or))
       (let* ((epsilon nil) ; any empty string?
              (chars   '()) ; set of chars to match
              (choices  '()))
         (labels ((walk (choice)
                    (cond ((accept-node-p choice)
                           (setf epsilon choice))
                          ((and (char-node-p choice)
                                (accept-node-p (nonterminal-node-successor choice)))
                           (setf chars (union chars (char-node-chars choice))))
                          ((and (choice-node-p choice)
                                (accept-node-p (nonterminal-node-successor choice)))
                           (mapc #'walk (choice-node-choices choice)))
                          (t
                           (push choice choices)))))
           (mapc (lambda (pattern)
                   (walk (parse-regexp pattern)))
                 (rest pattern)))
         (setf choices (nreverse choices))
         (when epsilon
           (push epsilon choices))
         (when chars
           (push (make-char-node :chars chars
                                 :successor (make-accept-node))
                 choices))
         (make-choice-node :choices choices
                           :successor (parse-regexp regexp))))
      ((cons (eql +))
       (let ((body (parse-regexp (rest pattern))))
         (cond ((and (repeat-node-p body)
                     (accept-node-p (nonterminal-node-successor body)))
                (setf (nonterminal-node-successor body) (parse-regexp regexp))
                body)
               (t
                (make-repeat-node :body body
                                  :successor (parse-regexp regexp)))))))))

(defgeneric %dfo (node))

(defvar *virtual-counter*)
(defun virtual-id ()
  (prog1 *virtual-counter*
    (incf *virtual-counter*)))

(defvar *epsilon-transitions*)
(defvar *char-nodes*)
(defvar *nodes*)

(defun register-epsilon (from to)
  (when (node-p from)
    (setf from (the integer (node-id from))))
  (when (node-p to)
    (setf to (the integer (node-id to))))
  (pushnew to (gethash from *epsilon-transitions*)))

(defmethod %dfo :before ((node node))
  (let ((id (setf (node-id node) (virtual-id))))
    (assert (= id (length *nodes*)))
    (vector-push-extend node *nodes*)))

(defmethod %dfo ((node accept-node))
  node)

(defmethod %dfo ((node nonterminal-node))
  (%dfo (nonterminal-node-successor node)))

(defmethod %dfo ((node char-node))
  (vector-push-extend (node-id node) *char-nodes*)
  (prog1 (call-next-method)
    (assert (= (1+ (node-id node))
               (node-id (nonterminal-node-successor node))))))

(defmethod %dfo ((node choice-node))
  (let* ((choices (choice-node-choices node))
         (choice-tails (mapcar #'%dfo choices))
         (successor (nonterminal-node-successor node))
         (tail (call-next-method node)))
    (loop for choice in choices
            for tail in choice-tails
          do (register-epsilon node choice)
             (register-epsilon tail successor))
    tail))

(defmethod %dfo ((node repeat-node))
  (let* ((body (repeat-node-body node))
         (body-tail (%dfo body))
         (succ (nonterminal-node-successor node))
         (tail (call-next-method)))
    (register-epsilon node body)
    (register-epsilon body-tail succ)
    (register-epsilon body-tail node)
    tail))

(defun dfo (regexp)
  (let* ((*virtual-counter* 0)
         (*char-nodes* (make-array 10 :adjustable t :fill-pointer 0))
         (*nodes* (make-array 10 :adjustable t :fill-pointer 0))
         (*epsilon-transitions* (make-hash-table))
         (tail (%dfo regexp)))
    (values regexp tail
            (coerce *nodes* 'simple-vector)
            (coerce *char-nodes* 'simple-vector)
            *epsilon-transitions*)))

(defun draw-regexp (nodes char-nodes epsilons)
  (format t "~
digraph G {
	rankdir=LR;
	bgcolor=transparent;
")
  (loop with last = (1- (length nodes))
        for i upfrom 0
        for node across nodes
        do (format t "	n~A [label=\"~A\" shape=~A];~%"
                   i i
                   (etypecase node
                     (accept-node
                      (if (= i last)
                          "doublecircle"
                          "cds"))
                     (char-node
                      "circle")
                     (choice-node
                      "diamond")
                     (repeat-node
                      "square"))))
  (loop for char-node-id across char-nodes
        for char-node = (aref nodes char-node-id)
        do (format t "	n~A -> n~A [label=\"~{&#~A;~}\"];~%"
                   (node-id char-node)
                   (node-id (nonterminal-node-successor char-node))
                   (mapcar #'char-code (char-node-chars char-node))))
  (maphash (lambda (from dests)
             (dolist (dest dests)
               (format t "	n~A -> n~A ~A;~%"
                       from dest
                       (if (> from dest)
                           "[color=blue constraint=false]"
                           "[color=blue]"))))
           epsilons)
  (format t "}~%"))

;; skip node directly to char/accept nodes
(defun reachable-interesting-nodes (state nodes transitions)
  (declare (optimize debug))
  (let ((seen (make-hash-table))
        (last-state (1- (length nodes)))
        (reachable '()))
    (labels ((walk (state)
               (when (gethash state seen)
                 (return-from walk))
               (setf (gethash state seen) t)
               (when (or (char-node-p (aref nodes state))
                         (= state last-state))
                 (push state reachable))
               (mapc #'walk (gethash state transitions))))
      (walk state)
      (setf (gethash state transitions)
            (remove state (sort reachable #'<))))))

(defun close-epsilon-transitions (nodes transitions)
  (maphash (lambda (state _)
             _
             (setf (gethash state transitions)
                   (reachable-interesting-nodes state nodes transitions)))
           transitions)
  transitions)

;; virtual states are in the same eqv class when they
;; are reachable exactly after the same set of CHAR nodes.
;; Also do the same for start nodes.
;;
;; Mark-class adds "root" to the set of nodes after which
;; each state reachable via root is active.
;;
;; Reverse class is thus (incrementally) a table from virtual
;; state to equivalence class designator.
(defun mark-class (reverse-classes root transitions)
  (declare (type hash-table reverse-classes transitions)
           (type integer root))
  (let ((seen (make-hash-table))
        (mark root))
    (labels ((mark (root)
               (when (gethash root seen)
                 (return-from mark))
               (setf (gethash root seen) t)
               (push mark (gethash root reverse-classes))
               (map nil #'mark (gethash root transitions))))
      (mark root))))

(defun merge-equivalence-class (id reverse-classes nodes transitions)
  (when (or (char-node-p (aref nodes id))
            (= id (1- (length nodes))))
    (return-from merge-equivalence-class))
  (let ((active (gethash id reverse-classes))
        (succ   (gethash id transitions)))
    (when succ
      (let ((widened (reduce #'intersection succ
                             :key (lambda (id)
                                    (gethash id reverse-classes)))))
        (assert (subsetp active widened))
        (setf (gethash id reverse-classes) widened)))))

(defun merge-all-classes (reverse-classes nodes transitions)
  (maphash (lambda (id _) _
             (merge-equivalence-class id reverse-classes nodes transitions))
           reverse-classes)
  reverse-classes)

;; Invert the virtual state -> class designator table
;; return a vector of eqv class id -> set of virtual states in class
;; and a reverse mapping from virtual state -> eqv class id
(defun make-classes (reverse-classes)
  (declare (optimize debug))
  (let ((%classes (make-hash-table :test #'equal))
        (id-count 0))
    (maphash (lambda (id class)
               (setf id-count (max (1+ id) id-count))
               (push id (gethash class %classes)))
             reverse-classes)
    (let ((classes (make-array (hash-table-count %classes)
                               :fill-pointer 0))
          (rclasses (make-array id-count :initial-element nil)))
      (maphash (lambda (class ids) class
                 (let ((class-id (length classes)))
                   (dolist (id ids)
                     (setf (aref rclasses id) class-id)))
                 (vector-push-extend ids classes))
               %classes)
      (values classes rclasses))))

(defstruct equivalence-class
  number
  virtual-ids
  state-ids ; list of (id . character)
  epsilon-successors
  free-ids ; list of unused ids
  char-successors ; popped off to build state-ids
  )

(defun lex< (x y)
  (loop
   (cond ((and (null x)
               (null y))
          (return nil))
         ((null x)
          (return t))
         ((null y)
          (return nil))
         (t
          (let ((x (pop x))
                (y (pop y)))
            (when (/= x y)
              (return (< x y))))))))

(defun canonicalise-char-successors (successors classes)
  (declare (optimize debug))
  (let ((reverse (make-hash-table)))
    (loop for (chars . class) in successors
          do (setf (gethash class reverse)
                   (union chars (gethash class reverse))))
    (let ((acc '()))
      (maphash (lambda (class chars)
                 (push (cons chars class) acc))
               reverse)
      (stable-sort (nreverse acc)
                   #'lex<
                   :key (lambda (transition)
                          (destructuring-bind (chars . class)
                              transition
                            chars
                            (equivalence-class-virtual-ids
                             (aref classes class))))))))

;; Rebuild equivalence class structs: each equivalence class inherits
;; its virtual states' epsilon and character transitions (translated
;; into eqv class terms)
(defun make-equivalence-classes (classes rclasses nodes char-nodes epsilons)
  (declare (optimize debug))
  (let* ((i -1)
         (classes (map 'simple-vector
                       (lambda (class)
                         (make-equivalence-class :number (incf i)
                                                 :virtual-ids (sort class #'<)
                                                 :state-ids nil
                                                 :epsilon-successors nil
                                                 :free-ids nil
                                                 :char-successors nil))
                       classes)))
    (map nil (lambda (id)
               (let ((node (aref nodes id))
                     (in-class (aref rclasses id))
                     (out-class (aref rclasses (1+ id))))
                 (push (cons (char-node-chars node) out-class)
                       (equivalence-class-char-successors
                        (aref classes in-class)))))
         char-nodes)
    (map nil (lambda (class)
               (setf (equivalence-class-char-successors class)
                     (canonicalise-char-successors
                      (equivalence-class-char-successors class)
                      classes)))
         classes)
    (maphash (lambda (src dests)
               (let ((in-class (aref rclasses src)))
                 (when in-class
                   (map nil (lambda (dest)
                              (pushnew (aref rclasses dest)
                                       (equivalence-class-epsilon-successors
                                        (aref classes in-class))))
                        dests))))
             epsilons)
    (values classes rclasses)))

(defun equivalence-classes (nodes char-nodes epsilons)
  (let ((reverse-classes (make-hash-table))) ; id -> eqv class
    (mark-class reverse-classes 0 epsilons)
    (map nil (lambda (node)
               (mark-class reverse-classes
                           (1+ node)
                           epsilons))
         char-nodes)
    (merge-all-classes reverse-classes nodes epsilons)
    (multiple-value-bind (classes rclasses)
        (make-classes reverse-classes)
      (make-equivalence-classes classes rclasses nodes char-nodes epsilons))))

(defvar *counter*)
(defun number-chain (classes start)
  (let ((class (aref classes start)))
    (assert (equivalence-class-free-ids class))
    (when (equivalence-class-char-successors class)
      (let* ((id (pop (equivalence-class-free-ids class)))
             (next (1+ id)))
        (destructuring-bind (chars . succ)
            (pop (equivalence-class-char-successors class))
          (assert (= *counter* next))
          (incf *counter*)
          (push (list chars id next)
                (equivalence-class-state-ids class))
          (push next (equivalence-class-free-ids (aref classes succ)))
          (number-chain classes succ))))))

;; assign real state numbers to eqv classes. Each character transition
;; gets its state number, hopefully by reusing another transition's
;; successor state.
(defun number-equivalence-classes (classes accept-class)
  (let ((*counter* 0))
    (tagbody
     retry
       (map nil (lambda (class)
                  (assert (not (and (equivalence-class-free-ids class)
                                    (equivalence-class-char-successors class))))
                  (when (equivalence-class-char-successors class)
                    (push *counter* (equivalence-class-free-ids class))
                    (incf *counter*)
                    (number-chain classes (equivalence-class-number class))
                    (go retry)))
            classes))
    (let ((accept-class (aref classes accept-class)))
      (unless (or (equivalence-class-free-ids accept-class)
                  (equivalence-class-char-successors accept-class))
        (push *counter* (equivalence-class-free-ids accept-class))
        (incf *counter*)))
    (values classes *counter*)))

(defun class-ids (class)
  (union (loop for (nil id nil) in (equivalence-class-state-ids class)
               collect id)
         (equivalence-class-free-ids class)))

(defun class-interesting-ids (class accept-class)
  (let ((ids (loop for (nil id nil) in (equivalence-class-state-ids class)
                   collect id)))
    (when (and (eql class accept-class)
               (not ids))
      (assert (equivalence-class-free-ids class))
      (push (first (equivalence-class-free-ids class)) ids))
    ids))

(defun find-start-states (start-class id-classes)
  (let ((states '())
        (seen (make-hash-table)))
    (labels ((walk (class-id)
               (when (gethash class-id seen)
                 (return-from walk))
               (setf (gethash class-id seen) t)
               (let ((class (gethash class-id id-classes)))
                 (setf states (union (class-ids class) states))
                 (map nil #'walk (equivalence-class-epsilon-successors class)))))
      (walk (equivalence-class-number start-class)))
    states))

(defstruct compressed-nfa
  id-count
  character-transitions
  epsilons-adjacency
  start-ids
  accept-ids)

(defun emit-compressed-nfa (classes counter start-class accept-class)
  (let ((id-classes (make-hash-table))
        (class-ids (make-hash-table))
        (class-interesting-ids (make-hash-table))
        (char-transitions '())
        (epsilon-transitions (make-array counter :initial-element '()))
        (start-class (aref classes start-class))
        (accept-class (aref classes accept-class)))
    (map nil (lambda (class)
               (setf char-transitions (append (equivalence-class-state-ids class)
                                              char-transitions))
               (setf (gethash class class-interesting-ids) (class-interesting-ids class
                                                                                  accept-class))
               (dolist (id (setf (gethash class class-ids) (class-ids class)))
                 (setf (gethash id id-classes) class)))
         classes)
    ;; emit epsilons
    (map nil (lambda (class)
               (dolist (id (gethash class class-ids))
                 (dolist (other (gethash class class-interesting-ids))
                   (pushnew other (aref epsilon-transitions id)))
                 (dolist (succ (equivalence-class-epsilon-successors class))
                   (dolist (succ (gethash (aref classes succ) class-interesting-ids))
                     (pushnew succ (aref epsilon-transitions id))))))
         classes)
    (make-compressed-nfa :id-count counter
                         :character-transitions char-transitions
                         :epsilons-adjacency (map 'list
                                                  (lambda (x)
                                                    (sort x #'<))
                                                  epsilon-transitions)
                         :start-ids (find-start-states start-class id-classes)
                         :accept-ids (class-ids accept-class))))

(defun convert-regexp-to-compressed-nfa (regexp)
  (multiple-value-bind (start accept
                        nodes char-nodes epsilons)
      (dfo (parse-regexp regexp))
    (let ((epsilons (close-epsilon-transitions nodes epsilons)))
      (multiple-value-bind (classes reverse-classes)
          (equivalence-classes nodes char-nodes epsilons)
        (let ((accept-class (aref reverse-classes (node-id accept))))
          (multiple-value-bind (classes class-count)
              (number-equivalence-classes classes accept-class)
            (emit-compressed-nfa classes class-count
                                 (aref reverse-classes (node-id start))
                                 accept-class)))))))

(defun remove-useless-states (nfa)
  (let ((state-count (compressed-nfa-id-count nfa))
        (char-match-states (make-hash-table))
        (epsilons (compressed-nfa-epsilons-adjacency nfa)))
    (loop for (nil from nil) in (compressed-nfa-character-transitions nfa)
          do (setf (gethash from char-match-states) t))
    (labels ((killable (state)
               (and (not (gethash state char-match-states))
                    (equal (list state (1+ state))
                           (elt epsilons state))
                    (prog1 t
                      (assert (or (not (member state (compressed-nfa-start-ids nfa)))
                                  (member (1+ state) (compressed-nfa-start-ids nfa))))
                      (assert (or (not (member state (compressed-nfa-accept-ids nfa)))
                                  (member (1+ state) (compressed-nfa-accept-ids nfa)))))))
             (adjust-id (id victim)
               (cond ((= id victim)
                      '())
                     ((< id victim)
                      (list id))
                     (t
                      (list (1- id)))))
             (kill (victim)
               (assert (not (gethash victim char-match-states)))
               (assert (equal (list victim (1+ victim))
                              (elt epsilons victim)))
               (assert (not (member victim (compressed-nfa-start-ids nfa))))
               (assert (or (not (member victim (compressed-nfa-accept-ids nfa)))
                           (member (1+ victim) (compressed-nfa-accept-ids nfa))))
               (decf (compressed-nfa-id-count nfa))
               (setf (compressed-nfa-character-transitions nfa)
                     (loop for (char from to) in (compressed-nfa-character-transitions nfa)
                           do (assert (/= from victim))
                           collect (list char
                                         (if (> from victim)
                                             (1- from)
                                             from)
                                         (if (> to victim)
                                             (1- to)
                                             to)))
                     (compressed-nfa-epsilons-adjacency nfa)
                     (loop for adjacency in (compressed-nfa-epsilons-adjacency nfa)
                           for i upfrom 0
                           unless (= i victim)
                             collect (loop for j in adjacency
                                           append (adjust-id j victim)))
                     (compressed-nfa-start-ids nfa)
                     (loop for accept in (compressed-nfa-start-ids nfa)
                           append (adjust-id accept victim))
                     (compressed-nfa-accept-ids nfa)
                     (loop for accept in (compressed-nfa-accept-ids nfa)
                           append (adjust-id accept victim)))))
      (dotimes (i state-count nfa)
        (when (killable i)
          (kill i)
          (return (remove-useless-states nfa)))))))

(defun insert-gap-state (nfa gap)
  "Any state id >= gap is incremented by one"
  (incf (compressed-nfa-id-count nfa)
        (if (> (compressed-nfa-id-count nfa) gap) 1 0))
  (labels ((adjust-id (id)
             (+ id (if (>= id gap) 1 0)))
           (adjust-all (ids)
             (mapcar #'adjust-id ids)))
    (setf (compressed-nfa-character-transitions nfa)
          (loop for (char from to) in (compressed-nfa-character-transitions nfa)
                for new-from = (adjust-id from)
                collect (list char
                              new-from
                              (1+ new-from)))
          (compressed-nfa-epsilons-adjacency nfa)
          (loop for adjacency in (compressed-nfa-epsilons-adjacency nfa)
                collect (adjust-all adjacency))
          (compressed-nfa-start-ids nfa)
          (adjust-all (compressed-nfa-start-ids nfa))
          (compressed-nfa-accept-ids nfa)
          (adjust-all (compressed-nfa-accept-ids nfa)))
    nfa))

(defun reachable (source arcs)
  (declare (type hash-table arcs))
  (let ((seen (make-hash-table))
        (succ '()))
    (labels ((walk (node)
               (when (gethash node seen)
                 (return-from walk))
               (setf (gethash node seen) t)
               (push node succ)
               (mapc #'walk (gethash node arcs))))
      (walk source)
      (setf (gethash source arcs) (sort succ #'<)))))

(defun transitive-closure (adjacencies)
  (let ((arcs (make-hash-table)))
    (loop for i upfrom 0
          for adjacency in adjacencies
          do (dolist (j adjacency)
               (push j (gethash i arcs))))
    (loop for i upfrom 0
          for nil in adjacencies
          collect (reachable i arcs))))

;; whenever there is a char transition from break to break+1,
;; insert a clone node to make it from break+1 to break+2.
(defun ensure-state-number-gaps (nfa breaks)
  (labels ((fixup (breaks)
             (when (null breaks)
               (return-from fixup nfa))
             (destructuring-bind (break . breaks) breaks
               (loop for (char from to) in (compressed-nfa-character-transitions nfa)
                     do (when (= from break)
                          (insert-gap-state nfa break)
                          (let ((adjacency (compressed-nfa-epsilons-adjacency nfa)))
                            (push (1+ break) (elt adjacency break))
                            (setf (compressed-nfa-epsilons-adjacency nfa)
                                  (transitive-closure
                                   (append (subseq adjacency 0 (1+ break))
                                           '(()) ; empty adjacency list for padding
                                           (subseq adjacency (1+ break))))))
                          (return)))
               (fixup breaks))))
    (fixup (sort (copy-list breaks) #'<))))

(defun reachable-states (nfa)
  (let ((reachable (make-hash-table))
        (character-transitions (make-hash-table))
        (adjacencies (coerce (compressed-nfa-epsilons-adjacency nfa)
                             'simple-vector)))
    (loop for (nil from to) in (compressed-nfa-character-transitions nfa)
          do (push to (gethash from character-transitions)))
    (labels ((walk (state)
               (when (gethash state reachable)
                 (return-from walk))
               (setf (gethash state reachable) t)
               (mapc #'walk (gethash state character-transitions))
               (mapc #'walk (aref adjacencies state))))
      (mapc #'walk (compressed-nfa-start-ids nfa)))
    reachable))

(defun remove-useless-epsilons (nfa)
  (let ((predecessors (make-hash-table))
        (reachable (reachable-states nfa)))
    (loop for (nil from nil) in (compressed-nfa-character-transitions nfa)
          do (setf (gethash from predecessors) t))
    (setf (compressed-nfa-epsilons-adjacency nfa)
          (loop for i upfrom 0
                for adjacency in (compressed-nfa-epsilons-adjacency nfa)
                collect (adjoin i
                                (and (gethash i reachable)
                                     (remove-if-not (lambda (dst)
                                                      (and (gethash dst reachable)
                                                           (gethash dst predecessors)))
                                                    adjacency))) ))
    nfa))

(defun draw-compressed-nfa (nfa)
  (let ((id-count (compressed-nfa-id-count nfa))
        (starts (compressed-nfa-start-ids nfa))
        (accepts (compressed-nfa-accept-ids nfa)))
    (format t "~
digraph G {
	rankdir=LR;
	bgcolor=transparent;
")
    (dotimes (i id-count)
      (format t "	n~A [label=\"~A\" shape=~A ~A];~%"
              i i
              (if (member i accepts)
                  "doublecircle"
                  "circle")
              (if (member i starts)
                  "style=filled fillcolor=lightgrey"
                  "")))
    (loop for (chars from to) in (compressed-nfa-character-transitions nfa)
          do (format t "	n~A->n~A [label=\"~{&#~A;~}\"];~%"
                     from to (mapcar #'char-code chars)))
    (loop for i upfrom 0
          for epsilons in (compressed-nfa-epsilons-adjacency nfa)
          do (dolist (epsilon epsilons)
               (unless (= i epsilon)
                 (format t "	n~A->n~A~A;~%"
                         i epsilon
                         (if (> i epsilon)
                             "[color=blue constraint=false]"
                             "[color=blue]")))))
    (format t "}~%"))
  nfa)

(defun convert-regexp (regexp &key break-states)
  (remove-useless-epsilons
   (ensure-state-number-gaps
    (remove-useless-states
     (convert-regexp-to-compressed-nfa regexp))
    break-states)))
