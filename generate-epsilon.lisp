(defun %make-simd-pack-ub128 (x)
  (%make-simd-pack-ub64 (ldb (byte 64 0) x)
                        (ldb (byte 64 64) x)))

(defun %simd-pack-ub128 (x)
  (multiple-value-bind (low high)
      (%simd-pack-ub64s x)
    (logior low (ash high 64))))

(defconstant +state-size+ 128)
(defconstant +chunk-size+ 64)

(deftype index ()
  `(and unsigned-byte fixnum))

(defstruct (row
            (:constructor %make-row (index row indices)))
  (index  0   :type index :read-only t)
  (number nil :type (or null index))
  (row    nil :type (unsigned-byte #.+state-size+) :read-only t)
  (indices nil :type (simple-array index 1) :read-only t))

(defun make-row (index &key row indices)
  (declare (type (or null (unsigned-byte #.+state-size+)) row)
           (type (or null (simple-array index 1)) indices))
  (assert (or row indices))
  (cond ((and row indices)
         (setf (logbitp index row) 1)
         (dotimes (i +state-size+)
           (when (logbitp i row)
             (assert (find i indices))))
         (map nil (lambda (i)
                    (assert (logbitp i row)))
              indices))
        (row
         (setf (logbitp index row) 1)
         (let ((acc '()))
           (dotimes (i +state-size+)
             (when (logbitp i row)
               (push i acc)))
           (setf indices (coerce (nreverse acc)
                                 '(simple-array index 1)))))
        (indices
         (setf row 0)
         (map nil (lambda (i)
                    (setf (logbitp i row) 1))
              indices)))
  (assert (logbitp index row))
  (assert indices)
  (%make-row index row (sort (copy-seq indices) #'<)))

(defun make-rows (adjacency)
  (let ((rows (make-array +state-size+ :initial-element 0)))
    (loop for (i . j) in adjacency
          do (setf (logbitp j (aref rows i)) 1))
    (let ((i 0))
      (map 'simple-vector (lambda (row)
                            (prog1 (make-row i :row row)
                              (incf i)))
           rows))))

(defun order-rows (rows)
  (declare (type simple-vector rows))
  (assert (= +state-size+ (length rows)))
  (setf rows (sort (copy-seq rows)
                   #'>
                   :key (lambda (row)
                          (+ (* +state-size+ (length (row-indices row)))
                             (row-index row)))))
  (dotimes (i (length rows) rows)
    (setf (row-number (aref rows i)) i)))

(defstruct (op
            (:constructor nil))
  (src 0 :type (or index list) :read-only t)
  (anti-deps #() :type vector :read-only t))

(defstruct (simple-op
            (:include op)
            (:constructor make-simple-op (src dst &aux (anti-deps (vector dst)))))
  (dst 0 :type index :read-only t))

(defstruct (row-op
            (:include op)
            (:constructor make-row-op (src row)))
  (row nil :type (unsigned-byte #.+state-size+) :read-only t))

(defstruct (multi-row-op
            (:include op)
            (:constructor make-multi-row-op (src row)))
  (row nil :type (unsigned-byte #.+state-size+) :read-only t))

(defun find-simple-op (row rows)
  (let* ((i (row-index row))
         (number (row-number row))
         (op (logandc2 (row-row row) (ash 1 i)))
         (value -1)
         (dst nil))
    (map nil (lambda (j)
               (let ((other (aref rows j))
                     (op (logandc2 op (ash 1 j))))
                 (when (and (/= i j)
                            (> (row-number other) number)
                            (= op (logand op (row-row other)))
                            (> (row-number other) value))
                   (setf value (row-number other)
                         dst j))))
         (row-indices row))
    (when dst
      (make-simple-op i dst))))

(defun find-row-op (row)
  (let ((i (row-index row)))
    (when (notevery (lambda (j)
                      (eql j i))
                    (row-indices row))
      (make-row-op i (row-row row)))))

(defun find-multirow-ops (ops)
  (let ((row-ops (make-hash-table)))
    (map nil (lambda (op)
               (when (row-op-p op)
                 (setf (gethash (row-op-src op) row-ops)
                       (list op))))
         ops)
    (let ((acc '()))
      (map nil (lambda (op)
                 (etypecase op
                   (simple-op
                    (let* ((dst (simple-op-dst op))
                           (entry (gethash dst row-ops)))
                      (if entry
                          (push (simple-op-src op) (cdr entry))
                          (push op acc))))
                   (row-op
                    (let ((entry (shiftf (gethash (row-op-src op) row-ops) nil)))
                      (assert entry)
                      (destructuring-bind (op . others)
                          entry
                        (let ((src (row-op-src op)))
                          (cond ((not others)
                                 (push op acc))
                                (t
                                 (push (make-multi-row-op (cons src others)
                                                          (logior (row-op-row op)
                                                                  (ash 1 src)))
                                       acc)))))))))
           ops)
      (coerce (nreverse acc) 'simple-vector))))

(defun merge-row-ops (ops)
  (flet ((row-op-mask (op)
           (logandc2 (row-op-row op)
                     (ash 1 (row-op-src op)))))
    (let ((row-ops (make-hash-table))
          acc)
      (map nil (lambda (op)
                 (when (row-op-p op)
                   (push op (gethash (row-op-mask op) row-ops))))
           ops)
      (map nil (lambda (op)
                 (if (row-op-p op)
                     (let* ((mask (row-op-mask op))
                            (ops (shiftf (gethash mask row-ops) nil)))
                       (cond ((null ops))
                             ((cdr ops)
                              (push (make-multi-row-op (mapcar #'row-op-src ops)
                                                       mask)
                                    acc))
                             (t (push op acc))))
                     (push op acc)))
           ops)
      (coerce (nreverse acc) 'simple-vector))))

(defun find-ops (ordered-rows rows)
  (merge-row-ops
   (find-multirow-ops
    (delete nil (map 'simple-vector
                     (lambda (src)
                       (or (find-simple-op src rows)
                           (find-row-op src)))
                     ordered-rows)))))

;; try to find up to 4-wide parallelism
(defvar *bundle-size* 4)

(defun find-shifts (ready)
  ;; which chunk . mod-chunk shift
  (let ((shifts (make-hash-table :test 'equal)))
    (map nil (lambda (ready)
               (when (simple-op-p ready)
                 (let ((chunk (truncate (op-src ready) +chunk-size+))
                       (shift (- (mod (simple-op-dst ready) +chunk-size+)
                                 (mod (op-src ready) +chunk-size+))))
                   (push ready (gethash (cons chunk shift) shifts)))))
         ready)
    (sort (alexandria:hash-table-alist shifts)
          #'> :key #'length)))

(defun find-rows (ready)
  (nreverse (remove-if-not (lambda (x)
                             (typep x '(or row-op multi-row-op)))
                           ready)))

(defgeneric generate (op))

(defmethod generate ((shift list))
  (destructuring-bind ((chunk . shift) . ops)
      shift
    (let ((mask (let ((low 0)
                      (high 0))
                  (mapc (lambda (op)
                          (let ((src (op-src op))
                                (dst-chunk (truncate (simple-op-dst op)
                                                     +chunk-size+)))
                            (assert (= (truncate src +chunk-size+) chunk))
                            (ecase dst-chunk
                              (0
                               (setf (logbitp (mod src +chunk-size+) low) 1))
                              (1
                               (setf (logbitp (mod src +chunk-size+) high) 1)))))
                        ops)
                  (if (= (ash low shift)
                         (ash high shift)
                         (ash (ldb (byte +chunk-size+ 0) -1) shift))
                      nil
                      (%make-simd-pack-ub64 low high))))
          (source (if (every (lambda (op)
                               (= (truncate (simple-op-src op) +chunk-size+)
                                  (truncate (simple-op-dst op) +chunk-size+)))
                             ops)
                      'source
                      (ecase chunk
                        (0 'low-source)
                        (1 'high-source)))))
      `(lambda (source low-source high-source ones zero)
         (declare (ignore ones zero)
                  (ignorable source low-source high-source))
         ',(acons chunk shift ops)
         (let ((select ,(if mask
                            `(pand ,source ,mask)
                            source)))
           ,(cond ((zerop shift)
                   'select)
                  ((minusp shift)
                   `(psrlq select ,(- shift)))
                  (t
                   `(psllq select ,shift))))))))

(defmethod generate ((op row-op))
  (let* ((src (row-op-src op))
         (row (row-op-row op))
         (ones `(psllq ones ,(mod src +chunk-size+))))
    (if (or (and (< src 64)  (typep row '(unsigned-byte 64)))
            (and (>= src 64) (zerop (ldb (byte 64 0) row))))
        `(lambda (source low-source high-source ones zero)
           (declare (ignore low-source high-source zero))
           ',op
           (let* ((ones ,ones)
                  (select (pand source ones))
                  (mask (pcmpeqq select ones)))
             (pand mask ,(%make-simd-pack-ub128 row))))
        `(lambda (source low-source high-source ones zero)
           (declare (ignorable low-source high-source)
                    (ignore source zero))
           ',op
           ,(let ((source (ecase (truncate src +chunk-size+)
                            (0 'low-source)
                            (1 'high-source))))
              `(let* ((ones ,ones)
                      (select (pand ,source ones))
                      (mask   (pcmpeqq select ones)))
                 (pand mask ,(%make-simd-pack-ub128 row))))))))

(defmethod generate ((op multi-row-op))
  (let* ((src (multi-row-op-src op))
         (row (multi-row-op-row op))
         (low-mask 0)
         (high-mask 0))
    (dolist (src src)
      (multiple-value-bind (chunk offset)
          (truncate src +chunk-size+)
        (ecase chunk
          (0 (setf (logbitp offset low-mask) 1))
          (1 (setf (logbitp offset high-mask) 1)))))
    (if (or (and (zerop high-mask) (typep row '(unsigned-byte 64)))
            (and (zerop low-mask) (zerop (ldb (byte 64 0) row))))
        `(lambda (source low-source high-source ones zero)
           (declare (ignore low-source high-source ones))
           ',op
           (let* ((select (pand source ,(%make-simd-pack-ub64 low-mask high-mask)))
                  (maskn (pcmpeqq select zero)))
             (pandn maskn ,(%make-simd-pack-ub128 row))))
        `(lambda (source low-source high-source ones zero)
           (declare (ignorable low-source high-source)
                    (ignore source ones))
           ',op
           ,(let ((low-select (and (plusp low-mask)
                                   (if (= low-mask (ldb (byte 64 0) -1))
                                       'low-source
                                       `(pand low-source ,(%make-simd-pack-ub64 low-mask
                                                                                low-mask)))))
                  (high-select (and (plusp high-mask)
                                    (if (= high-mask (ldb (byte 64 0) -1))
                                        'high-source
                                        `(pand high-source ,(%make-simd-pack-ub64 high-mask
                                                                                  high-mask))))))
              `(let* ((select ,(cond ((and low-select high-select)
                                      `(por ,low-select
                                            ,high-select))
                                     (low-select)
                                     (high-select)
                                     (t (error "No source?"))))
                      (maskn (pcmpeqq select zero)))
                 (pandn maskn ,(%make-simd-pack-ub128 row))))))))

(defun retire-ops (ready)
  (let ((shifts (find-shifts ready))
        (rows   (find-rows ready))
        (chosen '())
        (instructions '()))
    (loop for i below *bundle-size*
          while (or shifts rows)
          do (multiple-value-bind (choice instruction)
                 ;; start with rows: they can never be coalesced
                 ;; and either uses exactly one memory op
                 (if rows
                     (let ((row (pop rows)))
                       (values row (generate row)))
                     (let ((shift (pop shifts)))
                       (values (cdr shift)
                               (generate shift))))
               (if (listp choice)
                   (setf chosen (append choice chosen))
                   (push choice chosen))
               (push instruction instructions)))
    (values chosen (nreverse instructions))))

(defun schedule-ops (ops)
  (let ((schedule (map-into (make-array +state-size+)
                            (lambda ()
                              (cons 0 nil)))))
    (map nil (lambda (op)
               (let ((src (op-src op)))
                 (when (listp src) ; choose a representative
                   (setf src (first src))) ; arbitrarily
                 (setf (cdr (aref schedule src)) op)
                 (map nil (lambda (anti-dep)
                            (incf (car (aref schedule anti-dep))))
                      (op-anti-deps op))))
         ops)
    (let ((ready '())
          (retired '()))
      (labels ((find-ready ()
                 (loop for cons across schedule
                       for (countdown . op) = cons
                       when (and op (zerop countdown)
                                 (typecase (op-src op)
                                   (index t)
                                   (cons
                                    (every (lambda (src)
                                             (zerop (car (aref schedule src))))
                                           (op-src op)))))
                         do (push op ready)
                            (setf (cdr cons) nil)))
               (maybe-exit ()
                 (when (null ready)
                   (assert (every (lambda (x)
                                    (null (cdr x)))
                                  schedule))
                   (return-from schedule-ops (nreverse retired)))))
        (loop
         (find-ready)
         (maybe-exit)
         (multiple-value-bind (done instruction)
             (retire-ops ready)
           (mapc (lambda (done)
                   (map nil (lambda (anti-dep)
                              (decf (car (aref schedule anti-dep))))
                        (op-anti-deps done)))
                 done)
           (setf ready (set-difference ready done))
           (push instruction retired)))))))

(defun emit-instructions-1 (scheduled-instructions input)
  (let ((source (gensym "SOURCE"))
        (low (gensym "LOW"))
        (high (gensym "HIGH"))
        (ones (gensym "ONES"))
        (zero (gensym "ZERO")))
    (labels ((emit-por-tree (temps)
               (assert temps)
               (if (null (cdr temps))
                   (car temps)
                   (let* ((half (ceiling (length temps) 2)))
                     `(por ,(emit-por-tree (subseq temps 0 half))
                           ,(emit-por-tree (subseq temps half))))))
             (emit-one-step (step)
               (let (temps)
                 `(let* ((,low (punpcklqdq ,source ,source))
                         (,high (punpckhqdq ,source ,source))
                         ,@(loop for op in step
                                 for temp = (gensym "ROW")
                                 do (push temp temps)
                                 collect `(,temp (,op ,source ,low ,high ,ones ,zero))))
                    ,(emit-por-tree (cons source (nreverse temps)))))))
      (if scheduled-instructions
          (values `(let ((,source ,input))
                     (declare (type (simd-pack integer) ,source))
                     (let* ,(loop for bundle in scheduled-instructions
                                  collect `(,source ,(emit-one-step bundle)))
                       ,source))
                   ;; avoid constant propagation
                  `(let ((,ones (to-simd-pack-integer
                                 (%make-simd-pack-ub64 1 1)))
                         (,zero (to-simd-pack-integer
                                 (%make-simd-pack-ub64 0 0))))
                     (declare (type (simd-pack integer) ,ones ,zero))))
          (values `(the (simd-pack integer) ,input) nil)))))

(defun emit-instructions (scheduled-instructions input)
  (multiple-value-bind (body around)
      (emit-instructions-1 scheduled-instructions input)
    (if around
        (append around (list body))
        body)))

(defun compile-adjacency (adjacency input &key raw)
  (let* ((rows (make-rows adjacency))
         (order (order-rows rows))
         (ops (find-ops order rows))
         (schedule (schedule-ops ops)))
    (funcall (if raw #'emit-instructions-1 #'emit-instructions)
             schedule input)))

(defun transitive-closure (arcs)
  (declare (optimize debug))
  (let ((transpose (map 'simple-vector
                        (lambda (dst)
                          (let ((hash (make-hash-table)))
                            (map nil (lambda (dst)
                                       (setf (gethash dst hash) t))
                                 dst)
                            hash))
                        (transpose arcs)))
        delta)
    (loop
     (setf delta nil)
     (dotimes (i 128)
       (let ((acc (aref transpose i)))
         (flet ((try (dst)
                  (unless (gethash dst acc)
                    (setf delta t)
                    (setf (gethash dst acc) t))))
           (try i)
           (maphash (lambda (j _) _
                      (maphash (lambda (k v) v
                                 (try k))
                               (aref transpose j)))
                    acc))))
     (unless delta
       (return)))
    (loop for i upfrom 0
          for spec across transpose
          do (remhash i spec)
          append (map 'list (lambda (j)
                              (cons i j))
                      (sort (alexandria:hash-table-keys spec) #'<)))))

(defvar *max* 128)

(defun random-transitions (n &aux (max *max*))
  (transitive-closure
   (let ((keys (make-hash-table :test 'equal)))
     (loop repeat (* n n)
           while (< (hash-table-count keys) n)
           do (setf (gethash (cons (random max) (random max)) keys) t))
     (alexandria:hash-table-keys keys))))

(defun transpose (transitions)
  (let ((destinations (make-array 128 :initial-element '())))
    (loop for (src . dst) in transitions
          do (pushnew dst (aref destinations src))
          finally (return destinations))))

(defun test (transitions)
  (declare (optimize debug))
  (let* ((code (compile nil `(lambda (x)
                               (declare (type (simd-pack integer) x))
                               ,(compile-adjacency transitions 'x))))
         (spec (transpose transitions)))
    (dotimes (i 128)
      (let ((result (%simd-pack-ub128
                     (funcall code (%make-simd-pack-ub128 (ash 1 i)))))
            (expected (adjoin i (aref spec i))))
        (assert (= (logcount result) (length expected)))
        (map nil (lambda (j)
                   (assert (logbitp j result)))
             expected)))))

(defvar *state* (sb-ext:seed-random-state 1234578))

(defun n-tests (min max repetitions)
  (declare (optimize debug))
  (loop for count from min upto max do
        (format t "count: ~A -" count)
        (finish-output)
        (let ((*random-state* (make-random-state *state*)))
          (loop repeat repetitions
                for random = (random-transitions count)
                do (format t " ~A" (length random))
                   (finish-output)
                   (test random)))
        (format t "~%")
        (finish-output)))
