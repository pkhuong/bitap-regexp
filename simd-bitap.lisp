(in-package "CL-USER")
(defun make-byte-pack (bytes)
  (flet ((word (i0)
           (let ((acc 0))
             (dotimes (i 8 acc)
               (setf (ldb (byte 8 (* 8 i)) acc)
                     (elt bytes (+ i i0)))))))
    (sb-ext:%make-simd-pack-ub64 (word 0)
                                 (word 8))))

(defun replicate-bytes (byte &rest bytes)
  (let ((bytes (cons byte bytes)))
    (make-byte-pack (subseq (apply 'alexandria:circular-list bytes)
                            0 16))))

(defun make-ub16-pack (ub16)
  (flet ((word (i0)
           (let ((acc 0))
             (dotimes (i 4 acc)
               (setf (ldb (byte 16 (* 16 i)) acc)
                     (elt ub16 (+ i i0)))))))
    (sb-ext:%make-simd-pack-ub64 (word 0)
                                 (word 4))))

(sb-c:define-source-transform vref (vector index)
  `(%vref-with-offset (the sb-kernel:simple-unboxed-array ,vector)
                      (the (mod ,most-positive-fixnum) ,index)
                      0))

(sb-c:defknown %vref-with-offset ((sb-kernel:simple-unboxed-array 1) fixnum fixnum)
    (sb-ext:simd-pack integer)
    (sb-c:foldable sb-c:flushable sb-c:always-translatable))

(sb-c:deftransform %vref-with-offset ((vector index offset))
  (sb-c::fold-index-addressing '%vref-with-offset 128
                               sb-vm:other-pointer-lowtag sb-vm:vector-data-offset
                               index offset))

(sb-c:defknown (pshufb pmulhuw pmullw por pand pandn pxor pcmpeqq
                       punpcklqdq punpckhqdq)
    ((simd-pack integer) (simd-pack integer)) (simd-pack integer)
    (sb-c:foldable sb-c:flushable sb-c:movable sb-c:always-translatable)
  :overwrite-fndb-silently t)

(sb-c:defknown (psllq psrlq) ((simd-pack integer) (mod 64)) (simd-pack integer)
    (sb-c:foldable sb-c:flushable sb-c:movable sb-c:always-translatable))

(sb-c:defknown pmovmskb ((simd-pack integer)) (unsigned-byte 16)
    (sb-c:foldable sb-c:flushable sb-c:movable sb-c:always-translatable))

(sb-c:defknown byte-sign-logtest ((simd-pack integer) (unsigned-byte 16)) boolean
    (sb-c:foldable sb-c:flushable sb-c:movable sb-c:always-translatable))

(sb-c:defknown ptest ((simd-pack integer) (simd-pack integer)) boolean
    (sb-c:foldable sb-c:flushable sb-c:movable sb-c:always-translatable))

(sb-c:defknown to-simd-pack-integer (simd-pack) (simd-pack integer)
    (sb-c:flushable sb-c:movable sb-c:always-translatable))

(in-package "SB-VM")
(define-vop (cl-user::%vref-with-offset)
  (:translate cl-user::%vref-with-offset)
  (:policy :fast-safe)
  (:args (vector :scs (descriptor-reg)) (index :scs (any-reg)))
  (:arg-types  * tagged-num (:constant fixnum))
  (:info offset)
  (:results (r :scs (int-sse-reg)))
  (:result-types simd-pack-int)
  (:generator 3
    (inst movdqa r (make-ea :qword :base vector
                                   :index index
                                   :scale (ash 16 (- n-fixnum-tag-bits))
                                   :disp (- (+ (* 16 offset)
                                               (* n-word-bytes vector-data-offset))
                                            other-pointer-lowtag)))))

(define-vop (%vref-with-offset/c)
  (:translate cl-user::%vref-with-offset)
  (:policy :fast-safe)
  (:args (vector :scs (descriptor-reg)))
  (:arg-types  * (:constant (eql 0)) (:constant fixnum))
  (:info index offset)
  (:results (r :scs (int-sse-reg)))
  (:result-types simd-pack-int)
  (:generator 2
    (incf offset index)
    (inst movdqa r (make-ea :qword :base vector
                                   :disp (- (+ (* 16 offset)
                                               (* n-word-bytes vector-data-offset))
                                            other-pointer-lowtag)))))

(define-vop (cl-user::pmovmskb)
  (:translate cl-user::pmovmskb)
  (:policy :fast-safe)
  (:args (x :scs (int-sse-reg)))
  (:arg-types simd-pack-int)
  (:results (r :scs (unsigned-reg)))
  (:result-types unsigned-num)
  (:generator 2
    (inst pmovmskb r x)))

(define-vop (cl-user::byte-sign-logtest)
  (:translate cl-user::byte-sign-logtest)
  (:policy :fast-safe)
  (:args (x :scs (int-sse-reg)) (mask :scs (unsigned-reg)))
  (:arg-types simd-pack-int unsigned-num)
  (:temporary (:sc unsigned-reg) bits)
  (:conditional :nz)
  (:generator 3
    (inst pmovmskb bits x)
    (inst test bits mask)))

(define-vop (byte-sign-logtest/c)
  (:translate cl-user::byte-sign-logtest)
  (:policy :fast-safe)
  (:args (x :scs (int-sse-reg)))
  (:arg-types simd-pack-int (:constant (unsigned-byte 16)))
  (:info mask)
  (:temporary (:sc unsigned-reg) bits)
  (:conditional :nz)
  (:generator 2
    (inst pmovmskb bits x)
    (inst test bits (if (= mask (ldb (byte 16 0) -1))
                        bits
                        mask))))

(define-vop (cl-user::ptest)
  (:translate cl-user::ptest)
  (:policy :fast-safe)
  (:args (x :scs (int-sse-reg)) (mask :scs (int-sse-reg)))
  (:arg-types simd-pack-int simd-pack-int)
  (:conditional :nz)
  (:generator 3
    (inst ptest x mask)))

(define-vop (ptest/c cl-user::ptest)
  (:args (x :scs (int-sse-reg)))
  (:arg-types simd-pack-int (:constant simd-pack))
  (:info mask)
  (:generator 2
    (inst ptest x (if (and (= most-positive-word
                              (%simd-pack-high mask))
                           (= most-positive-word
                              (%simd-pack-low mask)))
                      x
                      (register-inline-constant mask)))))

(macrolet ((def (name instruction)
             `(progn
                (define-vop (,name)
                  (:translate ,name)
                  (:policy :fast-safe)
                  (:args (x :scs (int-sse-reg) :target r)
                         (y :scs (int-sse-reg int-sse-stack)
                            :load-if (not (location= x y))))
                  (:arg-types simd-pack-int simd-pack-int)
                  (:results (r :scs (int-sse-reg) :from (:argument 0)))
                  (:result-types simd-pack-int)
                  (:generator 4
                    (aver (not (and (not (location= x y))
                                    (location= y r))))
                    (move r x)
                    (inst ,instruction r (if (location= x y)
                                             r y))))
                (define-vop (,(intern (format nil "~A/C" name)))
                  (:translate ,name)
                  (:policy :fast-safe)
                  (:args (x :scs (int-sse-reg) :target r))
                  (:arg-types simd-pack-int (:constant simd-pack))
                  (:info y)
                  (:results (r :scs (int-sse-reg) :from (:argument 0)))
                  (:result-types simd-pack-int)
                  (:generator 2
                    (move r x)
                    (inst ,instruction r (register-inline-constant y)))))))
  (def cl-user::pshufb pshufb)
  (def cl-user::pmulhuw pmulhuw)
  (def cl-user::pmullw pmullw)
  (def cl-user::por por)
  (def cl-user::pand pand)
  (def cl-user::pandn pandn)
  (def cl-user::pxor pxor)
  (def cl-user::pcmpeqq pcmpeqq)
  (def cl-user::punpcklqdq punpcklqdq)
  (def cl-user::punpckhqdq punpckhqdq))

(define-vop (cl-user::psrlq)
  (:translate cl-user::psrlq)
  (:policy :fast-safe)
  (:args (x :scs (int-sse-reg) :target r))
  (:arg-types simd-pack-int (:constant (mod 64)))
  (:info count)
  (:results (r :scs (int-sse-reg)))
  (:result-types simd-pack-int)
  (:generator 3
    (move r x)
    (inst psrlq-imm r count)))

(define-vop (cl-user::psllq cl-user::psrlq)
  (:translate cl-user::psllq)
  (:generator 3
    (move r x)
    (inst psllq-imm r count)))

(define-vop (cl-user::to-simd-pack-integer)
  (:translate cl-user::to-simd-pack-integer)
  (:policy :fast-safe)
  (:args (x :scs (int-sse-reg single-sse-reg double-sse-reg) :target r))
  (:arg-types simd-pack)
  (:results (r :scs (int-sse-reg)))
  (:result-types simd-pack-int)
  (:generator 3
    (move r x)))
(in-package "CL-USER")

(defun vref (vector index)
  (vref vector index))

(defun %vref-with-offset (vector index offset)
  (vref vector (+ index offset)))

(macrolet ((def (name)
             `(defun ,name (x y)
                (,name x y))))
  (def pshufb)
  (def pmulhuw)
  (def pmullw)
  (def por)
  (def pand)
  (def pandn)
  (def pxor)
  (def pcmpeqq)
  (def ptest)
  (def punpcklqdq)
  (def punpckhqdq))

(macrolet ((def (name)
             `(defun ,name (x count)
                (ecase count
                  ,@(loop for i below 64 collect
                          `(,i (,name x ,i)))))))
  (def psllq)
  (def psrlq))

(defun byte-sign-logtest (x mask)
  (byte-sign-logtest x mask))

;; capture group: after complete transition, ANDN with
;;  previous, AND with states that begin capture groups.
;;  if not all zero, record index for all delta states.
(defun transition (states mask loops sources)
  (declare (type (simd-pack integer) states mask loops sources))
  (por (por (pand states loops)
            sources)
       (pand (psllq states 1) mask)))

(defun bit-shift-index (source shift)
  (declare (type (mod 128) source)
           (type (integer -63 63) shift))
  (let ((destination (+ source shift)))
    (and (>= destination 0)
         (< destination 128)
         ;; same quadword
         (or (zerop shift)
             (= (truncate source 64) (truncate destination 64)))
         destination)))

(defun transition-covered-p (transition shift destination-byte)
  (destructuring-bind (source . target) transition
    (let ((blitted (+ (* 8 destination-byte) (mod source 8))))
      (and (eql target (bit-shift-index blitted shift))
           blitted))))

;; ->  number of transitions achieved
;;   + in-mask for that byte
(defun eval-byte-transition (transitions shift destination source)
  (declare (type (mod 16) destination source)
           (type (integer -8 8) shift))
  (let ((hits 0)
        (bits '()))
    (loop for transition in transitions
          for (src . dst) = transition
          for blitted = (transition-covered-p transition shift destination)
          when (and (= (truncate src 8) source)
                    blitted)
            do (incf hits)
               (pushnew blitted bits)
          finally (return (values hits bits)))))

;; transitions: vector of (source . destination) pairs
;; for destination byte and shift, find source byte
;; that takes care of the most transitions
(defun find-best-byte-transition-1 (transitions shift destination)
  (let ((hits 0)
        (source nil)
        (bits '()))
    (dotimes (i 16 (values hits source bits))
      (let ((i (mod (+ i destination) 16)))
        (multiple-value-bind (try-hits try-bits)
            (eval-byte-transition transitions shift destination i)
          (when (> try-hits hits)
            (setf hits try-hits
                  source i
                  bits try-bits)))))))

(defun find-best-byte-transition (transitions shift)
  (let ((hits 0)
        (sources nil)
        (bits '()))
    (dotimes (i 16 (values hits (nreverse sources) (sort (copy-list bits) #'<)))
      (multiple-value-bind (sub-hits sub-source sub-bits)
          (find-best-byte-transition-1 transitions shift i)
        (incf hits sub-hits)
        (push sub-source sources)
        (setf bits (union sub-bits bits))))))

(defvar *shift-values* (stable-sort (loop for i from -8 upto 8 collect i)
                                    #'< :key #'abs))

(defun find-best-transition (transitions)
  (let ((hits 0)
        (shift 0)
        (sources nil)
        (bits nil))
    (dolist (try-shift *shift-values*)
      (multiple-value-bind (try-hits try-sources try-bits)
          (find-best-byte-transition transitions try-shift)
        (when (> try-hits hits)
          (setf hits try-hits
                shift try-shift
                sources (coerce try-sources 'simple-vector)
                bits try-bits))))
    (let* ((covered '())
           (transitions (if (zerop hits)
                            transitions
                            (remove-if (lambda (transition)
                                         (let ((src-byte (truncate (car transition) 8)))
                                           (dotimes (dst-byte 16)
                                             (when (and (eql src-byte (aref sources dst-byte))
                                                        (transition-covered-p transition shift dst-byte))
                                               (push transition covered)
                                               (return t)))))
                                       transitions))))
      (values hits shift sources bits
              (nreverse covered) transitions))))

(defun transpose (transitions)
  (let ((destinations (make-array 128 :initial-element '())))
    (loop for (src . dst) in transitions
          do (pushnew dst (aref destinations src))
          finally (return destinations))))

(defun clean-transitions (transitions covered already-covered)
  (let ((destinations (transpose transitions))
        (covered (transpose covered))
        (already (transpose already-covered))
        (acc '()))
    (dotimes (src 128 acc)
      (let ((dest (aref destinations src)))
        (map nil (lambda (covered)
                   (setf dest (remove covered dest)
                         dest (set-difference dest (aref already covered))))
             (aref covered src))
        (setf acc (append (mapcar (lambda (dest)
                                    (cons src dest))
                                  dest)
                          acc))))))

(defun compute-transitions (transitions)
  (declare (optimize debug))
  (setf transitions (remove-if (lambda (x)
                                 (eql (car x) (cdr x)))
                               transitions))
  (let ((sequence '())
        (original transitions)
        (already-covered '()))
    (loop while transitions
          do (multiple-value-bind (hits shift sources bits covered remaining)
                 (find-best-transition transitions)
               (assert (plusp hits))
               (assert (= hits (length covered)))
               (push (list shift sources bits) sequence)
               (setf transitions (clean-transitions remaining covered already-covered))
               #+nil(let ((*print-pretty* nil))
                 (format t "~A ~A~% ~A -> ~A~%" remaining covered already-covered transitions))
               (setf already-covered (set-difference original transitions :test #'equal))))
    sequence))

(defun reoptimize-shuffle-mask (sources mask shift &aux (sources (copy-seq sources)))
  ;; simplify mask: try to get as many 1 bits as possible.
  (cond ((zerop shift)
         ;; no need to mask out identity shuffles
         (dotimes (i 16)
           (when (eql (elt sources i) i)
             (setf (ldb (byte 8 (* 8 i)) mask) -1))))
        ((minusp shift)
         ;; shift right. No need to mask out leftmost bits
         (let ((count (- shift)))
           (setf (ldb (byte count 64) mask) -1
                 (ldb (byte count 0) mask) -1)))
        ((plusp shift)
         ;; shift left. No need to mask out rightmost bits
         (setf (ldb (byte shift (- 128 shift)) mask) -1
               (ldb (byte shift (- 64 shift)) mask) -1)))
  (block nil
    ;; priority: avoid shuffle
    (when (loop for i below 16
                for source = (elt sources i)
                always (or (null source) (eql source i)))
      (loop for i below 16
            when (null (elt sources i))
              do (setf (elt sources i) i
                       (ldb (byte 8 (* 8 i)) mask) 0))
      (return (values sources mask)))
    ;; otherwise: avoid mask
    (dotimes (i 16 (values sources mask))
      (when (zerop (ldb (byte 8 (* 8 i)) mask))
        (setf (elt sources i) nil))
      (when (null (elt sources i))
        (setf (ldb (byte 8 (* 8 i)) mask) -1)))))

(defun identity-shuffle (sources)
  (assert (= (length sources) 16))
  (loop for i below 16
        for source = (elt sources i)
        always (eql i source)))

(defun identity-mask (sources mask)
  (loop for i below 16
        for source = (elt sources i)
        always (or (null source)
                   (= (ldb (byte 8 (* 8 i)) mask)
                      (ldb (byte 8 0) -1)))))

(defun emit-shift-form (input sources bits shift)
  (multiple-value-bind (sources mask)
      (reoptimize-shuffle-mask sources
                               (let ((mask 0))
                                 (dolist (bit bits mask)
                                   (setf (logbitp bit mask) 1)))
                               shift)
    (let* ((shuffled (if (identity-shuffle sources)
                         input
                         `(pshufb ,input ,(make-byte-pack (map 'vector
                                                               (lambda (x)
                                                                 (or x 255))
                                                               sources)))))
           (masked (if (identity-mask sources mask)
                       shuffled
                       `(pand ,shuffled ,(%make-simd-pack-ub128 mask)))))
      (cond ((zerop shift)
             masked)
            ((minusp shift)
             `(psrlq ,masked ,(- shift)))
            (t
             `(psllq ,masked ,shift))))))

(defun emit-transition-code (sequence input)
  (let ((var (gensym "STATES"))
        (bindings ()))
    (loop for (shift sources bits) in sequence do
      (push `(,var (por ,var ,(emit-shift-form var sources bits shift)))
            bindings))
    `(let* ((,var (the (simd-pack integer) ,input))
            ,@(nreverse bindings))
       ,var)))

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

(defun random-transitions (n)
  (transitive-closure
   (let ((keys (make-hash-table :test 'equal)))
     (loop repeat (* n n)
           while (< (hash-table-count keys) n)
           do (setf (gethash (cons (random 128) (random 128)) keys) t))
     (alexandria:hash-table-keys keys))))

(defun %make-simd-pack-ub128 (x)
  (%make-simd-pack-ub64 (ldb (byte 64 0) x)
                        (ldb (byte 64 64) x)))

(defun %simd-pack-ub128 (x)
  (multiple-value-bind (lo hi)
      (%simd-pack-ub64s x)
    (logior lo (ash hi 64))))

(defun test (transitions)
  (declare (optimize debug))
  (let* ((sequence (compute-transitions transitions))
         (code (compile nil `(lambda (x)
                               (declare (type (simd-pack integer) x))
                               ,(emit-transition-code sequence 'x))))
         (spec (transpose transitions)))
    (dotimes (i 128)
      (let ((result (%simd-pack-ub128
                     (funcall code (%make-simd-pack-ub128 (ash 1 i)))))
            (expected (adjoin i (aref spec i))))
        (assert (= (logcount result) (length expected)))
        (map nil (lambda (j)
                   (assert (logbitp j result)))
             expected)))))

(defvar *state* (sb-ext:seed-random-state 12345))

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
