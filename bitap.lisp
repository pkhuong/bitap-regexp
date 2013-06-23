(defun bitap-search (pattern sequence &key (test 'eql))
  (declare (type simple-vector pattern sequence))
  (assert (<= (length pattern) (integer-length most-positive-fixnum)))
  (let ((characters (make-hash-table :test test)))
    (dotimes (i (length pattern))
      (check-type i (mod #. (integer-length most-positive-fixnum)))
      (dolist (character (alexandria:ensure-list (elt pattern i)))
        (let ((mask (gethash character characters most-positive-fixnum)))
          (declare (type fixnum mask))
          (setf (gethash character characters)
                (logandc2 mask (ash 1 i))))))
    (let ((length-1 (1- (length pattern)))
          (acc most-positive-fixnum)
          (i 0))
      (declare (type fixnum acc)
               (type (mod #.most-positive-fixnum) i)
               (type (mod #. (integer-length most-positive-fixnum)) length-1)
               (optimize speed))
      (map nil (lambda (c)
                 (let ((mask (gethash c characters most-positive-fixnum)))
                   (declare (type fixnum mask))
                   (setf acc (logior acc mask))
                   (unless (logbitp length-1 acc)
                     (return-from bitap-search (- i length-1)))
                   (setf acc (logand most-positive-fixnum (ash acc 1)))
                   (incf i)))
           sequence))))

(defun slow-search (pattern sequence)
  (declare (type simple-vector pattern sequence)
           (optimize speed (safety 0)))
  (search pattern sequence))

#||
CL-USER> (defparameter *pattern* (make-array 60 :initial-element t))
*PATTERN*
CL-USER> (defparameter *haystack*
           (coerce (loop for pattern
                           = (cons nil (make-list 59 :initial-element t))
                         repeat 100
                         append pattern)
                   'simple-vector))
*HAYSTACK*
CL-USER> (time (slow-search *pattern* *haystack*))
Evaluation took:
  0.004 seconds of real time
  0.004145 seconds of total run time (0.004125 user, 0.000020 system)
  100.00% CPU
  6,572,896 processor cycles
  0 bytes consed
  
NIL
CL-USER> (time (bitap-search *pattern* *haystack*))
Evaluation took:
  0.000 seconds of real time
  0.000290 seconds of total run time (0.000289 user, 0.000001 system)
  100.00% CPU
  459,392 processor cycles
  0 bytes consed
  
NIL
||#
