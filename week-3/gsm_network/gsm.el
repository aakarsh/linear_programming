(require 'an-lib)
(require 'dash)
(require 'cl)

(defstruct an/gsm
  (num-vertices 0)
  (num-edges 0)
  (relations '()))

(defun an/gsm-parse-file (in-file)
  (let ((p (make-an/gsm)))
    (an/parse-over-file  in-file
     (line,count) =>  (l,i)
     :first
     (let  ((line-1 (an/buffer:line-to-numbers l)))
       (setf (an/gsm-num-vertices p) (aref  line-1  0 ))
       (setf (an/gsm-num-edges p)    (aref  line-1  1 )))
     :rest
     (setf (an/gsm-relations p)
           (cons (an/buffer:line-to-numbers l) (an/gsm-relations p))))
    p))

(an/gsm-parse-file "tests/02" )
