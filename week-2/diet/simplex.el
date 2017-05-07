(require 'cl)
(require 'gaussian)
(defvar s/A nil "Coefficient matrix for Ax \leq b")
(defvar s/b nil "Bounds on the inequalities ")
(defvar s/objective nil "Objective function to maximize")
(defvar m 0 "Number of variables in Ax \leq b")
(defvar n 0 "Number of inequalities in Ax \leq b" )

(defun s/read-input(input-file)
  "Read in simplex from file."
  (with-temp-buffer
    (insert-file-contents input-file t)
    (goto-char 0)
    (let*((sizes (g/fetch-num-vector))
          (m (aref sizes 0))
          (n (aref sizes 1)))
      (setf s/A (make-vector m nil))
      (loop for i from 0 below m do
            (aset s/A i (g/fetch-num-vector)))
      (setf s/b (g/fetch-num-vector))
      (setf s/objective (g/fetch-num-vector)))))

(s/read-input "tests/02")
