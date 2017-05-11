(require 'cl)
(require 'gaussian)

(defvar s/debug 1)

(defvar s/A nil "Coefficient matrix for Ax \leq b")
(defvar s/b nil "Bounds on the inequalities ")
(defvar s/objective nil "Objective function to maximize")
(defvar m 0 "Number of variables in Ax \leq b")
(defvar n 0 "Number of inequalities in Ax \leq b" )


(defun s/pivot(entering leaving)
  " Pivot a slack form matrix for simplex based optimization
  `entering` - index of element becoming basic
  `leaving`  - index of element leaving the basic element"
  ;; 1. Scale the leaving row of the slack form matrix by the leaving
  ;;    entry form
  (loop
   with pivot-entry = (g/table-at s/A leaving entering)
   with b-entering  = (/ (aref s/b leaving) pivot-entry)
   for row from 0 below (g/table-ncols s/A) do   
   (if s/debug
       (message "pivot-entry:%d b-entering:%d" pivot-entry b-entering))
   ))

(defun s/read-input(input-file)
  "Read in simplex from file."
  (with-temp-buffer
    (insert-file-contents input-file t)
    (goto-char 0)
    (let*((sizes (g/fetch-line-as-numbers))
          (m (aref sizes 0))
          (n (aref sizes 1)))
      (setf s/A (make-vector m nil))
      (loop for i from 0 below m do
            (aset s/A i (g/fetch-line-as-numbers)))
      (setf s/b (g/fetch-line-as-numbers))
      (setf s/objective (g/fetch-line-as-numbers)))))

(defvar s/test-dir "/home/aakarsh/src/c++/coursera/linear_programming/week-2/diet")
(ert-deftest s/test-02()
  (should (s/read-input (concat s/test-dir "/tests/02")))
