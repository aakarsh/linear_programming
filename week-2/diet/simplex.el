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
    (let*((line1 (split-string (g/fetch-line) " " t))
          (m (string-to-number (car line1)))
          (n (string-to-number (cadr line1))))
      (setf s/A (g/make-matrix-2d m n 0))
      (setf s/b (make-vector m 0))
      (setf s/objective (make-vector n 0))
      (loop for line in (g/fetch-lines m)
            for i = 0 then (+ i 1) do
            (loop for cell in (split-string line " ")
                  for cell-value = (string-to-number cell)
                  for j = 0 then (+ j 1) do
                  (g/matrix-setf s/A i j cell-value)))
      (loop for cell in (split-string (g/fetch-line) " ")
            for cell-value = (string-to-number cell)
            for i = 0 then (+ i 1) do
            (aset s/b i cell-value))
      (loop for cell in (split-string (g/fetch-line) " ")
            for cell-value = (string-to-number cell)
            for i = 0 then (+ i 1) do
            (aset s/objective i cell-value))
      )))

(s/read-input "tests/01")
