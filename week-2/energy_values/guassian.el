(defvar g/debug 1)

;; Admitedly this is way too imperative
;; Solving equations of the form Ax=b
(defvar g/A nil)
(defvar g/b nil)
(defstruct g/position row column)

(defun g/current-line()
  (buffer-substring-no-properties
   (line-beginning-position) (line-end-position)))

(defun g/last-linep()
  (equal (line-beginning-position)
         (let ((position-eol 0))
           (save-excursion
             (goto-char (point-max))
             (setf position-eol (line-beginning-position)))
           position-eol)))

(defun g/make-matrix-2d(r c init)
  (let ((retval (make-vector r nil)))
    (loop for i from 0 below r do
        (setf (aref retval i) (make-vector c init)))
    retval))

(defun g/read-equation(input-file)
  "Read the equation from input file into g/A and g/b"
  (with-temp-buffer
    (insert-file-contents input-file t)
    (goto-char 0)
    (let ((size (string-to-number (g/current-line)))
          (i 0))
      ;; Create the matrix
      (setf g/A (g/make-matrix-2d size size 0))
      (setf g/b (make-vector size 0))

      (forward-line 1)
      (while (not (g/last-linep))
        (let ((j 0))
          (dolist (cur (split-string (g/current-line)))
            (if (< j size)
                (setf (aref (aref g/A i) j) (string-to-number cur))
              (setf (aref g/b i) (string-to-number cur)))
            (incf j)))
          (incf i)
          (forward-line 1)))))

(defun g/select-pivot(used_rows used_columns)
  (let ((retval (make-g/position :row 0 :column 0)))
    (loop for i from 0 below (length used_rows)
          while (aref used_rows i) do
          (incf (g/position-row retval)))
    (loop for i from 0 below (length used_columns)
          while (aref used_columns i) do
          (incf (g/position-column retval)))
    (if (not (aref (aref g/A (g/position-row retval)) (g/position-column retval)))
        ;; Need to swap rows.
        (message "Need swapping..."))
    retval))

(defun g/gausian(input-file)
  (g/read-equation input-file))

(g/read-equation "tests/02")
