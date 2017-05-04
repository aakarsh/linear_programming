(defvar g/debug 1)

;; Admitedly this is way too imperative. This provides straight forward
;; and not necessarity efficent means of computing solution of Ax=b
;; 
;; Solving equations of the form Ax=b
(defvar g/A nil)
(defvar g/b nil)
(defstruct g/position row column)

(defmacro g/A-at (i j)
  `(aref (aref g/A ,i) ,j))

(defmacro g/A-at-position(pos)
  `(g/A-at (g/position-row ,pos)
           (g/position-column ,pos)))

(defun g/nrows()
  (length g/A))

(defun g/ncols()
  (length (aref g/A 0)))

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
                (setf (g/A-at i j) (string-to-number cur))
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
    (if (not (g/A-at-position retval))
        ;; Need to swap rows.
        (message "Need swapping..."))
    retval))

(defun g/process-pivot(pivot-pos)
  (let* ((pivot-value (g/A-at-position pivot-pos))
        (col (g/position-column pivot-pos))
        (row (g/position-row pivot-pos)))
    ;; Scale Row By Pivot Value
    (loop for i from 0 below (g/ncols)
          do
          (setf (g/A-at row i)  (/ (g/A-at row i) pivot-value)))

    (setf (aref g/b row) (/ (aref g/b row) pivot-value))

    ;; pivot row  1 at pivot poistion from scaling
    ;; use it to eliminate all values in pivot column.
    (loop for i from 0 below (g/nrows)
          for j from 0 below (g/ncols)
          do
          (let ((scale (* -1.0 (g/A-at i col))))
            (unless (equal i row) ;; add scaled pivot columen value to this element
              (incf  (g/A-at i j)  (* scale (g/A-at row j)))
              (incf (aref g/b i) (* scale (aref g/b row)))
              )))))


(defun g/print-matrix (pivot-pos)
  (let ((prow (g/position-row pivot-pos))
        (pcol (g/position-column pivot-pos))
        (retval ""))    
  (dotimes (i (g/ncols))
    (setf retval (concat retval  "--------")))
  (setf retval (concat retval "\n"))
  (dotimes (i (g/nrows))
    (dotimes (j (g/ncols))
      (if (and (equal prow i) (equal pcol j))
          (setf retval (concat retval  (format "[%-4.2f]" (g/A-at i j))))
        (setf retval (concat retval (format  " %-4.2f " (g/A-at i j))))))
    
      (setf retval (concat retval (format  "|%-4.2f\n" (aref g/b i)))))
    (dotimes (i (g/ncols))
      (setf retval (concat retval  "--------")))
    (setf retval (concat retval "\n"))
    retval))


(defun g/gausian(input-file)  
  (g/read-equation input-file)
  (let* ((size (g/ncols))
         (used-rows (make-vector size nil))
         (used-cols (make-vector size nil)))
    
    (loop
     for i from 0 below size do
     (let ((pivot-position (g/select-pivot used-rows used-cols)))
       (g/process-pivot pivot-position)
       (if g/debug
           (message (g/print-matrix pivot-position)))
       (setf (aref used-rows (g/position-row pivot-position)) t)
       (setf (aref used-cols (g/position-column pivot-position)) t)))
    g/b))



(g/gausian "tests/02")
