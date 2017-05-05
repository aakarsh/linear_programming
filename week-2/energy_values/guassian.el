(defvar g/debug 1)

;; Admitedly this is way too imperative. This provides straight forward
;; and not necessarity efficent means of computing solution of Ax=b
;;
;; Solving equations of the form Ax=b
(defvar g/A nil)
(defvar g/size 0)
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

(defun g/num-lines()
  (count-lines (point-min) (point-max)))

(defun g/make-matrix-2d(r c init)
  (let ((retval (make-vector r nil)))
    (loop for cell across-ref retval do
          (setf cell (make-vector c init)))
    retval))

(defun g/read-equation(input-file)
  "Read the equation from input file into g/A and g/b"
  (with-temp-buffer
    (insert-file-contents input-file t)
    (goto-char 0)
    (let ((size (string-to-number (g/current-line)))
          (i 0))
      ;; Create the matrix
      (setf g/size size)
      (setf g/A (g/make-matrix-2d size size 0))
      (setf g/b (make-vector size 0))

      (forward-line 1)
      (while (< i (-  (g/num-lines) 1))
        (let ((j 0))
          (dolist (cur (split-string (g/current-line)))
            (if (< j size)
                (setf (g/A-at i j) (string-to-number cur))
              (setf (aref g/b i) (string-to-number cur)))
            (incf j)))
          (incf i)
          (forward-line 1)))))

(defmacro g/swapf(r1 r2)
  `(let ((temp nil))
     (setf  temp ,r2)
     (setf ,r2 ,r1)
     (setf ,r1 temp)))

(defun g/vector-swap (v p1 p2)
  (g/swapf (aref v p1) (aref v p2)))

(defun g/swap-rows(r1 r2)
  (loop for c from 0 below (g/ncols) do
        (g/swapf (g/A-at r1 c) (g/A-at r2 c)))
  (g/vector-swap g/b r1 r2))

(defun g/first-false-position(ls)
  "Position of first unset element in vector."
  (loop with pos = 0 for v across ls while v do (incf pos)
        finally (return pos)))

(defun g/select-pivot(used_rows used_columns)
  (let ((pivot (make-g/position :row 0 :column 0)))
    
    (setf (g/position-row pivot)
          (g/first-false-position used_rows))
    
    (setf (g/position-column pivot)
          (g/first-false-position used_columns))

    (let* ((row (g/position-row pivot))
          (col (g/position-column pivot))
          (switch_row row))

      (if (= 0 (g/A-at-position pivot))
          (progn
            (loop for i from row below (g/nrows)
                  while (and (< switch_row (g/nrows))
                             (= 0 (g/A-at switch_row col)))
                  do (incf switch_row))
            (if (< switch_row (g/nrows))
                (g/swap-rows row switch_row)
              (error "Switch row %d" switch_row))))
      pivot)))

(defmacro g/divf(place value)
  `(setf ,place (/ ,place  ,value)))

(defmacro g/concatf(place value &rest rest)
  `(setf ,place (concat ,place ,value ,@rest)))

(defun g/process-pivot(pivot-pos)
  (let* ((pivot-value (* 1.0 (g/A-at-position pivot-pos)))
        (col (g/position-column pivot-pos))
        (row (g/position-row pivot-pos)))

    ;; scale row by pivot value
    (loop for i from 0 below (g/ncols) do
          (g/divf (g/A-at row i) pivot-value))

    (g/divf (aref g/b row) pivot-value)
    ;; pivot row  1 at pivot poistion from scaling
    ;; use it to eliminate all values in pivot column.

    (loop for r from 0 below (g/nrows) do
     (unless (equal r row)
       ;; to eliminated A(r,col) entry we scale the pivot row
       ;; by -A(r,col) then added it
       (let ((scale (* -1.0 (g/A-at r col))))
         (loop for c from 0 below (g/ncols) do
               (incf (g/A-at r c) (* scale (g/A-at row c))))
         (incf (aref g/b r) (* scale (aref g/b row))))))
    ))

(defun g/print-matrix (pivot-pos)
  (let ((prow (g/position-row pivot-pos))
        (pcol (g/position-column pivot-pos))
        (retval ""))    
    (g/concatf retval (loop repeat (g/ncols) concat "---------") "\n")
    
    (loop for i from 0 below (g/nrows) do
     (loop for j from 0 below (g/ncols) do
      (if (and (equal prow i) (equal pcol j))
          (g/concatf retval  (format "[%-4.2f]" (g/A-at i j)))
          (g/concatf retval (format  " %-4.2f " (g/A-at i j)))))
      (g/concatf retval (format  "|%-4.2f\n" (aref g/b i))))
    (g/concatf retval (loop repeat (g/ncols) concat "---------") "\n")
    retval))

(defun g/gausian(input-file)
  (g/read-equation input-file)
  (if (= g/size 0)
      []
    (let* ((size (g/ncols))
           (used-rows (make-vector size nil))
           (used-cols (make-vector size nil)))
      (if g/debug
          (message "Before procesing : \n %s" (g/print-matrix (make-g/position :row 0 :column 0))))
      (loop
       for i from 0 below size do
       (let* ((pivot-position (g/select-pivot used-rows used-cols))
              (pivot-row (g/position-row pivot-position))
              (pivot-col (g/position-column pivot-position)))
         (g/process-pivot pivot-position)
         (if g/debug
             (message (g/print-matrix pivot-position)))
         (aset used-rows pivot-row t)
         (aset used-cols pivot-col t)))
      g/b)))

(g/gausian "tests/02")
