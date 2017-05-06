;; Admitedly this is way too imperative. This provides straight forward
;; and not necessarity efficent means of computing solution of Ax=b
;;
;; Solving equations of the form Ax=b
(defvar g/debug 1)
(defvar g/A nil)
(defvar g/size 0)
(defvar g/b nil)

(defstruct g/position row column)

(defmacro g/A-at (i j)
  `(aref (aref g/A ,i) ,j))

(defmacro g/matrix-setf(m i j value)
  `(setf (aref (aref ,m ,i ) ,j)  ,value))

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

(defun g/make-matrix-2d(rows cols cell-value)
  (loop repeat rows vconcat
        (vector (loop repeat cols vconcat (make-vector 1 cell-value)))))

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

(defmacro g/divf(place value)
  `(setf ,place (/ ,place  ,value)))

(defmacro g/concatf(place value &rest rest)
  `(setf ,place (concat ,place ,value ,@rest)))

(defun g/fetch-lines(n)
  (let ((reg-begin nil)
        (reg-end nil))
  (save-excursion
    (goto-char (line-beginning-position))
    (setf reg-begin (point)) 
    (forward-line n)
    (goto-char (line-beginning-position))
    (setf reg-end (point)))
  (split-string (buffer-substring-no-properties reg-begin reg-end) "\n" t)))

(defun g/read-equations(input-file)
  "Read the equation from input file into g/A and g/b"
  (with-temp-buffer
    (insert-file-contents input-file t)
    (goto-char 0)
    (let ((size (string-to-number (g/current-line))))
      (setf g/size size)
      (setf g/A (g/make-matrix-2d size size 0))
      (setf g/b (make-vector size 0))

      (forward-line 1)      

      (loop for current-line in (g/fetch-lines (g/num-lines))
            for i = 0 then (+ i 1) do
            (loop for cell-string in (split-string current-line)
                  for cell-value = (string-to-number cell-string)
                  for j = 0 then (+ j 1) do
            (if (< j size)
                (g/matrix-setf g/A i j cell-value)
              (aset g/b i cell-value)))))))

(defun g/first-unused(ls)
  "Position of first unset element in vector."
  (loop  for v across ls
         for pos = 0 then (+ pos 1) while v
         finally (return pos)))

(defun g/select-pivot(used_rows used_columns)
  (letf* ((pivot  (make-g/position :row    (g/first-unused used_rows)
                                   :column (g/first-unused used_columns)))
          (row (g/position-row pivot))
          (col (g/position-column pivot))
          (switch_row row))
    (if (= 0 (g/A-at-position pivot))
        (progn
          (loop for i from row below (g/nrows)                
                while (and (< switch_row (g/nrows))
                           (= 0 (g/A-at switch_row col)))
                count t into switch_row)          
          (if (< switch_row (g/nrows))
              (g/swap-rows row switch_row))))
    pivot))

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

    (loop for r from 0 below (g/nrows)
          for scale = (* -1.0 (g/A-at r col)) do
     (unless (equal r row)
       ;; to eliminated A(r,col) entry we scale the pivot row
       ;; by -A(r,col) then added it
         (loop for c from 0 below (g/ncols) do
               (incf (g/A-at r c) (* scale (g/A-at row c))))
         (incf (aref g/b r) (* scale (aref g/b row)))))))

(defun g/print-matrix (pivot-pos)
  (let ((prow (g/position-row pivot-pos))
        (pcol (g/position-column pivot-pos))
        (retval ""))

    (defun pivot-cellp(i j)
      (and (equal prow  i) (equal pcol j))) 

    (defun cell-format (i j)
      (format
       (if (pivot-cellp i j) "[%-4.2f]" " %-4.2f ") (g/A-at i j)))

    (defun vline(num)
      (concat (loop repeat num concat "--------") "\n"))

    (g/concatf retval (vline (g/ncols)))

    (loop for i from 0 below (g/nrows) do
          (loop for j from 0 below (g/ncols) do 
                (g/concatf retval (cell-format i j)))
          (g/concatf retval (format  "|%-4.2f\n" (aref g/b i))))

    (g/concatf retval (vline (g/ncols)))
    
    retval))

(defun g/gausian(input-file)
  (g/read-equations input-file)
  (if (= g/size 0)
      []
      (loop
       with size = (g/ncols)
       with used-rows = (make-vector size nil)
       with used-cols = (make-vector size nil)  
       for i from 0 below size
            for pivot-position = (g/select-pivot used-rows used-cols)
            for pivot-row = (g/position-row pivot-position)
            for pivot-col = (g/position-column pivot-position)
            while (not (= (g/A-at pivot-row pivot-col) 0))
            do
            (g/process-pivot pivot-position)
            (if g/debug
                (message (g/print-matrix pivot-position)))
            (aset used-rows pivot-row t)
            (aset used-cols pivot-col t)
            finally (return  g/b))))

(progn
  (assert (equal (g/gausian "tests/01") []))
  (assert (equal (g/gausian "tests/02") [1.0 5.0 4.0 3.0]))
  (assert (equal (g/gausian "tests/03") [3.0 0.0]))
  (assert (equal (g/gausian "tests/04") [0.19999999999999996 0.39999999999999997]))
  (assert (equal (g/gausian "tests/05") [1.0 3.0 5.0 0.0])))
