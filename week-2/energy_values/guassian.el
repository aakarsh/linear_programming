;; Admitedly this is way too imperative. This provides straight forward
;; and not necessarity efficent means of computing solution of Ax=b
;;
;; Solving equations of the form Ax=b
(defvar g/debug 1)
(defvar g/A nil)
(defvar g/size 0)
(defvar g/b nil)

(defstruct g/position row column)

(defun g/make-table(rows cols cell-value)
  (loop repeat rows vconcat
        (vector (loop repeat cols vconcat (make-vector 1 cell-value)))))

(defun g/table-nrows(table)
  (length table))

(defun g/table-ncols(table)
  (length (aref table 0)))

(defmacro g/table-at (table i j)
  `(aref (aref ,table ,i) ,j))

(defmacro g/table-setf(m i j value)
  `(setf (aref (aref ,m ,i ) ,j)  ,value))

(defmacro g/table-at-position(table pos)
  `(g/table-at ,table  (g/position-row ,pos)
               (g/position-column ,pos)))

(defun g/table-swap-rows(table r1 r2)
  (loop for c from 0 below (g/table-ncols table) do
        (g/swapf (g/table-at table r1 c) (g/table-at table r2 c))))

(defun g/make-vector(length constructor)
  (let ((retval (make-vector length nil)))
    (loop for i from 0 below length do
          (aset  retval i (funcall constructor i)))
    retval))

(defun g/vector-list(ls)
  (loop with v = (make-vector (length ls) 0)
        for l in ls 
        for i = 0 then (+ i 1)
        do (aset v i l)
        finally (return v)))

(defun g/line-to-numbers(line)
  (g/vector-list
   (mapcar 'string-to-number
           (split-string line " "))))

(defun g/fetch-line-as-numbers()
  (g/vector-list
   (mapcar 'string-to-number
           (split-string (g/fetch-line) " "))))

(defun g/num-lines()
  (count-lines (point-min) (point-max)))

(defmacro g/swapf(r1 r2)
  `(let ((temp nil))
     (setf  temp ,r2)
     (setf ,r2 ,r1)
     (setf ,r1 temp)))

(defun g/vector-swap (v p1 p2)
  (g/swapf (aref v p1) (aref v p2)))

(defun g/swap-rows(r1 r2)
  (g/table-swap-rows g/A r1 r2)
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
    (goto-char (line-end-position))
    (setf reg-end (point))
    ;; AN - 5/14
    ;;    (if (equal (point) reg-begin)
    ;;        (setf reg-end (line-end-position))
    ;;      (setf reg-end (point))
    )
  (forward-line n) ;; change buffer state so curser is n-lines ahead
  (let ((region (buffer-substring-no-properties reg-begin reg-end)))
    (split-string region "\n" t))))

(defun g/fetch-line()
  (car (g/fetch-lines 1)))

(defun g/map-over-file(input-file f)
  (with-temp-buffer
    (insert-file-contents input-file t)
    (goto-char 0)
    (loop with num-lines = (g/num-lines)
          for current-line in (g/fetch-lines num-lines)
          for i = 0 then (+ i 1) do
          (funcall  f i current-line))))

(defun g/read-equations(input-file)
  "Read the equation from input file into g/A and g/b"
  (with-temp-buffer
    (insert-file-contents input-file t)
    (goto-char 0)
    (let ((size (string-to-number (g/fetch-line))))
      (if (= size  0)
          (progn
            (setf g/size 0)
            (setf g/A nil)
            (setf g/b nil))
        (progn
          (setf g/size size)        
          (setf g/A (g/make-table size size 0))
          (setf g/b (make-vector size 0))
          (loop for current-line in (g/fetch-lines (g/num-lines))
                for i = 0 then (+ i 1) do
                (loop for cell-string in (split-string current-line)
                      for cell-value = (string-to-number cell-string)
                      for j = 0 then (+ j 1) do
                      (if (< j size)
                          (g/table-setf g/A i j cell-value)
                        (aset g/b i cell-value)))))))))

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
    (if (= 0 (g/table-at-position g/A pivot))
        (progn
          (loop for i from row below (g/table-nrows g/A)                
                while (and (< switch_row (g/table-nrows g/A))
                           (= 0 (g/table-at g/A switch_row col)))
                count t into switch_row)          
          (if (< switch_row (g/table-nrows g/A))
              (g/swap-rows row switch_row))))
    pivot))

(defun g/process-pivot(pivot-pos)
  (let* ((pivot-value (* 1.0 (g/table-at-position g/A pivot-pos)))
        (col (g/position-column pivot-pos))
        (row (g/position-row pivot-pos)))

    ;; scale row by pivot value
    (loop for i from 0 below (g/table-ncols g/A) do
          (g/divf (g/table-at g/A row i) pivot-value))

    (g/divf (aref g/b row) pivot-value)
    ;; pivot row  1 at pivot poistion from scaling
    ;; use it to eliminate all values in pivot column.

    (loop for r from 0 below (g/table-nrows g/A)
          for scale = (* -1.0 (g/table-at g/A r col)) do
     (unless (equal r row)
       ;; to eliminated A(r,col) entry we scale the pivot row
       ;; by -A(r,col) then added it
         (loop for c from 0 below (g/table-ncols g/A) do
               (incf (g/table-at g/A r c) (* scale (g/table-at g/A row c))))
         (incf (aref g/b r) (* scale (aref g/b row)))))))

(defun g/print-table (table &optional pivot-pos)
    (if (not pivot-pos)
        (setf pivot-pos (make-g/position :row 0 :column 0)))
    (let ((prow (g/position-row pivot-pos))
          (pcol (g/position-column pivot-pos))
          (retval ""))

      (defun cell-format (i j)
        (defun pivot-cellp(i j) (and (equal prow  i) (equal pcol j))) 
        (format
         (if (pivot-cellp i j) "[%-4.2f]" " %-4.2f ") (g/table-at g/A i j)))

      (defun vline(num)
        (concat (loop repeat num concat "--------") "\n"))

      (g/concatf retval (vline (g/table-ncols g/A)))

      (loop for i from 0 below (g/table-nrows g/A) do
            (loop for j from 0 below (g/table-ncols g/A) do 
                  (g/concatf retval (cell-format i j)))
            (g/concatf retval (format  "|%-4.2f\n" (aref g/b i))))
      (g/concatf retval (vline (g/table-ncols g/A)))
      
      retval))

(defun g/gausian(A b)
  (setf g/A A)
  (setf g/b b)
  (setf g/size (g/table-nrows g/A))
  (if (= g/size 0)
      []
      (loop
       with size = (g/table-ncols g/A)
       with used-rows = (make-vector size nil)
       with used-cols = (make-vector size nil)  
       for i from 0 below size
       for pivot-position = (g/select-pivot used-rows used-cols)
       for pivot-row = (g/position-row pivot-position)
       for pivot-col = (g/position-column pivot-position)
       while (not (= (g/table-at g/A pivot-row pivot-col) 0))
       do
       (g/process-pivot pivot-position)
       (if g/debug
           (message (g/print-table  g/A pivot-position)))
       (aset used-rows pivot-row t)
       (aset used-cols pivot-col t)
       finally (return  g/b))))

(defun g/gausian-file(input-file)
  (g/read-equations input-file)
  (g/gausian g/A g/b))

(ert-deftest g/test-01()
  (should (equal (g/gausian-file "tests/01") [])))

(ert-deftest g/test-02()
  (should (equal (g/gausian-file "tests/02") [1.0 5.0 4.0 3.0])))

(ert-deftest g/test-03()
  (should (equal (g/gausian-file "tests/03") [3.0 0.0])))

(ert-deftest g/test-04()
  (should (equal (g/gausian-file "tests/04") [0.19999999999999996 0.39999999999999997])))

(ert-deftest g/test-05()
  (assert (equal (g/gausian-file "tests/05") [1.0 3.0 5.0 0.0])))

(provide 'gaussian)











