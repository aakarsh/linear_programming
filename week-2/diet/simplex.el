(require 'cl)
(require 'gaussian)


;; Simplex Algorithm
;;
;; Simplex algorithm will be specified using:
;;
;; - A - a constraint matrix such that Ax <= b
;;
;; - b - the bounds on the constraints
;;
;; - x_i - a set of non-negativity constrains x_i >=0 for every
;;   variable in the objective function
;;
;; - c^Tx - an objective function which needs to be maximized.
;;
;; { Ax <=b , x_i >= 0,max{(c^T).x} }
;;
;; Together the constraints Ax <= b and x_i >= 0 define a feasible
;; region - a convex polytope - or are unbounded.
;;
;; (x_1,x_2,....x_n) - is an extreme point if and only if the subset
;; of A_i corresponding to non zero entries are linearly independent ?
;; 
;; For example consider the linear program in standard form:
;;
;; maximize : 3*x_1 + x_2 + 2*x_3
;; subject to:
;; x_1   + x_2 + 3*x_3 <= 30
;; 2*x_1 + 2*x_2 + 5*x_3 <= 24
;; 4*x_1 + x_2 + 2*x_3 <= 36
;;
;; x_1,x_2,x_3 >= 0
;;
;; We write the above equation into slack form by introducting
;; slack variables x_4,x_5,x_6 such that
;;
;; x_4  = 30 - x_1   -  x_2 - 3*x_3
;; x_5  = 24 - 2*x_1 - 2*x_2 - 5*x_3
;; x_6  = 36 - 4*x_1 - x_2 - 2*x_3 
;;
;; x_1,x_2,x_3 >= 0 and x_4,x_5,x_6 >=0
;; 
;; Each slack variable also called basic variables, different values
;; of slack variable specify the `tightness` of the specified
;; constraints. The original variables x_1,x_2,x_3 are called
;; non-basic variables. A particular constraint is tight if for a
;; defined value of non-basic variables the basic variable of that
;; constraint is set to zero.
;;
;; A basic solution is one in which we set all non-basic variables to
;; 0. Thus in above example the basic solution will be :
;;
;; (x_1,x_2,x_3,x_4,x_5,x_6) = (0,0,0,30,24,36)
;;
;; The value of the objective function for this basic solution is z =
;; 3*x_1+x_2 + 2*x_3 = 0 (since all the non basic variables are 0 in
;; the basic solution.
;;
;; The goal of the simplex algorithm will be to increase the value of
;; the objective function by re-writing by using different sets of
;; basic variables such that at each step the value of objective
;; function is greater than its value in the previous step.
;;
;; For example : Consider x_1 which occurs in the objective function
;; with a positive coefficient. If we try to increase the value x_1 we
;; find that we cannot increase it beyond (30,24/2, 36/4)
;; ie. (30,12,9) without resulting in (x_4,x_5,x_6) from becoming
;; negative. Thus the maximum we can increase x_1 will be by setting
;; it to 9, which will is the tightest constraint that x_1 is under.
;;
;; Finding the non-basic variable and its corresponding tightest
;; constraint we now perform a pivot where the role of the non-basic
;; and basic variables are swapped. And corresponding substitution
;; will be performed in all the other equations we have. Thus equation
;; with x_6 becomes :
;;
;; x_1 =  9 - (x_2)/4 - (x_3)/2 - (x_6)/4
;;
;; x_4 = 30 - x_1 - x_2 - 3*x_3
;;
;; becomes :
;; :: x_4 = 30 - (9 - (x_2)/4 - (x_3)/2 - (x_6)/4)  - x_2 - 3*(x_3)
;; :: x_4 = 21 - (3*x_2)/4 - (5*x_3)/2 - (x_6)/4
;;
;; Following the same lines and subsitituing in corresponding
;; equations the pivot is going to transform into :
;;
;; z = 27 + (x_2)/4 + (x_3)/2 - (3*x_6)/4
;; x_1 = 9 - (x_2)/4 - (x_3)/2 - (x_6)/4
;; x_4 = 21 - (3*x_2)/4 - (5*x_3)/2 - (x_6)/2
;; x_5 = 6 - (3*x_2)/2  - 4*x_3 + (x_6)/2
;;
;; Thus we see that in our objective function substitution of basic
;; variable by the non-basic variable ensures that the coefficent of
;; the new basic variable is not negative.
;;
;; In simplex terminolgy of the preceding operation is known as a
;; pivot. The variable x_e (non-basic varaible , x_1 above example )
;; is called the `entering variable`. The variable x_l(basic variable)
;; is called the `leaving variable` when it becomes non-basic. The
;; pivot operation does not change the optimal value of the objective
;; which we are seeking.
;;
;; Computing the new value of the objective function z = 27 + 0 + 0+ 0
;; = 27 which is greater than previous value of the objective function
;; the basic solution is now (x_1,x_2,x_3,x_4,x_5,x_6) =
;; (9,0,0,21,6,0). Thus the pivot operation allowed us to choose a set
;; of basic variables such that the value of the objective function
;; for these new basic variables is greater than the basic solution
;; prior to the pivot.
;;
;; We also notice that we cannot use x_6 to increase the value of the
;; objective function z since it appears with a negative
;; coefficient. Thus we must pick a coefficent with postive
;; coefficient to increase.
;;
;; We keep performing these pivot operations till there are no basic
;; variables with postivie coefficents. Outputing the basic solution
;; which we find in the process.
;;
;; Formal Pivoting Algorithm
;; PIVOT(N,B,A,b,c,l,e) :
;;   1. Compute coefficients of entering new basic variable x_e
;;      b'[e] <- b[l]/a[l][e] ;; Where e is entering variable , l is leaving variable
;;      for j in N - {e}: ;; Where N is set of non-basic variables
;;          a'[e][j] <- a[l][j]/a[l][e]
;;      a'[e][l] = 1/a[l][e] ;; The coefficient leaving variable in entering equation
;;
;;   2. Compute the coefficients of remaining constraints
;;      for i in B - {l}
;;          b'[i] = b[i] - a[i][e]*b'[e]
;;          for j in N - {l}:
;;              a'[i][j] = a[i][j] - a[i][e]* a'[e][j]
;;          a'[i][l] = -a[i][e]
;;
;;   3. Compute the new objective function
;;      v' <- v+c[e]*b'[e]
;;      for j in N - {e}:
;;         c'[j] = c[j] - c[e]*a'[e][j]
;;      c[l] = -c[e]*a'[e][l]
;;
;;   4. Comput new basic and non-basic sets
;;      N' <- N -{e} +{l}
;;      B' <- B +{e} - {l}
;;
;;   5. Return transformed solution:
;;      return (N',B',A',b',c')
;;
;;  Pivot can only be called when a[l][e] != 0 that is the leaving
;;  variable equation's entering variable coefficient is non-negative
;;  to avoid division by zero.
;;
;;  
;;
;;References: CLRS -pg 795

(require 'cl)
(require 'eieio)

(defvar s/debug 1)

(defvar s/A
  nil "Coefficient matrix for Ax \leq b")

(defvar s/b
  nil "Bounds on the inequalities ")

(defvar s/objective
  nil "Objective function to maximize")

(defvar m 0
  "Number of variables in Ax \leq b")

(defvar n 0
  "Number of inequalities in Ax \leq b" )

(defvar s/N
  (make-bool-vector m nil)
  "Used to maintain a set non-basic variables")

(defvar s/B
  (make-bool-vector m nil)
  "Used to represent a set of basic variables")


(defclass s/lp () ; No superclasses
  (
   (N :initarg :N
      :initform nil
      :documentation "Used to maintain set of non-basic variables ")
  (B  :initarg :B
      :initform nil
      :documentation "Used to maintain set of basic variables ")
  (A  :initarg :A
      :initform nil
      :documentation "Coefficient matrix upon which we are acting")
  (b  :initarg :b
      :initform nil
      :documentation "value of slack varaibles")
  (c  :initarg :c
      :initform nil
      :documentation "Coefficients of the objective function"))
    
  "Representation in basic form of a linear program upon which we
  will be acting ")

(cl-defmethod s/pivot((lp s/lp) entering leaving)
  (let ((A (oref lp A)))
    (list 
     (format "A %s " A)     
     (format "Entering %d" entering)
     (format "Leaving %d" leaving))))
  

(defun s/pivot(entering leaving basis-set non-basis-set)
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
       (message "pivot-entry:%d b-entering:%d" pivot-entry b-entering))))

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
  (should (s/read-input (concat s/test-dir "/tests/02"))))
