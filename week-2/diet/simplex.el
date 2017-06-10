(require 'an-lib)
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
;;
;; subject to:
;;   x_1   +   x_2 + 3*x_3   <= 30
;; 2*x_1   + 2*x_2 + 5*x_3   <= 24
;; 4*x_1   +   x_2 + 2*x_3   <= 36
;;
;; x_1,x_2,x_3 >= 0
;;
;; We write the above equation into slack form by introducting
;; slack variables x_4,x_5,x_6 such that:
;;
;; x_4  = 30 -   x_1   -   x_2 - 3*x_3
;; x_5  = 24 - 2*x_1   - 2*x_2 - 5*x_3
;; x_6  = 36 - 4*x_1   -   x_2 - 2*x_3
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
;;  x_4 = 30 - (9 - (x_2)/4 - (x_3)/2 - (x_6)/4)  - x_2 - 3*(x_3)
;;  x_4 = 21 - (3*x_2)/4 - (5*x_3)/2 - (x_6)/4
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
;; PIVOT (N,B,A,b,c,l,e) :
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
;;  if x' is the basic solution after a pivot then:
;;  1. x'[j] = 0 for all j \in N'
;;
;;     Since basic solution sets all non-basic values to 0
;;
;;  2. x'[e] = b[l]/a[l][e]
;;
;;  3. x'[i] = b[i] - a[l][e]*b'[e] for all i in B'-{e}
;;
;;  Setting all non-basic variables to zero will leave the recently
;;  computed coefficient for constants.
;;
;;  The goal of the simplex algorithm is to receive a linear program
;;  in standard form and return the vector x_n which maximizes the
;;  objective function. Or report if objecitive function is unbounded
;;  or indeterminate.
;;
;;  InitializeSimplex(A,b,c) : To be discussed later but it tranforms
;;  Simplex input into a slack form where the basic solution is
;;  feasible. As we iterate through various transformations of the
;;  simplex the basic solution will always remain feasible.
;;
;;  Simplex(A, b, c):
;;
;;     (N,B,A,b,c,v) <- InitializeSimplex(A,b,c)
;;
;;     Iterate through the positive coeffients non-basic variables in
;;     the objective function.
;;
;;     while j in N has c[j] > 0:
;;
;;       e <- pick e in N such that c[e] > 0 ;; e will serve as the entering variable
;;
;;       Iterate through basic variable equations, looking for a
;;       leaving variable by locating the most constrainting,
;;       tightest bound on entering variable.
;;
;;       for each i in B :
;;           if a[i][e] > 0:
;;              delta[i] = b[i]/a[i][e]
;;           else: delta[i]= Infinity
;;
;;       leaving l <- pick l in B , such that min{delta[i] for i in B}
;;
;;       if delta [l] == Infinity:
;;           return "unbounded"
;;       else:
;;           Pivot using (leaving,entering) pair of variables
;;           (N,B,A,b,c,v) <- Pivot([N,B,A,b,c,v],leaving,entering)
;;
;;     Loop Exists when all coefficients in objective function turn
;;     negative. The basic feasible solution is also now the optimal
;;     solution.
;;
;;     for i in range(0,n):
;;         if i in B: x[i] = b[i]
;;         else: x[i] = b[i]
;;
;;
;;     Questions:
;;        1. What is the continuous variant of linear programs ?
;;        2. What are the dual variants ?
;;
;;
;;  Returning to problem of constructing a slack form of the Simplex
;;  Method from the Initial input , it is important to understand that
;;  such a conversion may not be simple
;;
;;  Consider the linear program:
;;     maximize { 2*x_1 - x_2 }
;;
;;     under :
;;        2*x_1 - x_2    <= 2
;;        x_1  - 5*(x_2) <= -4
;;
;;        x_1,x_2 >= 0
;;
;;     Setting x_1 = 0 and x_2 = 0  will however violate the constraint x_1 - 5*(x_2) <= -4
;;     Thus the basic solution is not feasible. Thus the equations need to be tranformed into
;;     A form in which the basic solution will be feasible.
;;
;;     The standard technique to solve this impasse is to use the
;;     initial linear program to construct an auxiliary linear program
;;     such that solution of the auxiliary program will suggest a
;;     tranformation of the original program into slack form.
;;
;;     Auxiliary Linear Program:
;;
;;     maximize  -x_0 (Can be read as minimizing x_0)
;;
;;     under:
;;       a_ij - x_0 <= b_i for  i=range(1,n)
;;
;;       x_j >= 0 in range (0,n)
;;
;;
;;     Lemma: The original linear program is feasible if and only if
;;     the auxiliary program is feasible and the optimum/maximum value
;;     of the objective function is 0.
;;
;;     Thus the details of initialize simplex are given by:
;;
;;     InitializeSimplex(A, b, c):
;;

;;
;;       if b[i] >= 0:
;;          return ({1,2,3,...n},{n+1,n+2,...,n+m}, A,b,c
;;
;;       1. Create L_{aux}
;;          1.1. Objective value: -x_0
;;          1.2. \sigma(j=1..n,a_ij -x_o <= b_i)  ;; Add -x_0 to left hand side of every equation
;;
;;       2. x_j >= 0  for j={0,1,..n}
;;
;;       let l be the index of minimum b[i]
;;       l = min{b[i] for i in n}
;;
;;       3. let (N, B, A, b, c, v) <- Pivot(N, B, A, b, c, v, l, 0) # pivot with x_0 as entering variable
;;
;;       4.
;;
;;
;;  References: CLRS -pg 795

(require 'cl)
(require 'eieio)

(defclass s/lp () ; No superclasses
  (
  (NB :initarg :NB
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
      :documentation "Coefficients of the objective function")
  (v  :initarg :v
      :initform nil
      :documentation "The constant part of the objective function"))

  "Representation in basic form of a linear program upon which we
  will be acting.")

(defun s/lp:var-string (index-coefficient)
  (let ((index (car index-coefficient))
        (coefficient (cadr index-coefficient)))
    (cond
     ((eq index 0)
      (if coefficient
          (format " %d " coefficient)))
     ((< coefficient 0 ) (format " - %d x_%d " (abs coefficient) index))
     ((> coefficient 0 ) (format " + %d x_%d " coefficient index))
     (t ""))))

(defun s/lp:equation-string (equation-vec)
  "Convert given printable equation vector to text"
  (setf index-coef-pairs
        (loop for objective  across equation-vec
              for i = 0 then (+ i 1)
              if objective collect (list i objective)))
  (setf variables (mapcar 's/lp:var-string index-coef-pairs))
  (loop for v in variables
        concat (format " %s " v)))

(defun s/lp:objective-string (objective-function)
  (format "Max : %s"
          (s/lp:equation-string  objective-function)))

(cl-defmethod s/print((lp s/lp))
  (let ((B (oref lp B))
        (NB (oref lp NB))
        (A (oref lp A))
        (b (oref lp b))
        (c (oref lp c)))

    (message (s/lp:objective-string c))

    (setf equations
          (loop for i in B
                collect (format "x_%d = %s " i
                                (s/lp:equation-string (aref A (- i 1))))))
    (loop for e in equations do
          (message e))))

(cl-defmethod s/pivot((lp s/lp) e l)
  "Will pivot be changing the roles of entering and leaving
variables"
  (let* ((B  (oref lp B))
         (B-set (an/set-make :init B))
         (NB (oref lp NB))
         (NB-set (an/set-make :init NB))
         (A  (oref lp A))
         (b  (oref lp b))
         (c  (oref lp c))
         (v  (oref lp v))
         (ret-c (make-vector (length c) nil))
         (ret-v nil)
         (ret-b (make-vector (length b)  nil))
         (ret-A (an/vector:make (length A)
                                (lambda (i) (make-vector (length (aref A i))
                                                    nil))))
         (ret-lp  (s/lp :B B :NB NB :b b :c c))
         (pivot-coefficient (table/at A l e))
         (pivot-inverse (/ 1.0 pivot-coefficient)))

    (message "pivot-coefficient[%d][%d]:%d" l e pivot-coefficient)

    ;; 1. Compute the entering variable's final equation using the
    ;;    pivot element (l,e):
    ;; Scale leaving equation's b  by pivot-coefficient
    (aset ret-b e (* (aref b l) pivot-inverse))

    ;; Scale all leaving equation coefficient by pivot-coefficient
    ;; set the the entering equation to be this new scaled leaving equation
    (aset ret-A e
          (an/vector:scale
           (aref A l) pivot-inverse :in NB :skip e))

    ;; set the entering variable's coefficent to be
    (table/setf ret-A e l pivot-inverse)

    ;; 2. For all equations except the leaving equation (for which it
    ;;    would be pointless) we need to re-calculate their
    ;;    coefficient as a result of substitution.

    ;; cur - Will denote the equation which we will be working with
    (loop for cur in B
          for current-entering-coeff = (table/at A cur e)
          if (not (equal cur l)) do

          ;; 2.1 Update the corresponding equation.
          (let* ((b-entering-coeff (aref ret-b e))
                 (delta (* b-entering-coeff current-entering-coeff))

                 ;; 2.1.1 Update coefficient into ret-b

                 (an/vector:subtract-into ret-b b cur delta)))

          ;; 2.2 Update coefficients of other variables in current
          ;;     equation by introducing entering variable as a
          ;;     subsitituion of the leaving variable.

          (loop for var in N
                for cur-var-coeff = (table/at A  cur var)
                for cur-entering-coef = (table/at A cur e)
                for entering-var-coef = (table/at ret-A e var)
                for delta = (* cur-entering-coef entering-var-coef)

                for cur-equation = (aref A cur)
                for new-equation = (aref ret-A cur)

                do

                ;; 2.2.2 Update variables by delta from substituting
                ;; entering equation into current equation.

                (an/vector:subtract-into new-equation cur-equation var  delta)))
    
          ;; 2.3 Update objective function both the constant and
          ;;     variable part.
          (let* ((entering-objective-coeff (aref c e))
                 (entering-constant-coeff  (aref ret-b e))
                 (delta          (* entering-constant-coeff
                                    entering-objective-coeff)))
            
            ;; 2.3.1 Updating by constant part of objective function
            ;;       delta
            (setf ret-v (- v delta)))

          (loop for var in N
                for var-obj-value = (aref c var)
                for entering-obj-value = (aref e var)
                for entering-eq-coeff = (table/at ret-A e var)
                for delta = (* entering-eq-coeff
                               entering-obj-value)                
                if (not (equal var e))                
                do
                (an/vector:subtract-into ret-c c var delta))
          
          ;; 4. Exchange leaving and entering variables in NB and B
          ;;    Entering variable: becomes a     basic variable.
          ;;    Leaving  variable: becomes a non-basic variable.
          
          (an/set-replace! NB-set e l )
          (an/set-replace! B-set  l e )
          
          (setq NB (an/set-list NB-set :sort '<))
          (setq B  (an/set-list B-set :sort '<))

          ;; 5. Create the Pivoted instance of the LP
          (s/lp :NB NB
                :B  B
                :A  ret-A
                :b  ret-b
                :c  ret-c
                :v  ret-v)))


(defvar s/test-input
  (s/lp :c  [nil 3 1 2 nil nil nil]
        :b  [nil nil nil 30 24 36]
        :v 0
        :NB '(1 2 3)
        :B  '(4 5 6)
        :A  (vector   [ nil  nil  nil  nil  nil  nil]
                      [ nil  nil  nil  nil  nil  nil]
                      [ nil  nil  nil  nil  nil  nil]
                      [  -1   -1   -3  nil  nil  nil]
                      [  -2   -2   -5  nil  nil  nil]
                      [  -4   -1   -2  nil  nil  nil])))

(defun s/test-print()
  (setq input s/test-input)
  (s/pivot input 0 1)
  (s/print input))

;; z = 3 x_1 + x_2 + 2*x_3
;; x_1 = undef ;; dont use these while they are non-basic?
;; x_2 = undef
;; x_3 = undef
;; x_4 = 30 -    x_1  -    x_2 - 3*x_3
;; x_5 = 24 - 2* x_1  - 2* x_2 - 5*x_3
;; x_6 = 36 - 4* x_1  -    x_2 - 2*x_3
;;
;; A = [[nil , nil, nil],
;;      [nil , nil, nil],
;;      [nil , nil, nil],
;;      [-1  ,  -1,  -3],
;;      [-2  ,  -2,  -5],
;;      [-4  ,  -1,  -2]]
;;
;; b  = [nil, nil, nil, 30,  24,  36]
;; c  = [nil,   3,   1,  2, nil, nil, nil]
;; B  = {  1,   2,   3}
;; NB = {  4,   5,   6}



;; (defun s/pivot(entering leaving basis-set non-basis-set)
;;   " Pivot a slack form matrix for simplex based optimization
;;   `entering` - index of element becoming basic
;;   `leaving`  - index of element leaving the basic element"
;;
;;   ;; 1. Scale the leaving row of the slack form matrix by the leaving
;;   ;;    entry form
;;   (loop
;;    with pivot-entry = (g/table-at s/A leaving entering)
;;    with b-entering  = (/ (aref s/b leaving) pivot-entry)
;;    for row from 0 below (g/table-ncols s/A) do
;;    (if s/debug
;;        (message "pivot-entry:%d b-entering:%d" pivot-entry b-entering))))

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
