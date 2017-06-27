(require 'an-lib)
(require 'cl)

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


(defmacro s/debug (msg &rest args)
  `(with-current-buffer (get-buffer-create "*simplex:debug*")
     (insert (format (format  "%s\n" ,msg) ,@args))
     (goto-char (point-max))))


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
          (format " %.2f " coefficient)))
     ((< coefficient 0 ) (format " - %.2f x_%d " (abs coefficient) index))
     ((> coefficient 0 ) (format " + %.2f x_%d " coefficient index))
     (t ""))))

(defun s/lp:equation-string (equation-vec equation-constant)
  "Convert given printable equation vector to text"
  (setf index-coef-pairs
        (loop for objective  across equation-vec
              for i = 0 then (+ i 1)
              if objective collect (list i objective)))
  (setf variables (mapcar 's/lp:var-string index-coef-pairs))
  (format "%.2f %-5s" equation-constant
          (loop for v in variables
                concat (format " %s " v))))

(defun s/lp:objective-string (objective-function objective-constant)
  (format "Max : %s"
          (s/lp:equation-string  objective-function objective-constant)))

(cl-defmethod s/print((lp s/lp))
  (let ((B (oref lp B))
        (NB (oref lp NB))
        (A (oref lp A))
        (b (oref lp b))
        (c (oref lp c))
        (v (oref lp v)))

    (s/debug (s/lp:objective-string c v))
    (setf equations
          (loop for i in B
                collect
                (format "x_%d = %s " i
                        (s/lp:equation-string (aref A i) (aref b i)))))
    (loop for e in equations do
          (s/debug e))))

(defstruct s/equation
  "Representation for single equation"
  (equation nil )
  (constant 0))

(defun s/entering-eq-init (A b B NB
                             leaving   ;; Index of  leaving equation originally in non-basic set
                             entering) ;; Index of entering equation originally in basic set
  ""
  (setq pivot (abs  (table/at A leaving entering)))
  (setq pivot-inverse  (/ 1.0 pivot))

    ;; leaving constant
    (setq leaving-constant (aref b leaving))

    ;; entering constant will be scaled by pivot inverse
    (setq entering-constant
          (* leaving-constant pivot-inverse))

    ;; entering equation will be scaled
    (setq entering-equation
          (an/vector:scale
           (aref A leaving) pivot-inverse :in B :skip entering)) ;; basic variables are what need to be scaled

    ;; set non-basic variables to be nil
    (loop for non-basic-variable  in NB do
          (aset entering-equation non-basic-variable nil))

    (aset entering-equation entering nil)
    (aset entering-equation leaving (* -1.0 pivot-inverse))

    (make-s/equation :equation entering-equation
                     :constant entering-constant))

(defun s/substitue-into-equation (equation
                                  substitute-eq
                                  variable-set
                                  entering-idx
                                  leaving-idx)
  "Subsititute the substitute equation into equation"
  (let* ((current-equation (s/equation-equation equation))
         (current-constant (s/equation-constant equation))
         (entering-var-coefficient (aref current-equation entering-idx))
         (return-constant nil)
         (return-equation
          (make-vector (length current-equation) nil)))

    (setq entering-constant  (s/equation-constant substitute-eq))
    (setq entering-eq  (s/equation-equation substitute-eq))
    
    (if (not  current-constant)
        (setq current-constant 0))
    
    (setq return-constant
          (+ current-constant  (* entering-var-coefficient entering-constant)))
    
    (loop for variable in variable-set
          if (not (equal variable entering-idx)) do
          ;; iterate through variables in entering equation
          ;; check current coefficient of the variable
          (let ((current-coefficient  (aref current-equation variable))
                (substitute-coefficient (aref entering-eq variable)))

            (if (not substitute-coefficient)
                (setq substitute-coefficient 0))

            ;; Present in current coefficent
            (if current-coefficient
                (aset return-equation variable
                      (+ current-coefficient
                         (* entering-var-coefficient substitute-coefficient)))
              ;; no current-coefficient
              (aset return-equation variable
                    (* -1  (* entering-var-coefficient substitute-coefficient))))))

    (aset return-equation leaving-idx
                       (* entering-var-coefficient (aref entering-eq leaving-idx)))

    ;; return the substituted equations
    (make-s/equation :equation return-equation
                     :constant return-constant)))

(cl-defmethod s/posivitve-objective-coefficent  ((lp  s/lp) variable-idx)
  "Pick entering index to be one wish the first non-negative value in objective function"
  (let* ((objective (oref lp c))
         (coefficient (aref objective variable-idx)))
    (and coefficient (> coefficient 0))))


(cl-defmethod s/pick-entering-idx ((lp  s/lp))
  "Pick entering index to be one wish the first non-negative value in objective function"
  (an/list:find-first
   (oref lp B)  (lambda (var-idx) (s/posivitve-objective-coefficent lp var-idx))))


(cl-defmethod s/lp-objective-contains-positive-coefficients? ((lp s/lp))
  "Checks that the objecive function has positive coefficeints"
  (an/vector:contains? (oref lp c) 'non-nil? 'non-zero-positive?))

(defun s/variable-slackness (eq var-idx)
  "Defines variable's slackness as -constant/coefficient in the equation"
  (let* ((equation   (s/equation-equation eq))
         (constant   (s/equation-constant eq))
         (coefficient (* -1 (aref equation var-idx))))    
    (if (> coefficient 0)
        (/ constant constant)
      nil)))

(cl-defmethod s/pick-leaving-idx ((lp s/lp) entering-idx)
  "Will pivot be changing the roles of entering and leaving
variables"
  (let* ((A  (oref lp A))  ;; Input equation coefficents
         (b  (oref lp b))  ;; Constant coefficients
         (B  (oref lp B))  ;; Members of of the basic set
         (NB (oref lp NB)) ;; Members of the non-basic set
         (slackness (an/make-vector-shape b nil)))

    ;;(make-s/equation :equation (aref A entering-idx))

    ;; After having chosen the entering variable we must pick the
    ;; leaving variable equation to be one with the tightest
    ;; constraints
    ;; find the slackness of all basic variables

    (loop for non-basic-variable in NB
          for constant = (aref b non-basic-variable)
          for coefficient = (* -1  (table/at A  non-basic-variable entering-idx ))
          do
          (if (>  coefficient 0)
              (aset slackness non-basic-variable
                    (/ constant coefficient))))

    ;; return index of min slackness non-zero positive
    (an/vector:find-min-idx slackness 'non-nil? 'non-zero-positive?))
  )

(cl-defmethod s/pivot ((lp s/lp) e l test)
  "Will pivot be changing the roles of entering and leaving
variables"
  (let* (
         (A  (oref lp A))  ;; Input equation coefficents
         (b  (oref lp b))  ;; Constant coefficients
         (c  (oref lp c))  ;; Objective function coefficents
         (v  (oref lp v))  ;; Objecive constnat coefficent
         (B  (oref lp B))  ;; Members of of the basic set
         (NB (oref lp NB)) ;; Members of the non-basic set
         ;; make a set of basic elements for faster look up
         (B-set (an/set-make :init B))
         ;; make a set of non-basic elements
         (NB-set (an/set-make :init NB))
         ;; Recomputed table of coefficients of a
         (ret-A (an/make-table-shape A 0))
         ;; Recomputed objective constant coefficient
         (ret-b (an/make-vector-shape b 0))
         ;; Recomputed value of objective function coefficentis
         (ret-c (an/make-vector-shape c 0))
         ;; Recomputed objective constant coefficent
         (ret-v 0)
         ;; Updated linear program
         (ret-lp  (s/lp :B B :NB NB :b b :c c))
         ;; Leaving equation and entering's coefficent value
         (pivot-coefficient (table/at A l e)))

    ;; We will be dividing the leaving equation's coefficents
    ;; with the pivot coeffient
    (setq entering-equation  (s/entering-eq-init A b B NB l e))

    ;; construct new entering equation
    (aset ret-b e (s/equation-constant entering-equation))
    (aset ret-A e (s/equation-equation entering-equation))

    ;; For every basic equation set-up
    (loop for equation-idx in NB
          if (not (equal equation-idx l))
          do
          (setq current-equation
                (make-s/equation :equation (aref A equation-idx)
                                 :constant (aref b equation-idx)))
          (setq new-equation
                (s/substitue-into-equation current-equation
                                           entering-equation
                                           B e l))
          (setf (aref ret-A equation-idx ) (s/equation-equation new-equation))
          (setf (aref ret-b equation-idx ) (s/equation-constant new-equation)))

    ;; For the objective equation
    (setq objective-equation
          (make-s/equation :equation c :constant v))
    ;; Subsitute the entering equation into objective function
    (setq new-objective-equation
          (s/substitue-into-equation objective-equation entering-equation
           B e l))
    ;;
    (setq ret-c (s/equation-equation new-objective-equation))
    (setq ret-v (s/equation-constant new-objective-equation))
    ;;
    (an/set-replace! NB-set l e)
    (an/set-replace! B-set  e l)
    ;;
    (setq NB (an/set-list NB-set :sort '<))
    (setq B  (an/set-list B-set :sort '<))
    
    ;; 5. Create the pivoted instance of the LP
    (s/lp :NB NB
          :B  B
          :A  ret-A
          :b  ret-b
          :c  ret-c
          :v  ret-v)))

(defstruct s/simplex-result
  (assignment nil)
  (max 0))


(cl-defmethod s/simplex-pivot-till-opt ((lp s/lp))
  "Keep pivoting on variables till there are no more positive
coefficients in the objective function."
  (catch 'done
    (let ((pivot-result lp))
      (while  (s/lp-objective-contains-positive-coefficients? pivot-result)
        (setq entering-idx  (s/pick-entering-idx pivot-result))
        (setq leaving-idx   (s/pick-leaving-idx pivot-result entering-idx))
        (if (or (not leaving-idx ) (not entering-idx))
            (throw 'done pivot-result)
          (setq pivot-result (s/pivot pivot-result entering-idx leaving-idx nil))))      
      pivot-result)))

(cl-defmethod s/lp-basic-solution ((lp s/lp))
  "Computes the basic solution by setting all basic variables to
zero and computing values of corresponding non basic
variables. Returns final assignment for all non-basic variables
in the linear program."  
  (loop with non-basic-set    =  (oref lp NB)
        with b = (oref lp b)
        with retval = (an/make-vector-shape b 0)        
        for i in non-basic-set  do  (aset retval i (aref b i))
        finally return retval))

;; TODO: Assumes non-basic set gets sequential (0..n) numbering
(cl-defmethod s/lp-objective-value ((lp s/lp) assignment)
  (loop with sum = (oref lp v)
        for obj-coeff across (oref lp c) 
        for i = 0 then (+ i 1)
        for value = (aref assignment i)
        if (and value obj-coeff )
        do
        (incf sum (* obj-coeff value))
        finally return sum))

(cl-defmethod s/simplex ((lp s/lp) in-basic-form)
  ""
  ;; Keep pivoting till all coefficients in objective function are
  ;; negative    
  (setq lp (s/simplex-pivot-till-opt lp))
  
  (setq nb-assignment (s/lp-basic-solution lp))
  (setq sum (s/lp-objective-value lp nb-assignment))
    
  (make-s/simplex-result
   :assignment nb-assignment
   :max  sum))

(cl-defmethod s/make-auxiliary-form ((lp s/lp))
  "Creates an auxiliary form."
  (let* ((A (oref lp A))
         (b (oref lp b))
         ;; Non-basic variables
         (num-non-basic-variables  (length A))
         (n num-non-basic-variables)

         (num-basic-variables (length (aref A 0)))
         (m num-basic-variables)
         ;; In slack form all coefficients are negative
         ;;(coefficient-matrix (table/negate A))
         (coefficient-matrix A)
         ;; Adding x_0 in slack form to all equations
         (aux-col (an/vector:times [1] n))
         (aux-coefficent-matrix (table/push-column aux-col coefficient-matrix))
         ;; Objective function of -x_0
         (aux-v 0)
         (aux-c (an/vector:push-head
                 -1 (make-vector m nil)))
         ;; Adding to non-basic variables,
         ;; need to preserve auxiliary form index
         ;; x_0..x_{n-1}
         (aux-NB (number-sequence 0 (- n 1)))
         ;; total
         (total (+ n m))
         ;; Adding to basic variables x_n .. x_{n+m-1}
         (aux-B (number-sequence n (- total 1))))


    ;; Construct the auxiliary linear program
    (s/lp
     :A aux-coefficent-matrix
     :b b
     :c aux-c
     :v 0
     :NB aux-NB
     :B aux-B)))



(defun s/aux-test ()
  (setq test-input
        (s/lp :c  [3 1 2 0 0 0]
              :b  [0 0 0 30 24 36]
              :v 0
              :NB '(0 1 2)
              :B  '(3 4 5)
              :A  (vector
                   [ nil  nil  nil  nil  nil  nil]
                   [ nil  nil  nil  nil  nil  nil]
                   [ nil  nil  nil  nil  nil  nil]
                   [   -1    -1    -3  nil  nil  nil]
                   [   -2    -2    -5  nil  nil  nil]
                   [   -4    -1    -2  nil  nil  nil])))
  (s/make-auxiliary-form test-input))

(defun s/make-simplex (A b c)  
  "Construct the simplex tableau from input constraints."
  (catch 'done 
    (let* ((nrows  (table/nrows A))
           (ncols  (table/ncols A)) ;; number of non-basic variables
           (nvars  (+ nrows ncols))
           (simplex (an/make-table nvars nvars nil))
           ;; standard slack form will be a square matrix [(nrows+ncols) x (nrows+ncols)]
           ;; with entries of A negated , nil for all non basic columns
           ;; b is expected to have 0 for unused coefficients and be of size nrows
           ;; c is expected to have  
           )
    
      ;; Copy over corresponding rows and columnts into simplex
      (table/init simplex A)
      ;; Corresponding entries are going to be negative for entries in A 
      (table/negate simplex)      
      ;; Make sure basic variables are in correct positions
      (table/rshift simplex nrows)
    
      ;; Expan b to be size nrows+ncols while copying over
      (setq simplex-b (make-vector nvars nil))
      ;; copy over b into exteded vector
      (an/vector:init simplex-b b)

      ;; Expand c to the size of nvars
      ;; TODO can't just do an copy need to shift by nvars
      (setq simplex-c (make-vector nvars nil))
      (an/vector:init simplex-c c)
      (setf simplex-c (an/vector:rshift simplex-c nrows))
    
      ;; non-basic variables are numbered from 0 to nrows
      (setq non-basic-variables (number-sequence 0 (- nrows 1)))
      ;; basic variables are numbered from nrows to nvars
      (setq basic-variables     (number-sequence nrows (- nvars 1) ))

      ;; find index of non nil b
      (setq leaving-idx (an/vector:find-min-idx simplex-b 'non-nil?))
      (setq leaving-coeff (aref simplex-b leaving-idx))
      (if (positive? leaving-coeff)
          (throw 'done (s/lp :A simplex
                             :b simplex-b
                             :c simplex-c
                             :NB non-basic-variables
                             :B basic-variables)))
      
      )))



(cl-defmethod s/simplex-initialize ((lp s/lp))
  "Initialize the simplex algorithm."
  (let* ((A  (oref lp A))
         (b  (oref lp b))
         (c  (oref lp c))
         (NB (oref lp NB))
         (B  (oref lp B))

         ;; Number of non-basic variables
         (n (length NB))

         ;; Number of basic variables
         (m (length B))

         ;; total number of variables x_0..x_{m+n-1}
         (total (+ m n))

         ;; THIS IS WRONG NEED TO COMPUTE
         ;; SIZE OF NON BASIC AND BASIC SETS

         ;; number non basic variables from 0 to (n-1)
         ;; (x_0..x_{n-1})
         ;; (non-basic-variables (number-sequence 0 (- n 1)))

         ;; number basic variables from n to (n+m-1)
         ;; (x_n..x_{n+m-1})
         ;;x(basic-variables (number-sequence n (- total 1)))
         )

    ;; Find the non-basic variable index with minimum coefficient
    ;; set that variable to be the leaving variable.

    (setq l (an/vector:find-min-idx b 'non-nil?))

    ;; Already in basic form all constant-coefficents are positive
    ;; l is index of non-basic with least constant coefficient
    ;; if least constant constant is positive
    (if (positive? (aref b l)) ;; return lp
        ;; Already in basic form , return with our numbering for
        ;; non-basic and basic variables.
        (s/lp  :A A  :b b  :c c  :NB NB   :B  B)

      ;; If b[l] < 0 then we need to transform to basic from using
      ;; pivot.
      (let* ((auxiliary-form (s/make-auxiliary-form lp)))
        
        ;; pivot lp with 0 for entering and l for leaving index
        ;; worried that auxiliary form messes up the laving variable index
        ;; leaving varialbe is a non basic form index
        (setq basic-form (s/pivot auxiliary-form l m nil))
        
        ;; Extract optimal and return values.
        (let* ((optimized-aux-form (s/simplex-pivot-till-opt basic-form))
               (opt-assignment (s/lp-basic-solution optimized-aux-form))
               (opt-value (s/lp-objective-value optimized-aux-form opt-assignment)))
          
          (if (not (equal 0 opt-value)) ;; x_0 is non negative
              nil ;; infeasible solution

            ;; New slack form is feasible  strip away the x_0 row
            ;;
            ;; TODO: I am not sure where x_0 will lie in the basic form. 
            ;; (s/print basic-form)
            
            ;; x_0 is in basic set-? can be removed
            ;; subsititue non basic variables into objective function
            ;; return.
            
            ;; (s/lp
            ;;  :A (table/pop-row basic-form 0 ) ;; is row 0 corresponding to it?
            ;;  :b (oref basic-form b)
            ;;  :c (oref lp c) ;; restore original objective function
            ;;  :v (oref lp v) ;; restore original objective function
            ;;  :NB (oref basic-form :NB) ;; TODO remove 0 from the basic form
            ;;  :B (oref basic-form :B)   ;; TODO remove x_0?
            ;;  )
            )))
      
      ;; add    -x_0  -all equations in A
      ;; using - x_0  -to left side of  A
      )))

(defun s/test-initialize-simplex-simple ()
  (setq A
        (vector
         [ 2    -1 ]
         [ 1    -5 ]))
  (setq b [ 2 -4])
  (setq c [ 2 -1 ])
  (setq v 0)
  ()

  (s/print basic-lp))

(defun s/test-initialize-simplex ()
  (setq A
        (vector
         [ nil  nil  nil  nil]
         [ nil  nil  nil  nil]
         [ -2    1   nil  nil]
         [ -1    5   nil  nil]))
  (setq b [nil nil 2 -4])
  (setq c [2 -1 nil nil])
  (setq v 0)
  (setq non-basic-lp (s/lp :A A :b b :c c :v v :NB '(2 3) :B '(0 1)))
  (setq basic-lp  (s/simplex-initialize non-basic-lp))
  (s/print basic-lp))

;;  z = 2*x_1 - x_2
;;  x_3 = 2 - 2*x_1 + x_2
;;  x_4 = -4 - x_1 + 5*x_2
;;  A = [nil nil nil nil
;;       ]

(defun s/entering-eq-test ()
  (setq A
        (vector
         [ nil  nil  nil  nil  nil  nil]
         [ nil  nil  nil  nil  nil  nil]
         [ nil  nil  nil  nil  nil  nil]
         [   -1    -1    -3  nil  nil  nil]
         [   -2    -2    -5  nil  nil  nil]
         [   -4    -1    -2  nil  nil  nil]))
    (setq b   [nil nil nil 30 24 36])
    (setq NB   '(0 1 2))
    (setq B   '(3 4 5))
    (s/entering-eq-init A b B NB 5 0))

(defun s/substitution-test ()
  (setq main-equation
        (make-s/equation :equation  [   -1  -1  -3 nil nil nil nil]
                         ;; x_1 x_2 x_3 x_4 x_4 x_5
                         :constant 30))
  (setq sub-equation
        (make-s/equation
         :constant 9
         :equation  [nil -.25 -.5  nil nil -.25 ]))
   ;;
   (s/substitue-into-equation
    main-equation sub-equation (list 0 1 2) 0 5)
   ;;
   (setq objective-equation
         (make-s/equation :equation  [ 3  1  2 nil nil nil nil]
                          ;; x_1 x_2 x_3 x_4 x_4 x_5
                          :constant 0))
   (s/substitue-into-equation
      objective-equation  sub-equation  (list 0 1 2)  0 5))



(defun s/test2()
  
  (setq s/test-input
        (s/make-simplex
         (vector          
          [   1    1    3]
          [   2    2    5]
          [   4    1    2])
         [30 24 36]
         [3 1 2]))
  
  (setq input s/test-input)
  (setq result  (s/simplex input t))
  (s/debug "\nResult:%s maximum:%f\n"
           (s/simplex-result-assignment result)
           (s/simplex-result-max result))
  (if result
      (s/simplex-result-max result)
    nil))

(defun s/test()
  (setq s/test-input
        (s/lp :c  [3 1 2 0 0 0]
              :b  [0 0 0 30 24 36]
              :v 0
              :NB '(0 1 2)
              :B  '(3 4 5)
              :A  (vector
                   [ nil  nil  nil  nil  nil  nil]
                   [ nil  nil  nil  nil  nil  nil]
                   [ nil  nil  nil  nil  nil  nil]
                   [   -1    -1    -3  nil  nil  nil]
                   [   -2    -2    -5  nil  nil  nil]
                   [   -4    -1    -2  nil  nil  nil])))
  (setq input s/test-input)
  (setq result  (s/simplex input t))
  (s/debug "\nResult:%s maximum:%f\n"
           (s/simplex-result-assignment result)
           (s/simplex-result-max result))
  (if result
      (s/simplex-result-max result)
    nil))




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

(defun s/read-input(input-file)
  "Read in simplex from file."
  (with-temp-buffer
    (insert-file-contents input-file t)
    (goto-char 0)
    (let*((sizes (an/buffer:fetch-line-as-numbers))
          (m (aref sizes 0))
          (n (aref sizes 1)))
      (setf s/A (make-vector m nil))
      (loop for i from 0 below m do
            (aset s/A i (an/buffer:fetch-line-as-numbers)))
      (setf s/b (an/buffer:fetch-line-as-numbers))
      (setf s/objective (an/buffer:fetch-line-as-numbers)))))

(defvar s/test-dir "/home/aakarsh/src/c++/coursera/linear_programming/week-2/diet")

(ert-deftest s/test-02()
  (should (s/read-input (concat s/test-dir "/tests/02"))))

(ert-deftest s/test-simplex-feasible-start ()
  (setq test
        (s/make-simplex
         (vector          
          [   1    1    3]
          [   2    2    5]
          [   4    1    2])
         [30 24 36]
         [3 1 2]))
  (setq result  (s/simplex test nil))
  (s/debug "\nResult:%s maximum:%f\n"
           (s/simplex-result-assignment result)
           (s/simplex-result-max result))
  (should (equal 28.0 (s/simplex-result-max result))))


