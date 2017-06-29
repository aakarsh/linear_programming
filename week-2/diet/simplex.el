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
;; PIVOT (N,INDEPENDENT,A,b,c,l,e) :
;;   1. Compute coefficients of entering new basic variable x_e
;;      b'[e] <- b[l]/a[l][e] ;; Where e is entering variable , l is leaving variable
;;      for j in N - {e}: ;; Where N is set of non-basic variables
;;          a'[e][j] <- a[l][j]/a[l][e]
;;      a'[e][l] = 1/a[l][e] ;; The coefficient leaving variable in entering equation
;;
;;   2. Compute the coefficients of remaining constraints
;;      for i in INDEPENDENT - {l}
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
;;      INDEPENDENT' <- INDEPENDENT +{e} - {l}
;;
;;   5. Return transformed solution:
;;      return (N',INDEPENDENT',A',b',c')
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
;;  3. x'[i] = b[i] - a[l][e]*b'[e] for all i in INDEPENDENT'-{e}
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
;;     (N,INDEPENDENT,A,b,c,v) <- InitializeSimplex(A,b,c)
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
;;       for each i in INDEPENDENT :
;;           if a[i][e] > 0:
;;              delta[i] = b[i]/a[i][e]
;;           else: delta[i]= Infinity
;;
;;       leaving l <- pick l in INDEPENDENT , such that min{delta[i] for i in INDEPENDENT}
;;
;;       if delta [l] == Infinity:
;;           return "unbounded"
;;       else:
;;           Pivot using (leaving,entering) pair of variables
;;           (N,INDEPENDENT,A,b,c,v) <- Pivot([N,INDEPENDENT,A,b,c,v],leaving,entering)
;;
;;     Loop Exists when all coefficients in objective function turn
;;     negative. The basic feasible solution is also now the optimal
;;     solution.
;;
;;     for i in range(0,n):
;;         if i in INDEPENDENT: x[i] = b[i]
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
;;       3. let (N, INDEPENDENT, A, b, c, v) <- Pivot(N, INDEPENDENT, A, b, c, v, l, 0) # pivot with x_0 as entering variable
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
  (DEPENDENT :initarg :DEPENDENT
      :initform nil
      :documentation "Used to maintain set of non-basic variables ")
  (INDEPENDENT  :initarg :INDEPENDENT
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
  (let ((INDEPENDENT (oref lp INDEPENDENT))
        (DEPENDENT (oref lp DEPENDENT))
        (A (oref lp A))
        (b (oref lp b))
        (c (oref lp c))
        (v (oref lp v)))

    (s/debug (s/lp:objective-string c v))
    (setf equations
          (loop for i in INDEPENDENT
                collect
                (format "x_%d = %s " i
                        (s/lp:equation-string (aref A i) (aref b i)))))
    (loop for e in equations do
          (s/debug e))))

(defstruct s/equation
  "Representation for single equation"
  (equation nil )
  (constant 0))

(defun s/entering-eq-init (A b INDEPENDENT DEPENDENT
                             leaving   ;; Index of  leaving equation originally in non-basic set
                             entering) ;; Index of entering equation originally in basic set
  ""
  (setq pivot (abs  (table/at A leaving entering)))
  (setq pivot-inverse  (/ 1.0 pivot))

  (setq pivot-pos (positive? (table/at A leaving entering)))
  (setq sign (if pivot-pos -1 1))

  ;; leaving constant
  (setq leaving-constant (aref b leaving))

    ;; entering constant will be scaled by pivot inverse
    (setq entering-constant
          (* leaving-constant pivot-inverse sign))

    ;; entering equation will be scaled
    (setq entering-equation
          (an/vector:scale
           (aref A leaving) (* sign pivot-inverse) :in INDEPENDENT :skip entering)) ;; basic variables are what need to be scaled

    ;; set non-basic variables to be nil
    (loop for non-basic-variable  in DEPENDENT do
          (aset entering-equation non-basic-variable nil))

    (aset entering-equation entering nil)
    (aset entering-equation leaving (* -1.0 pivot-inverse sign))

    (make-s/equation :equation entering-equation
                     :constant entering-constant))

(defun s/substitute-into-equation (equation
                                  substitute-eq
                                  entering-idx
                                  ;;leaving-idx
                                  )  
  "Subsititute the substitute equation into "
  (catch 'return  
    (let* ((current-equation (s/equation-equation equation))
           (current-constant (s/equation-constant equation))
           (entering-var-coefficient (aref current-equation entering-idx))
           (return-constant nil)
           (return-equation
            (make-vector (length current-equation) nil)))

      ;; No substitution to perform
      (if  (or (not entering-var-coefficient)
               (equal 0.0 entering-var-coefficient))
          (throw 'return equation))
      
      (setq entering-constant  (s/equation-constant substitute-eq))
      (setq entering-eq  (s/equation-equation substitute-eq))

      (if (not  current-constant)
          (setq current-constant 0))

      (setq return-constant
            (+ current-constant  (* entering-var-coefficient entering-constant)))

      (loop for variable in (number-sequence 0 (-  (length current-equation) 1) ) ;;variable-set
            for current-coefficient    =  (aref current-equation variable)
            for substitute-coefficient =  (aref entering-eq variable)
            if (and  (not (equal variable entering-idx))
                     (or current-coefficient
                         substitute-coefficient))
            do
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
                (aset return-equation variable (* entering-var-coefficient substitute-coefficient)))
              ))
      
      ;; When we dont't know this
      ;; TODO : Why can i comment this code and it makes no difference ???
      ;; (if leaving-idx
      ;;     (aset return-equation leaving-idx
      ;;           (* entering-var-coefficient
      ;;              (aref entering-eq leaving-idx))))

      ;; return the substituted equations
      (make-s/equation :equation return-equation
                       :constant return-constant))))

(cl-defmethod s/posivitve-objective-coefficent  ((lp  s/lp) variable-idx)
  "Pick entering index to be one wish the first non-negative value in objective function"
  (let* ((objective (oref lp c))
         (coefficient (aref objective variable-idx)))
    (and coefficient (> coefficient 0))))


(cl-defmethod s/pick-entering-idx ((lp  s/lp))
  "Pick entering index to be one wish the first non-negative value in objective function"
  (an/list:find-first
   (oref lp INDEPENDENT)  (lambda (var-idx) (s/posivitve-objective-coefficent lp var-idx))))


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
         (INDEPENDENT  (oref lp INDEPENDENT))  ;; Members of of the basic set
         (DEPENDENT (oref lp DEPENDENT)) ;; Members of the non-basic set
         (slackness (an/make-vector-shape b nil)))

    ;;(make-s/equation :equation (aref A entering-idx))

    ;; After having chosen the entering variable we must pick the
    ;; leaving variable equation to be one with the tightest
    ;; constraints
    ;; find the slackness of all basic variables

    (loop for non-basic-variable in DEPENDENT
          for constant = (aref b non-basic-variable)
          for coefficient = (* -1  (table/at A  non-basic-variable entering-idx ))
          do
          (if (>  coefficient 0)
              (aset slackness non-basic-variable
                    (/ constant coefficient))))

    ;; return index of min slackness non-zero positive
    (an/vector:find-min-idx slackness 'non-nil? 'non-zero-positive?)))


(cl-defmethod s/pivot ((lp s/lp) e l test)
  "Will pivot be changing the roles of entering and leaving
variables"
  (let* (
         (A  (oref lp A))  ;; Input equation coefficents
         (b  (oref lp b))  ;; Constant coefficients
         (c  (oref lp c))  ;; Objective function coefficents
         (v  (oref lp v))  ;; Objecive constnat coefficent
         (INDEPENDENT  (oref lp INDEPENDENT))  ;; Members of of the basic set
         (DEPENDENT (oref lp DEPENDENT)) ;; Members of the non-basic set
         ;; make a set of basic elements for faster look up
         (INDEPENDENT-set (an/set-make :init INDEPENDENT))
         ;; make a set of non-basic elements
         (DEPENDENT-set (an/set-make :init DEPENDENT))
         ;; Recomputed table of coefficients of a
         (ret-A (an/make-table-shape A 0))
         ;; Recomputed objective constant coefficient
         (ret-b (an/make-vector-shape b 0))
         ;; Recomputed value of objective function coefficentis
         (ret-c (an/make-vector-shape c 0))
         ;; Recomputed objective constant coefficent
         (ret-v 0)
         ;; Updated linear program
         (ret-lp  (s/lp :INDEPENDENT INDEPENDENT :DEPENDENT DEPENDENT :b b :c c))
         ;; Leaving equation and entering's coefficent value
         (pivot-coefficient (table/at A l e)))

    ;; We will be dividing the leaving equation's coefficents
    ;; with the pivot coeffient
    (setq entering-equation  (s/entering-eq-init A b INDEPENDENT DEPENDENT l e))

    ;; construct new entering equation
    (aset ret-b e (s/equation-constant entering-equation))
    (aset ret-A e (s/equation-equation entering-equation))

    ;; For every basic equation set-up
    (loop for equation-idx in DEPENDENT
          if (not (equal equation-idx l))
          do
          (setq current-equation
                (make-s/equation :equation (aref A equation-idx)
                                 :constant (aref b equation-idx)))
          (setq new-equation
                (s/substitute-into-equation current-equation
                                            entering-equation
                                            e
                                            ;;l
                                            ))
          
          (setf (aref ret-A equation-idx ) (s/equation-equation new-equation))
          (setf (aref ret-b equation-idx ) (s/equation-constant new-equation)))

    ;; For the objective equation
    (setq objective-equation
          (make-s/equation :equation c :constant v))

    ;; Subsitute the entering equation into objective function
    (setq new-objective-equation
          (s/substitute-into-equation objective-equation entering-equation
                                      e
                                      ;;l
                                      ))
    ;;
    (setq ret-c (s/equation-equation new-objective-equation))
    (setq ret-v (s/equation-constant new-objective-equation))
    ;;
    (an/set-replace! DEPENDENT-set l e)
    (an/set-replace! INDEPENDENT-set  e l)
    ;;
    (setq DEPENDENT (an/set-list DEPENDENT-set :sort '<))
    (setq INDEPENDENT  (an/set-list INDEPENDENT-set :sort '<))

    ;; 5. Create the pivoted instance of the LP
    (s/lp :DEPENDENT DEPENDENT
          :INDEPENDENT  INDEPENDENT
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
  (catch 'unbounded
    (let ((pivot-result lp))
      (while  (s/lp-objective-contains-positive-coefficients? pivot-result)
        (setq entering-idx  (s/pick-entering-idx pivot-result))
        (setq leaving-idx   (s/pick-leaving-idx pivot-result entering-idx))
        (if (or (not leaving-idx ) (not entering-idx))
            (throw 'unbounded nil)
          (setq pivot-result (s/pivot pivot-result entering-idx leaving-idx nil))))
      pivot-result)))

(cl-defmethod s/lp-basic-solution ((lp s/lp))
  "Computes the basic solution by setting all basic variables to
zero and computing values of corresponding non basic
variables. Returns final assignment for all non-basic variables
in the linear program."
  (loop with non-basic-set    =  (oref lp DEPENDENT)
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
  (if (not lp)
      nil ;; unbounded
    (progn
      (setq nb-assignment (s/lp-basic-solution lp))
      (setq sum (s/lp-objective-value lp nb-assignment))
      (make-s/simplex-result
       :assignment nb-assignment
       :max  sum))))


(cl-defmethod s/make-auxiliary-form ((lp s/lp))
  "Creates an auxiliary form."
  (let* ((A (oref lp A))
         (b (oref lp b))

         (DEPENDENT (oref lp DEPENDENT))
         (INDEPENDENT (oref lp INDEPENDENT))

         (n (length DEPENDENT))
         (m (length INDEPENDENT))

         (nvars (+ n m))

         ;; Adding x_0 in slack form to all equations
         (aux-col (an/vector:times [1] nvars))
         (aux-b (an/vector:append b nil))
         ;; Objective function of -x_0
         (aux-v 0)
         ;; append the the objective function
         ;; the added -1 will appear at nvars position in aux-c
         (aux-c (an/vector:append (make-vector nvars nil) -1 ))
         ;; Adding to non-basic variables,
         ;; need to preserve auxiliary form index
         ;; x_0..x_{n-1}
         (aux-DEPENDENT (number-sequence 0 (- n 1)))
         ;; total
         (total (+ n m))
         ;; Adding to basic variables x_n .. x_{n+m-1},
         ;; new variable will be at x_{n+m}
         (aux-INDEPENDENT (number-sequence n nvars)))

    ;;(aux-coefficent-matrix (table/append-column A aux-col))
    (setq aux-simplex  (an/make-table (+ nvars 1) (+ nvars 1) nil))

    ;; Copy in A add a column with 1 as coeffient at position x_nvars
    (table/init aux-simplex A)

    (loop for i from 0 to nvars
          do
          (table/setf aux-simplex i nvars 1))


    ;; Construct the auxiliary linear program
    (s/lp
     :A aux-simplex
     :b aux-b
     :c aux-c
     :v 0
     :DEPENDENT aux-DEPENDENT
     :INDEPENDENT aux-INDEPENDENT)))



(defun s/aux-test ()
  (setq test-input
        (s/lp :c  [3 1 2 0 0 0]
              :b  [0 0 0 30 24 36]
              :v 0
              :DEPENDENT '(0 1 2)
              :INDEPENDENT  '(3 4 5)
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
      ;; Expand b to be size nrows+ncols while copying over
      (setq simplex-b (make-vector nvars nil))
      ;; Copy over b into exteded vector
      (an/vector:init simplex-b b)

      ;; Expand c to the size of nvars
      (setq simplex-c (make-vector nvars nil))
      (an/vector:init simplex-c c)
      (setf simplex-c (an/vector:rshift simplex-c nrows))

      ;; Non-basic variables are numbered from 0 to nrows
      (setq non-basic-variables (number-sequence 0 (- nrows 1)))
      ;; INDEPENDENTasic variables are numbered from nrows to nvars
      (setq basic-variables     (number-sequence nrows (- nvars 1) ))

      ;; find index of non-nil b
      (setq leaving-idx (an/vector:find-min-idx simplex-b 'non-nil?))
      (setq leaving-coeff (aref simplex-b leaving-idx))
      (setq initial-lp
            (s/lp :A  simplex
                  :b  simplex-b
                  :c  simplex-c
                  :DEPENDENT non-basic-variables
                  :INDEPENDENT  basic-variables))
      (if (positive? leaving-coeff)
          (throw 'done initial-lp))


      ;;
      ;; Seem to keep messing up basic and non-basic terminology for
      ;; now keep basic solution to be one where basic variables are
      ;; set to zero.
      ;;
      ;;Using terminalogy of independent variables appear in right
      ;; side of constraints.

      (setq aux-form
            (s/make-auxiliary-form initial-lp))


      (setq feasible-aux-form
            (s/pivot aux-form nvars leaving-idx  nil))
      ;;
      (setq optimal-aux-form
            (s/simplex-pivot-till-opt feasible-aux-form))
      ;;
      (setq assignment
            (s/lp-basic-solution optimal-aux-form))
      ;;
      (setq opt-value
            (s/lp-objective-value optimal-aux-form assignment))
      ;;
      (if (not (equal opt-value 0.0)) ;; infeasible
          (throw 'done nil))

      (when (not (equal (float (aref assignment nvars)) 0.0)) ;; infeasible
        (message "x_%d not assigned 0" (aref assignment nvars))
        (throw 'done nil))

      ;; Substititue dependent variables into original objective function
      (let ((objective  (make-s/equation
                                   :equation (oref initial-lp :c)
                                   :constant (oref initial-lp :v)) ))
        (loop for i in (oref optimal-aux-form  :DEPENDENT)
              for current-equation = (aref (oref optimal-aux-form :A) i)
              for current-constant = (aref (oref optimal-aux-form :b) i)
              do            
              (setq objective
                    (s/substitute-into-equation
                     objective
                     (make-s/equation :equation current-equation
                                      :constant current-constant)
                     i)))
              
        ;; x_nvars will be last variable and last column
        ;; Remove added pseudovariable at x_{n+m}
        ;; remove it.
        
        (setq n (length (oref optimal-aux-form :DEPENDENT)))
        (setq m (length (oref optimal-aux-form :INDEPENDENT)))
        (setq total (+ n m))
        
        (s/lp :A (table/sub-table
                  (oref optimal-aux-form :A)
                  (- total 1)
                  (- total 1))
              :DEPENDENT (oref optimal-aux-form :DEPENDENT)
              :INDEPENDENT (oref optimal-aux-form :INDEPENDENT)
              :b (an/vector:sub-vector  (oref optimal-aux-form :b) 0 (- total 1))
              :c (an/vector:sub-vector  (s/equation-equation  objective) 0 (- total 1))
              :v (s/equation-constant objective))))))

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
    (setq DEPENDENT   '(0 1 2))
    (setq INDEPENDENT   '(3 4 5))
    (s/entering-eq-init A b INDEPENDENT DEPENDENT 5 0))

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
   (s/substitute-into-equation
    main-equation sub-equation (list 0 1 2) 0 5)
   ;;
   (setq objective-equation
         (make-s/equation :equation  [ 3  1  2 nil nil nil nil]
                          ;; x_1 x_2 x_3 x_4 x_4 x_5
                          :constant 0))
   (s/substitute-into-equation
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
              :DEPENDENT    '(0 1 2)
              :INDEPENDENT  '(3 4 5)
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

(defun s/read-input(input-file)
  "Read in simplex from file."  
  (with-temp-buffer
    (insert-file-contents input-file t)
    (goto-char 0)
    (let*((sizes (an/buffer:fetch-lines-as-numbers
                  ;;an/buffer:fetch-line-as-numbers
                  ))
          (m (aref sizes 0))
          (n (aref sizes 1)))
      (setf s/A (make-vector m nil))
      (loop for i from 0 below m do
            (aset s/A i (an/buffer:fetch-lines-as-numbers
                         ;;an/buffer:fetch-line-as-numbers
                         )))
      (setf s/b (an/buffer:fetch-lines-as-numbers
                 ;;an/buffer:fetch-line-as-numbers
                 ))
      (setf s/objective (an/buffer:fetch-lines-as-numbers
                         ;;an/buffer:fetch-line-as-numbers
                         )))))

(defvar s/test-dir "/home/aakarsh/src/MOOC/coursera/linear_programming/week-2/diet/")

(ert-deftest s/test-read-01()
  (should (s/read-input (concat s/test-dir "/tests/01"))))

(ert-deftest s/test-find-opt-01 ()
  (s/read-input (concat s/test-dir "/tests/01"))  
  (setq test (s/make-simplex s/A s/b s/objective))
  (setq result (s/simplex test nil))
  (s/debug "\nResult:%s\nMaximum:%f\n"
           (s/simplex-result-assignment result)
           (s/simplex-result-max result)))

(ert-deftest s/test-find-opt-02 ()
  (s/read-input (concat s/test-dir "/tests/02"))  
  (setq test (s/make-simplex s/A s/b s/objective))
  (should (not test)))

(ert-deftest s/test-find-opt-03 ()
  (s/read-input (concat s/test-dir "/tests/03"))  
  (setq test (s/make-simplex s/A s/b s/objective))
  (should test)
  (setq result (s/simplex test nil))
  (should (not result)))


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
  (s/debug "\nResult:%s\nMaximum:%f\n"
           (s/simplex-result-assignment result)
           (s/simplex-result-max result))
  (should (equal 28.0 (s/simplex-result-max result)))
  (should (an/vector:equal [18.0 0 0 8.0 4.0 0]
                           (s/simplex-result-assignment result))))


(ert-deftest s/test-simplex-infeasible-start ()
  (setq test
        (s/make-simplex
         (vector
          [   2    -1 ]
          [   1    -5 ])
         [2 -4]
         [2 -1]))
  (should test)
  (setq result  (s/simplex test nil))
  (message  "\nResult:%s\nMaximum:%f\n"
            (s/simplex-result-assignment result)
            (s/simplex-result-max result))
  (should (equal 2.0 (s/simplex-result-max result))))


(ert "s/test-" )
