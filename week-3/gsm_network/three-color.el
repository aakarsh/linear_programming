;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Here we try to reduce graph three-coloring problem to an instance
;; of SAT. Such that finding a satisfying assignment will also provide
;; a coloring for a graph G with vertices V and edges E. G(V,E) being
;; the input graph.
;;
;; x_ij -> {vertex i has color j} where [j \in {1,2,3}]
;;
;; 1. For vertex v_i we will create three variables {x_i1, x_i2, x_i3}
;;    such that:
;;
;;    case x_i1 = 1 :=> color[v_i] = 1
;;    case x_i2 = 1 :=> color[v_i] = 2
;;    case x_i3 = 1 :=> color[v_i] = 3
;;
;; 2. Every vertex can have only a single color. This will mean that :
;;
;;    The satisfying state that at least one color is assigned to a
;;    vertex v_i:
;;
;;        [x_i1 or x_i2 or x_i3] => [x_i1 + x_i2 + x_i3]
;;
;;    A vertex can not be assigned two different colors :
;;
;;    not[or [x_i1 and x_i3]
;;           [x_i1 and x_i2]
;;           [x_i2 and x_i3]]
;;
;;    [and not[x_i1 and x_i3]
;;         not[x_i1 and x_i2]
;;         not[x_i2 and x_i3]] =>
;;
;;    [and [not(x_i1) or not(x_i3)] [not(x_i1) or not(x_i2)] [not(x_i2) or not(x_i3)]
;;    (not(x_i1) + not(x_i3)) . (not(x_i1) + not(x_i2)).  (not(x_i2) + not(x_i3))
;;
;;
;; (defun an/exclusive-coloring(a b c)
;;   (and (not (and a b))
;;        (not (and a c))
;;        (not (and b c))))
;;
;; (loop
;;  with cons-list = '()
;;  for i from 0 below 2
;;  finally (return  cons-list)
;;  do
;;  (loop
;;   for j from 0 below 2
;;   do
;;   (loop
;;    for k from 0 below 2
;;   do
;;   (message
;;    "str :(%s,%s,%s) : coloring: %s " (oddp i) (oddp j) (oddp k)
;;        (an/exclusive-coloring  (oddp i) (oddp j) (oddp k))))))
;;
;; 3. No neighboring vertices can have the same color
;;
;;    v_i and v_j are neighbours and (i,j) \in E
;;    then: [color(v_i) != color(v_j)]
;;
;;    The color of a vertex v_i can be defined as a triple:
;;
;;    color(v_i) = (x_i1,x_i2,x_i3)
;;    color(v_j) = (x_j1,x_j2,x_j3)
;;
;;    [not [and [== x_i1 x_j1] [== x_i2 x_j2] [== x_i3 x_j3]]]
;;
;;    This property is will depend on the actual structure of the
;;    graph and will require the addition of a clause:
;;
;;    \forevery edge e \in E(G):
;;
;;    [== x_i1 x_j1 ]
;;      => (x_i1 and x_j1) or (not(x_i1) and not(x_j1))
;;
;;    [!= x_i1 x_j1] XOR
;;
;;    => not [== x_i1 x_j1 ]
;;    => not [[x_i1 and x_j1] or [not[x_i1] and not[x_j1]]]
;;    => not[x_i1 and x_j1] . not[  not[x_i1] and not[x_j1] ]
;;    => [ not(x_i1) or not(x_j1) ] . [ x_i1 or x_j1 ]
;;    => [ not(x_i1) + not(x_j1) ] . [ x_i1 + x_j1 ]
;;    => (x_i1 + x_j1).(not(x_i1) + not(x_j1))
;;
;;    SAT_Products= {..}
;;
;;    for every edge (i,j) in E(G):
;;        SAT_Products += (x_i1+x_j1)
;;        SAT_Products += (not(x_i1) + not(x_j1))
;;
;;    Converting from variable form into actual output.
;;
;;   Output format :
;;        <number of clauses>  <number of variables>
;;        +/- variable_1  +/ var_2 ...... +/- var_k 0
;;        Where variables are labeled starting from 1 and ending at k.
;;
;;  Variable Numbering:
;;
;;         x_ij form the set of all introduced labels where i \in
;;         (1..|V|) and j \in (1,2,3) Thus total number of variables
;;         introduced will be 3*|V|
;;
;;         x_11 -> 1, x_12 -> 2, x_13 -> 3
;;         x_21 -> 4, x_22 -> 5, x_23 -> 6
;;         x_31 -> 7, x_32 -. 8, x_33 -> 7
;;
;;         ...x_ij -> i*3+j+1 assuming i in [0, |V|-1[ and j in [0, 2]
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(require 'an-lib)
(require 'dash)
(require 'cl)

(defvar an/3c-num-colors 3)

(defstruct an/3c
  (num-vertices 0)
  (num-edges 0)
  (relations '()))

(defun an/3c-parse-file (in-file)
  "Parse input file to create 3c structure"
  (let ((p (make-an/3c)))
    (an/parse-over-file in-file
     (line, count) =>  (l,i)
     :first
     (let ((line-1 (an/buffer:line-to-numbers l)))
       (setf (an/3c-num-vertices p) (aref line-1 0 ))
       (setf (an/3c-num-edges p)    (aref line-1 1 )))
     :rest
     (setf (an/3c-relations p)
           (cons (an/buffer:line-to-numbers l) (an/3c-relations p))))
    p))

(defun an/3c-graph-build(3c)
  "Create a graph which we will try to three-color using
a sat-solver"
  (an/graph:make 'adj-list
                 (an/3c-num-vertices 3c)
                 (an/relations:decrement (an/3c-relations 3c))
                 :edge-type 'undirected))

(defun an/vertex-has-at-least-one-color (num-vertices)
  "Returns a list of clauses per vertex, each clause will
represent the fact that the vertex v_i has at least one color j
\in [0,1,2]."
  (let ((clauses '()))
    (loop
     for at-least-one-color = '()
     for i from 0 below num-vertices do
     (loop for  j from 0 below an/3c-num-colors do
           (push (vector nil i j) at-least-one-color))
     (push at-least-one-color clauses))
    clauses))

(defun an/combinatorial-pairs (n)
  "Generates a set of pairs of $n$ numbers."
  (let ((pairs '()))
    (loop for i from 0 below n  do
          (setf pairs
                (append
                 (loop for j from (+ 1 i) below n
                       collect (vector  i j))
                                pairs)))
    pairs))

(defun an/vertex-has-exclusive-coloring (num-vertices)
  "Returns a list of clauses which ensure that a it does not get
assigned more than a single color. Negation of a clause variable
is represented by 'not type."
  (let ((clauses '()))
    (loop for i from 0 below num-vertices do
          (loop for p in (an/combinatorial-pairs an/3c-num-colors)
                for p1 = (aref p 0)
                for p2 = (aref p 1)
                do
                (push (list (vector t i p1 )
                            (vector t i p2))
                      clauses)))
    clauses))

(defun an/vertex-clauses(num-vertices)
  "Return a list of clause vectors where each variable is
represented by a pair."
  (let ((clauses nil))
    (push (an/vertex-has-at-least-one-color num-vertices) clauses)
    (setf clauses (append (an/vertex-has-exclusive-coloring num-vertices) clauses))
    clauses))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
