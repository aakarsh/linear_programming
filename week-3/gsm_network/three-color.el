;; Here we try to reduce graph three coloring problem to an instance
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
;; 2. Every vertex can have ony a single color. This will mean that
;;
;;    case x_i1 = 1  :=> {x_i2 = 0, x_i3 = 0}
;;    case x_i2 = 1  :=> {x_i1 = 0, x_i3 = 0}
;;    case x_i3 = 1  :=> {x_i2 = 0, x_i1 = 0}
;;
;; 3. No neighboring vertices can have the same color :
;;
;;    v_i and v_j are neighbours and (i,j) \in E
;;    then: color(v_i) != color(v_j)
;;     
;;    case x_i1 = 1 :=> x_j1 = 0 [ color(v_j) != 1 ]
;;    case x_i2 = 1 :=> x_j2 = 0 [ color(v_j) != 2 ]
;;    case x_i3 = 1 :=  x_j3 = 0 [ color(v_j) != 3 ]
;; 
(require 'an-lib)
(require 'dash)
(require 'cl)

(defstruct an/3c
  (num-vertices 0)
  (num-edges 0)
  (relations '()))

(defun an/3c-parse-file (in-file)
  "Parse input file to create 3c structure."
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
                 (an/relations:decrement (an/3c-relations gsm))
                 :edge-type 'undirected))
;; 
;;(setf 3c1 (an/3c-parse-file "tests/01"))
;;(setf 3c2 (an/3c-parse-file "tests/02"))
;;(an/3c-graph-build 3c1)
