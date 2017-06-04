;; We try to reduce the existence of a Hamiltonain Path and a graph to
;; an instance of a SAT. Such that if our constructed SAT clause is
;; found to be satisfiable then the there exists a Hamiltonian Path in
;; the original undirected graph G.
;;
;; Hamiltonain Path
;;
;; Definition : A hamiltonian path `P` in a graph `G` is a path which
;; visits every vertex `v \in V(G)` of the graph `G`. Such that each
;; vertex will appear in the path exactly once.
;;
;; A hamiltonian path can be expressed as a permutation of pi of
;; vertices {1,2...,n} such that
;;
;; - pi(i) = j ;; i'th position is occupied by v_j
;;
;; - {pi(i),pi(i+1)} \in G for i from {1..n-1}
;;
;; Reduction of Hamiltionian Path problem to SAT
;;
;; Given a graph G construct a CNF R(G) such that R(G) is satisfiable
;; iff G has a hamiltonian path.
;;
;; We define the boolean variable
;;
;; x_ij - i'th position in the Hamiltonian Path is occupied by the vertex v_j from graph G
;;
;; From the properties of the Hamiltonian Path we can now construct a
;; set of contraints on x_ij which will ensure that our if and only if
;; condition is satisfied.
;;
;; 1. Each vertex j must appear at a position in the graph (AtLeastOnce)
;;
;;    x_1j + x_2j + x_3j + ... + x_nj for every vertex v_j. Thus we
;;    or(+) the fact that vertex v_j will have at least one positional
;;    variable set to true
;;
;; 2. No vertex j will appear more than once in the path (AtMostOnce)
;;
;;    for i in positions 1...n:
;;       for k in positions 1...n:
;;             if i!=j:
;;                  not(x_ij) + not(x_kj) ;; It can't be true that x_ij =1 and x_kj are both true.
;;
;; 3. Every position i in the path must be occupied: (NoEmptyPosition)
;;
;;    for i in postions 1...n:
;;         x_i1 + x_i2 + x_i3 + x_i4 + ... + x_in
;;
;; 4. No-two nodes j and k can occupy the same position: (SimulOccupation)
;;
;;    not(x_ij) + not(x_ik) for all (j,k) That is poisiton i is held uniquely
;;
;; 5. Non-adjacent vertices j and k cannot occupy adjacent positions
;; in the path (AdjacencyPreserving)
;;
;;    not(x_ki) + not(x_{k+1}j): if (v_i,v_j) \not \in E(G)
;;
;;  Mapping clause variables x_ij to sat variable s_i. Since i varies
;;  from 0 to |V| and j also varies from 0 |V|

(require 'an-lib)
(require 'dash)
(require 'cl)

(defstruct an/sat-variable
  (compliment nil)
  (position nil)
  (vertex nil))

(defstruct an/hm-problem
  (num-vertices 0)
  (num-edges 0)
  (relations 0))

(defun an/sat-variable-encode (var num-vertices)
  "Encode the variable `var`   "
  (let ((factor (expt 10  (ceiling  (log  num-vertices  10))))
        (compliment 1))
    (if (an/sat-variable-compliment var)
        (setf compliment -1))
    (* compliment
       (+  (* (+ 1 (an/sat-variable-vertex var)) factor)
           (+ 1  (an/sat-variable-position var))))))

(defun an/sat-variable-decode (num num-vertices)
  "Decode the result of sat."
  (let*  ((factor (expt 10 (ceiling (log num-vertices 10))))
          (compliment nil)
          (num-value (abs num))
          (position (- (% num-value factor)  1))
          (vertex   (- (/ num-value factor ) 1)))
    (if (< num 0)
        (setf  compliment t))
    (make-an/sat-variable
     :vertex vertex
     :position position
     :compliment compliment)))

(defun an/hm-problem-parse-file (in-file)
  "Parse input file to create hm-problem structure"
  (let ((p (make-an/hm-problem)))
    (an/parse-over-file in-file
     (line, count) =>  (l,i)
     :first
     (let ((line-1 (an/buffer:line-to-numbers l)))
       (setf (an/hm-problem-num-vertices p) (aref line-1 0 ))
       (setf (an/hm-problem-num-edges p)    (aref line-1 1 )))
     :rest
     (setf (an/hm-problem-relations p)
           (cons (an/buffer:line-to-numbers l) (an/hm-problem-relations p))))
    p))

(defun an/hm-problem-graph-build(hm-problem)
  "Create a graph which we will try to three-color using a
sat-solver"
  (an/graph:make 'adj-list
                 (an/hm-problem-num-vertices hm-problem)
                 (an/relations:decrement (an/hm-problem-relations hm-problem))
                 :edge-type 'undirected))

(defun an/sat-variable-dispaly (v)
  (format  "x%s_{v-%d,p-%d}"
           (if (an/sat-variable-compliment v) "'" "")
           (an/sat-variable-vertex v)
           (an/sat-variable-position v)))

(defstruct an/hm-clause
  (variables '()))

(defun an/hm-clause-display (c)
  (loop for v in (an/hm-clause-variables c)
        for append = nil then t
        concat (concat (if append " + " "" )
                       (an/sat-variable-dispaly v))))

(defun an/hm-vertex-at-least-once (j num-vertices)
  "Ensure that vertex j appears in at least one position."
  (let ((v-clause (make-an/hm-clause) ))
    (setf (an/hm-clause-variables v-clause)
          (loop for position from 0 below num-vertices
                collect (make-an/sat-variable
                         :compliment nil
                         :position position
                         :vertex j)))
    v-clause))

(defun an/hm-vertices-at-least-once (num-vertices)
  "Generates the conitions that every vertex will appear at lest
one position in the hamiltonian path.(AtLeastOnce)"
  (loop for vertex from 0 below num-vertices
        collect (an/hm-vertex-at-least-once vertex num-vertices)))

(defun an/hm-vertex-at-most-once (j num-vertices)
  "For vertex j generates constraints that it does not exist more than once in the path by taking all pairs of positions and making sure that
vertex that only one of those positions is true "
  (loop for (i k) in  (an/iter:combinations num-vertices)
        collect
        (make-an/hm-clause
         :variables
         (list
          (make-an/sat-variable :compliment t :vertex j :position i)
          (make-an/sat-variable :compliment t :vertex j :position k)))))

(defun an/hm-vertices-at-most-once (num-vertices)
  "Generates constraints that a vertex cannot occur more than
  once in the path (AtMostOnce) "
  (-flatten
   (loop for j from 0 below num-vertices
         collect (an/hm-vertex-at-most-once j num-vertices))))

(defun an/hm-no-empty-positions (num-vertices)
  "Ensure that every position is occupied by at least once
vertex (NoEmptyPosition)."
  (loop
   for position from 0 below num-vertices
   collect
   (make-an/hm-clause
    :variables
    (loop for vertex from 0 below num-vertices
          collect
          (make-an/sat-variable
           :vertex vertex :position position)))))

(defun an/hm-vertex-no-simultaneous-positions (p num-vertices)
  "No two vertices j and k simultaneously occupy position p "
  (loop for (j k) in (an/iter:combinations num-vertices)
        collect
        (make-an/hm-clause
         :variables
         (list
          (make-an/sat-variable :compliment t :vertex j :position p)
          (make-an/sat-variable :compliment t :vertex k :position p)))))

(defun an/hm-vertices-no-simultaneous-positions (num-vertices)
  "For each position make sure it does not get assigned to two
different vertices by adding conditions for each vertex pair"
  (-flatten
   (loop for p from 0 below num-vertices
         collect (an/hm-vertex-no-simultaneous-positions p num-vertices  ))))

(defun an/hm-vertices-no-non-adjacent-vertices (graph)
  "Ensure that every position has at least one vertex."
  (let ((clauses '()))
    (an/graph-compliment graph)
    (loop
     with nodes = (an/graph-nodes graph)
     with num-vertices = (length nodes)
     for node across nodes
     for node-number = (an/graph:node-number node)
     do
     (message "node %d has non-neighbours %s"
              node-number
              (mapcar 'an/graph:node-number  (an/graph-neighbours graph node)))
     (loop for non-neighbour in (an/graph-neighbours graph node)
           for non-neighbour-node-number = (an/graph:node-number non-neighbour)
           if (not (equal node-number non-neighbour-node-number))
           do
           ;; no non-neighbour are non-adjacent vertices.
           (loop for pos from 0 below (-  num-vertices 1) do
                 (push  (make-an/hm-clause
                         :variables
                         (list
                          (make-an/sat-variable  :compliment t :position pos       :vertex node-number)
                          (make-an/sat-variable  :compliment t :position (+ pos 1) :vertex non-neighbour-node-number)))
                        clauses))))
    ;; set it back
    (an/graph-compliment graph)
    clauses))

(defun an/hm-problem-to-clauses(input-file)
  "Parse a input file, build an undirected graph G and convert it
into a set of SAT clauses such that if the SAT problem is
satisfiable then there exists a hamiltonian cycle in the undirect
graph G."
  (let* ((parsed (an/hm-problem-parse-file input-file))
         (num-vertices (an/hm-problem-num-vertices parsed))
         (num-edges    (an/hm-problem-num-edges parsed))
         (input-graph   (an/hm-problem-graph-build parsed))
         (clauses '())
         (output-clauses '()))
    (an/list:extend clauses  (an/hm-vertices-at-least-once num-vertices))
    (an/list:extend clauses (an/hm-vertices-at-most-once num-vertices))
    (an/list:extend clauses (an/hm-no-empty-positions num-vertices))
    (an/list:extend clauses (an/hm-vertices-no-simultaneous-positions  num-vertices))
    ;; Edge dependent
    (setf edge-clasues (an/hm-vertices-no-non-adjacent-vertices input-graph))
    ;;
    (an/list:extend clauses  (an/hm-vertices-no-non-adjacent-vertices input-graph))
    ;; collect output clauses here
    (setf output-clauses
          (loop for c in clauses collect
                (loop for v in (an/hm-clause-variables c)
                      collect (an/sat-variable-encode v num-vertices))))
    ;;
    (setf minisat-output  (an/run-minisat-clauses output-clauses))
    ;;
    (if (an/minisat-satisfiable minisat-output)
        (an/hamilitonian-path-from-sat minisat-output num-vertices)
      nil)))

(defun an/hamilitonian-path-from-sat (minisat-output num-vertices)  
  "Computes the hamiltonian path from minisat assignment."
  (let ((variables (an/minisat-clauses minisat-output)))    
    (setf variables
          (loop for v in variables
                if (> v 0)
                collect (an/sat-variable-decode v num-vertices)))
    (sort variables (lambda (v1 v2)
                      (> (an/sat-variable-position v1)
                         (an/sat-variable-position v2))))    
    (mapcar
     (lambda (v)
       (+  (an/sat-variable-vertex v) 1))
         variables)))

;; (an/hm-problem-to-clauses "tests/01")
;; (an/hm-problem-to-clauses "tests/02")
