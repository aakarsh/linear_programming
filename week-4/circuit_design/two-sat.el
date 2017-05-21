(require 'an-lib )
(require 'cl-lib)

(defvar sat/num-clauses 0)
(defvar sat/num-variables 0)
(defvar sat/clauses nil)

;; [-x x -y x -z z ]
;; Constraint Graph where:
;; -x is in postion x-1 and
;;  x is in postion x
(defvar sat/constraint-graph nil)

;; (x or y) -> { -x -> y , -y -> x }
;; [x-1][y] = 1
;; [y-1][x] = 1
;; for first-idx = (if (< first 0)
;;                     (- (abs first) 1)
;;                   first)
;; for second-idx = (if (< second 0)
;;                      (- (abs second ) 1)
;;                    second)
;; even odd maybe 0 - -1
;;
;; 0 -> -1 , 1 -> 1 , 2 -> -2 , 3 -> 2 , 4 -> -3,
(defun sat/node-index(literal)
  "Maps a literal integer value x to a node-number in the
constraint graph general scheme for example literal l will be
mapped as :
-l -> (2*l -2)
 l -> (2*l -1)"
  (let ((x (* 2 (abs literal))))
    (if (< literal 0) (- x 2)  (- x 1))))

;; [ 0 -> -1 , 1 -> 1 , 2 -> -2 , 3 -> 2 , 4 -> -3, 5 -> 3 ]
(defun sat/half (x)
  (/ x 2))

(defun sat/literal (node-index)
  "Convert a literal back into a node-index. `node-index' index. This is actactly the inverse "
  (sat/half  (if (evenp node-index) ;; negative literal
                 (* -1 (+ node-index 2 ))
               (+ node-index 1))))

(defun sat/make-cg-clauses(num-variables clauses)
  "Takes number of literal and list of clauses and builds a
   constraint graph."
  (let* ((size (* num-variables 2))
        (graph (table/make size size  nil)))
    (loop for clause in clauses
          for first  = (aref clause 0)
          for neg-first = (* -1 first)
          for second = (aref clause 1)
          for neg-second = (* -1 second)
          do
          (table/setf graph (sat/node-index neg-first)  (sat/node-index second) t)
          (table/setf graph (sat/node-index neg-second) (sat/node-index first) t))
    graph))

(defun sat/make-nodes(num)
  "Returns a vector of sat/nodes with increasing sequence numbers "
  (an/vector:make num (lambda(i) (make-an/graph:node :number i))))

(defun sat/build-constraint-graph(num-variables clauses)
  "Builds a constraint graph which contains both the literal and its conjugation"
  (let ((graph-size (* 2 num-variables)))
    (setf sat/nodes (sat/make-nodes graph-size))
    (setf sat/constraint-graph (sat/make-cg-clauses num-variables clauses))))

(defun sat/make-component-nodes(nodes num-components)
  (let ((component-nodes (sat/make-nodes num-components)))
    (loop for node across nodes
          for component-number = (an/graph:node-component node)
          for component = (aref component-nodes component-number ) do
          (push node (an/graph:node-data component)))
    component-nodes))

(defun sat/make-component-graph(nodes graph num-components)
  "A component graph is a directed acyclic graph which summarises
the original graph containing one vertex per strongly connected
component in the graph."
  (let ((component-graph (table/make num-components num-components nil)))
    (loop for i from 0 below (table/nrows graph )
          for i-cmp =  (an/graph:node-component (aref nodes i)) do
          (loop for j from 0 below (table/ncols graph)
                for j-cmp =  (an/graph:node-component (aref nodes j)) do
                ;; change component number to index
                (if (and  (table/at graph i j)   (not (eq i-cmp j-cmp)))
                    (table/setf component-graph i-cmp j-cmp t))))
    component-graph))

(defun sat/cg-contradictionp (graph nodes)
  "Checks the component assigment for nodes , if the literal and
  its complement reside in the same component it signal's an
  error"
  (loop for node across sat/nodes
        for node-id = (an/graph:node-number node)
        for node-literal =  (sat/literal node-id)
        for complement-literal = (* -1 node-literal)
        for complement-idx = (sat/node-index complement-literal)
        for complement = (aref sat/nodes complement-idx)
        finally (return t)
        always (not  (=  (an/graph:node-component node ) (an/graph:node-component complement)))))

(defun sat/find-satisfying-assignment(graph)
  (let ((num-components 0)
        (satisfiable t))
    ;; Compute and assign components to nodes in the graph
    (setf num-components (an/graph:assign-components graph sat/nodes))
    (setf satisfiable (sat/cg-contradictionp graph sat/nodes))

    (if (not satisfiable)
        nil
      ;; Add node data into component nodes
      (let* ((component-nodes (sat/make-component-nodes sat/nodes num-components))
             (component-graph (sat/make-component-graph sat/nodes graph num-components))
             ;; Determine component post ordering
             (component-post-order   (an/graph:dfs-post-order component-graph component-nodes)))

        ;; Go in Reverse topological order assigning the nodes in the
        ;; component for all literals that are in maybe we need some
        ;; sort of map from component number to nodes.
        (sat/compute-assignment  (reverse  component-post-order))))))


(defun sat/compute-assignment (component-post-order)
  "Takes a component graph, traversing it in reverse topological
   ordering. Assigning all unassigned literals in the components
   the value 1.  `component-post-order' a vector of lists, contains
   components in their reverse topologial order with all the
   nodes they contain as"
  (let ((assignment  (make-vector sat/num-variables nil)))
    (loop for component across component-post-order do
          (loop for node in (an/graph:node-data component)
                for literal = (sat/literal (an/graph:node-number node))
                for idx = (-  (abs literal ) 1) do
                (when (not (aref assignment idx))
                  (if (< literal 0)
                      (aset assignment idx 0)
                    (aset assignment idx 1)))))
    assignment))

(defun sat/nodes-clear-visited (nodes)
  "Mark all nodes as unvisited."
  (loop for node across nodes do
        (setf (an/graph:node-visited node) nil)))

(defun sat/clear()
  (setf sat/num-clauses 0)
  (setf sat/num-variables 0)
  (setf sat/nodes nil)
  (setf sat/clauses nil)
  (setf sat/constraint-graph nil))

(defun sat/file-parseline(line-number line)
  (let ((nums (an/buffer:line-to-numbers line)))
    (if (not (= line-number 0))
        (push nums sat/clauses)
      (setf sat/num-clauses (aref nums 0))
      (setf sat/num-variables (aref nums 1)))))

(defun sat/parse-file(input-file)
  (an/file:map-over-file input-file 'sat/file-parseline))

(defun sat/flip-assingment (a)
  (if (= a 1 ) 0 1))

(defun sat/assign-bool (a)
  (if (= a 1 ) t nil))

(defun sat/check-assignment (clauses assignment)
  "Takes a satisfying assigment and verifies that it satisfies a set of clauses. "
  (let ((retval t))
    (loop for clause in clauses
          for l1 = (aref clause 0)
          for l1-idx = (-  (abs l1) 1)
          for l2 = (aref clause 1)
          for l2-idx = (-  (abs l2) 1)

          for l1-val = (if ( <  l1 0)
                           (sat/flip-assingment  (aref assignment l1-idx)  )
                         (aref assignment l1-idx))
          for l2-val = (if ( <  l2 0)
                           (sat/flip-assingment  (aref assignment l2-idx)  )
                         (aref assignment l2-idx))
          do
          (if  (not (or (sat/assign-bool  l1-val ) (sat/assign-bool l2-val) ))
              (error "Failing clause %s " clause)
              ))
    retval))

(defun sat/check-satisfiable(input-file)
  (let ((assignment nil))
    (sat/clear)
    (sat/parse-file input-file)
    (sat/build-constraint-graph sat/num-variables sat/clauses)
    (setf assignment (sat/find-satisfying-assignment sat/constraint-graph))
    (if assignment
        (sat/check-assignment sat/clauses assignment)
      (message "UNSATISFIABLE"))))

(sat/check-satisfiable "tests/01")
(sat/check-satisfiable "tests/02")

(provide 'sat)
