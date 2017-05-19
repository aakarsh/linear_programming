(require 'an-lib )
(require 'cl-lib)

(defvar sat/num-clauses 0)
(defvar sat/num-variables 0)
(defvar sat/clauses nil)

(defstruct sat/node
  number
  (data nil)
  (component nil)
  (visited nil)
  (start-time -1)
  (finish-time -1))

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
;;
(defun sat/half (x) (/ x 2))
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
          for second = (aref clause 1)
          do
          (table/setf graph (sat/node-index (* -1 first))  (sat/node-index second) t)
          (table/setf graph (sat/node-index (* -1 second)) (sat/node-index first) t))
    graph))

(defun sat/make-nodes(num)
  "Returns a vector of sat/nodes with increasing sequence numbers "
  (an/vector:make num (lambda(i) (make-sat/node :number i))))

(defun sat/build-constraint-graph(num-variables clauses)
  "Builds a constraint graph which contains both the literal and its conjugation"
  (let ((graph-size (* 2 num-variables)))
    (setf sat/nodes (sat/make-nodes graph-size))
    (setf sat/constraint-graph (sat/make-cg-clauses num-variables clauses))))

(defun sat/reverse-graph(graph)
  "Create a reverse graph such that if (i,j) is edge
in G then (j,i) is an edge in reverse(G)"
  (loop
   with size = (* 2 sat/num-variables)
   with new-graph = (table/make size size nil)
   finally (return new-graph)
   for row from 0 below (table/nrows  graph) do
   (loop for col below  (table/ncols graph) do
         (if (table/at graph row col)
             (table/setf new-graph col row t)))))

(cl-defun sat/dfs-visit-graph (graph nodes  &key (traverse-order nil) (post-dfs nil) (pre-vist nil) (post-visit nil))
  "Visit a complete graph using dfs. Restarting on each
exhaustion, assumes node is vector "
  (sat/nodes-clear-visited nodes)  
  (loop for node across
        (if traverse-order
            traverse-order  nodes)
        do
        (if (not (sat/node-visited node))
            (progn
              (message "Call dfs-visit :" (sat/node-number node))
              (sat/dfs-visit graph nodes node
                             :pre-visit pre-vist
                             :post-visit post-visit)
              (if post-dfs
                  (funcall post-dfs graph nodes node)))))
  (sat/nodes-clear-visited nodes))

(cl-defun sat/dfs-visit(graph nodes node  &key (pre-visit nil) (post-visit nil))
  "Runs dfs on a `graph' represented by and adjaceny matrix of
vectors, `nodes' is a of nodes containing auxiliary
information about graph nodes. `node' is the node to
visit. `pre-vist' and `post-visit' are optional key word
callbacks called before and after visiting `node`. "
  (message "sat/dfs-visit:call %d" (sat/node-number node))
  (let* ((node-num (sat/node-number node))
         (initial-node node))    
    (if pre-visit
        (progn
          (funcall pre-visit graph nodes node)))
    (loop for neighbour-p across  (aref graph node-num)
          for j = 0  then (+ j 1) ;; node number is hter
           ;; this is wrong since nodes are no long sat/nodes so accessing based on index will not work
          for node =  (aref nodes j)
          finally
          (progn
            (message "Finished Visiting : %d , %s" (sat/node-number initial-node ) initial-node)
            (setf (sat/node-visited initial-node) 'visited)
            (if post-visit
                (funcall post-visit graph nodes initial-node)))
          do
          (if (and neighbour-p
                   (not (equal (sat/node-visited node) 'visited)))
              (progn
                (message "nodes : %s" nodes)
                (message "node : %d ->[j %d neighbour-p %s %s]" node-num j neighbour-p node )
                (message "Started Visiting :%d" (sat/node-number node))
                (setf (sat/node-visited node) 'visiting)
                (sat/dfs-visit graph nodes node :post-visit post-visit :pre-visit  pre-visit)
                (setf (sat/node-visited node) 'visited))))))

(defun sat/nodes-by-decreasing-finish-time(nodes)
  "Returns node by decreasing order of finish times."
  (let ((node-order (make-vector (length nodes) 0)))
    (loop for node across nodes
          for i = 0 then (+ i 1)
          do
          (aset node-order i (sat/node-number node)))
    (setf node-order
          (sort node-order
                (lambda (i j)
                  (let* ((node1 (aref sat/nodes i))
                         (node2 (aref sat/nodes j)))
                    (<  (sat/node-finish-time node1) (sat/node-finish-time node2))))))
    node-order))

(defun sat/make-component-nodes(nodes num-components)
  (let ((component-nodes (sat/make-nodes num-components)))    
    (loop for node across nodes
          for component-number = (sat/node-component node) 
          for component = (aref component-nodes component-number ) do
          (push node (sat/node-data component)))
    component-nodes))

(defun sat/make-component-graph(nodes graph num-components)
  "A component graph is a directed acyclic graph which summarises
the original graph containing one vertex per strongly connected
component in the graph."
  (let ((component-graph (table/make num-components num-components nil)))
    (loop for i from 0 below (table/nrows graph )
          for i-cmp =  (sat/node-component (aref nodes i)) do
          (loop for j from 0 below (table/ncols graph)
                for j-cmp =  (sat/node-component (aref nodes j)) do
                ;; change component number to index
                (if (and  (table/at graph i j)   (not (eq i-cmp j-cmp)))
                    (table/setf component-graph i-cmp j-cmp t))))
    component-graph))

(defun sat/dfs-post-order (graph nodes)
  "Computes the ordering of nodes, from last to finish to first to finish"
  (let ((node-finish-order '()))
    (sat/dfs-visit-graph graph nodes
                         :post-visit (lambda (graph nodes node)
                                       (push node node-finish-order)))
    (an/vector-list node-finish-order)))

(defun sat/assign-components(graph nodes)
  "Find all the strongly connected components:
1. Perform DFS on the graph, compute the completion order of each
node.
2. Starting from first finished , Perform DFS assigning same
component numbers till each component is exhausted.
3. Returns the number of components found."
  (lexical-let ((cur-component-number 0)
                (dfs-post-order (sat/dfs-post-order graph nodes)))    
    ;; Redo dfs this time going through reverse graph in node finish order
    (message "******Start Computing Component Number ********** ")
    (sat/dfs-visit-graph
     (sat/reverse-graph graph)  nodes
     :traverse-order dfs-post-order
     :post-visit (lambda (graph nds nd)                                       
                   (setf (sat/node-component nd) cur-component-number)
                   (message "assign-components : %d component: %d" (sat/node-number nd) (sat/node-component nd)))                         
     :post-dfs (lambda (graph nodes node)
                 (incf cur-component-number)))
    cur-component-number))

(defun sat/find-satisfying-assignment(graph)
  (let ((num-components 0)
        (component-number 0))
    ;; Compute and assign components to nodes in the graph
    (setf num-components (sat/assign-components graph sat/nodes))
    (setf component-number (-  num-components 1))
    ;; Add node data into component nodes    
    (let ((component-post-order nil)
          (component-nodes (sat/make-component-nodes sat/nodes num-components))
          (component-graph (sat/make-component-graph sat/nodes graph num-components)))
      ;; Determine component post ordering
      (setf component-post-order (sat/dfs-post-order component-graph component-nodes))
      ;; Go in Reverse topological order assigning the nodes in the
      ;; component for all literals that are in maybe we need some
      ;; sort of map from component number to nodes.      
      (sat/compute-assignment  component-post-order))))


(defun sat/compute-assignment (component-post-order)
  "Takes a component graph, traversing it in reverse topological
   ordering. Assigning all unassigned literals in the components
   the value 1.  `component-post-order' a vector of lists, contains
   components in their reverse topologial order with all the
   nodes they contain as"
  (let ((assignment  (make-vector sat/num-variables nil)))
    (loop for component across component-post-order do
          (loop for node in (sat/node-data component)
                for literal = (sat/literal (sat/node-number node))
                for idx = (-  (abs literal ) 1) do
                (when (not (aref assignment idx))
                  (if (< literal 0)
                      (aset assignment idx 0)
                    (aset assignment idx 1)))))
    assignment))


;; map node number back into the literal or its negation
;; use that to decide to give the assigment 0 or 1
;; if
;; (aset assignment  )

;; if literals of the components are not assigned then
;; give them a value of 1 their negations will be assigned
;; the value 0 for each node we need to assign the
;; correspoding clause a value of if it has not already
;; been assigned a TODO : how do we go backwards from node
;; the clause ??


(defun sat/nodes-clear-visited (nodes)
  "Mark all nodes as unvisited."
  (loop for node across nodes do
        (setf (sat/node-visited node) nil)))

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

(defun sat/check-satisfiable(input-file)
  (sat/clear)
  (sat/parse-file input-file)
  (sat/build-constraint-graph sat/num-variables sat/clauses)
  (sat/find-satisfying-assignment sat/constraint-graph))

;; (sat/find-satisfying-assignment sat/constraint-graph)

(sat/check-satisfiable "tests/01")

(provide 'sat)
