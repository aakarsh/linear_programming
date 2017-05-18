(require 'g)
(require 'an-alias )
(require 'cl-lib)

(defvar sat/num-clauses 0)
(defvar sat/num-variables 0)
(defvar sat/clauses nil)


(defstruct sat/node  number (component nil) (visited nil) (start-time -1) (finish-time -1))

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

(defun sat/make-constraint-graph(num-variables clauses)
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
  (g/make-vector num (lambda(i) (make-sat/node :number i))))

(defun sat/build-constraint-graph(num-variables clauses)
  "Builds a constraint graph which contains both the literal and its conjugation"
  (let ((graph-size (* 2 num-variables)))
    (setf sat/nodes (sat/make-nodes graph-size))
    (setf sat/constraint-graph (sat/make-constraint-graph num-variables clauses))))

(defun sat/reverse-graph(graph)
  (loop
   with size = (* 2 sat/num-variables)
   with new-graph = (table/make size size nil)
   finally (return new-graph)
   for row from 0 below (table/nrows  graph) do
   (loop for col below  (table/ncols graph) do
         (if (table/at graph row col)
             (table/setf new-graph col row t)))))

(cl-defun sat/dfs-visit(graph nodes node  &key (pre-visit nil) (post-visit nil))
  "Runs dfs on a `graph' represented by and adjaceny matrix of
vectors, `nodes' is a of nodes containing auxiliary
information about graph nodes. `node' is the node to
visit. `pre-vist' and `post-visit' are optional key word
callbacks called before and after visiting `node`. "

  (let ((node-num (sat/node-number node)))
    (if pre-visit
        (progn
          (funcall pre-visit graph nodes node)))
    (loop for neighbour-p across  (aref graph node-num)
          for j = 0  then (+ j 1)
          for node =  (aref nodes j)
          with initial-node = (aref nodes node-num)
          finally
          (progn
            (message "Marking Visited : %d" j)
            (setf (sat/node-visited initial-node) 'visited)
            (if post-visit
                (funcall post-visit graph nodes initial-node)))
          do
          (if (and neighbour-p
                   (not (equal (sat/node-visited node) 'visited)))
              (progn
                (message "Start Visit :%d" j)
                (setf (sat/node-visited node) 'visiting)
                (sat/dfs-visit graph nodes node
                               :post-visit post-visit
                               :pre-visit  pre-visit)
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

(defun sat/make-component-graph(nodes graph num-components)
  (let ((component-graph (table/make num-components num-components nil)))
    (loop for i from 0 below (table/nrows graph )
          for i-cmp =  (sat/node-component (aref nodes i))
          do
          (loop for j from 0 below (table/ncols graph)
                for j-cmp =  (sat/node-component (aref nodes j))
                do
                (if (and  (table/at graph i j)   (not (eq i-cmp j-cmp)))
                    (table/setf component-graph
                                ;; change component number to index
                                i-cmp j-cmp
                                t))))
    component-graph))

(defun sat/find-components(graph nodes)
  (let ((num-components 0)
        (component-number 0)
        (nodes-by-finish-time ()))    
    
    ;; Compute the finish times for all nodes
    (loop for i from 0 below (table/nrows graph)
          for node = (aref nodes i)
          with dfs-time = 0 do
          (if (not (sat/node-visited node))
              (sat/dfs-visit graph nodes node
                             :pre-visit (lambda (graph nodes node)
                                          (incf dfs-time)
                                          (setf (sat/node-start-time node) dfs-time))
                             :post-visit (lambda (graph nodes node)
                                           (push node nodes-by-finish-time)
                                           (setf (sat/node-finish-time node) dfs-time)))))
    
  ;; Clear visiting information
    (loop for node across nodes do
          (setf (sat/node-visited node) nil))
    
    (loop
     for v across (sat/nodes-by-decreasing-finish-time nodes)
     for node = (aref nodes v)
     with dfs-time = 0 do
     (if (not (sat/node-visited node))
         (progn
           (sat/dfs-visit
            (sat/reverse-graph graph) nodes node
            :pre-visit (lambda (graph nodes node)
                         (incf dfs-time)
                         (setf (sat/node-start-time node) dfs-time))                               
            :post-visit (lambda (graph nodes node)
                          (setf (sat/node-finish-time node) dfs-time)
                          (setf (sat/node-component node) component-number)))
           (incf component-number))))
    component-number))



(defun sat/find-satisfying-assignment(graph)
  (let ((num-components 0)
        (component-number 0))
    
    (setf component-number (sat/find-components graph sat/nodes))

    ;; Go through reverse graph, mark out the strongly connected components.

    
    (setf num-components (+ 1 component-number))
    
    (let ((nodes-by-component (make-vector num-components nil))
          (node-finish-order '())
          (component-nodes (sat/make-nodes num-components))
          (component-graph (sat/make-component-graph sat/nodes graph num-components)))
      
      ;; After dfs visit will contain the reverse-topological
      ;; ording strongly connected component vertices based on
      ;; when they finished
      (loop for node across sat/nodes
            for i = 0 then (+ i 1)
            for component-number = (sat/node-component node) do
            (push node (aref nodes-by-component component-number)))
      
      ;; determine component ordering
      (loop for node across component-nodes do
            (if (eq (sat/node-visited node ) nil)
                (sat/dfs-visit component-graph component-nodes node
                               :post-visit
                               (lambda(graph nodes node)
                                 (push node node-finish-order)))))

      ;; Go in Reverse topological order assigning the nodes in the
      ;; component for all literals that are in maybe we need some
      ;; sort of map from component number to nodes      
      (sat/compute-assignment nodes-by-component))))


(defun sat/compute-assignment (nodes-by-component)
  "Takes a component graph, traversing it in reverse topological
   ordering. Assigning all unassigned literals in the components
   the value 1.  `nodes-by-component' a vector of lists, contains
   components in their reverse topologial order with all the
   nodes they contain as"
  (let ((assignment  (make-vector sat/num-variables nil) ))
    (loop for component across nodes-by-component do
          (loop for node in component
                for literal = (sat/literal (sat/node-number node))
                for idx = (-  (abs literal ) 1)
                do
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



(defun sat/clear()
  (setf sat/num-clauses 0)
  (setf sat/num-variables 0)
  (setf sat/nodes nil)
  (setf sat/clauses nil)
  (setf sat/constraint-graph nil))

(defun sat/file-parseline(line-number line)
  (let ((nums (g/line-to-numbers line)))
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

(sat/check-satisfiable "tests/01")

(provide 'sat)
