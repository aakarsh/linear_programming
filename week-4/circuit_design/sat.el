(require 'g)

(defvar sat/num-clauses 0)
(defvar sat/num-variables 0)
(defvar sat/clauses nil)

(defstruct sat/node number component visited start-time finish-time  )

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
(defun sat/node-index(number)
  (if (< number 0)
      (- (* 2 (abs number)) 2)
    (- (* 2 (abs number)) 1)))

(defun sat/initialize-constraints(graph clauses)
    (loop for clause in clauses
          for first  = (aref clause 0)
          for second = (aref clause 1)
          do
          (g/table-setf graph (sat/node-index (* -1 first)) (sat/node-index second) t)
          (g/table-setf graph (sat/node-index (* -1 second)) (sat/node-index first) t)))

(defun sat/build-constraint-graph()
  (setf sat/nodes
        (g/make-vector
         (* 2 sat/num-variables)
         (lambda(i)
           (make-sat/node :number i :component nil :visited nil :start-time -1 :finish-time -1))))
  (sat/initialize-constraints sat/constraint-graph sat/clauses))

(defun sat/reverse-graph(graph)
  (loop
   with size = (* 2 sat/num-variables)
   with new-graph = (g/make-table size size nil)
   finally (return new-graph)
   for row from 0 below (g/table-nrows  graph) do
   (loop for col below  (g/table-ncols graph) do
         (if (g/table-at graph row col)
             (g/table-setf new-graph col row t)))))

;; keep track of time during dfs-visiting 
(defvar sat/dfs-time 0) 

;; TODO: Need to Implement Kosaraju's algorithm.
(defun sat/dfs-visit(graph node-num component )
  (incf sat/dfs-time)
  (setf (sat/node-start-time (aref sat/nodes  node-num)) sat/dfs-time)
  (loop for neighbour-p across  (aref graph node-num)
        for j = 0  then (+ j 1)
        for node =  (aref sat/nodes j)
        with initial-node = (aref sat/nodes node-num) 
        finally
         (progn
           (message "Marking Visited : %d" j)
           (setf (sat/node-visited initial-node) 'visited)           
           (setf (sat/node-finish-time initial-node) sat/dfs-time)
           (setf (sat/node-component initial-node) component))
        do
        (if (and neighbour-p
                 (not (equal (sat/node-visited node) 'visited)))
            (progn
              (message "Start Visit :%d" j)
              (setf (sat/node-visited node) 'visiting)
              (setf (sat/node-component node) component)
              (sat/dfs-visit graph j component )
              (setf (sat/node-visited node) 'visited)))))

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

(defun sat/find-strong-components(graph)
  (setf sat/dfs-time 0)
  
  ;; Compute the finish times for all nodes 
  (loop
   for i from 0 below (g/table-nrows graph)
   for node = (aref sat/nodes i)
   do
   (if (not (sat/node-visited node))
       (sat/dfs-visit graph i -1)))
  
  ;; Clear visiting information
  (loop for node across sat/nodes do
        (setf (sat/node-visited node) nil))
  
  (setf sat/dfs-time 0)
  
  ;; Go through reverse graph  
  (loop
   for v across (sat/nodes-by-decreasing-finish-time sat/nodes)
   for node = (aref sat/nodes v)
   with scc-number  = 0
   do 
   (if (not (sat/node-visited node))
       (progn 
         (incf scc-number) 
         (sat/dfs-visit (sat/reverse-graph graph) v scc-number )))))
        
(defun sat/clear()
  (setf sat/num-clauses 0)
  (setf sat/num-variables 0)
  (setf sat/nodes nil)
  (setf sat/clauses nil)
  (setf sat/constraint-graph nil))

(defun sat/file-parseline(line-number line)
  (let ((nums (g/line-to-numbers line)))
    (if (not (= line-number 0))
        (setf sat/clauses (cons  nums sat/clauses))
      (setf sat/num-clauses (aref nums 0))
      (setf sat/num-variables (aref nums 1))
      (setf sat/constraint-graph
            (g/make-table (* 2 sat/num-variables)  (* 2 sat/num-variables) nil)))))

(defun sat/parse-file(input-file)
  (g/map-over-file input-file 'sat/file-parseline))

(defun sat/check-satisfiable(input-file)
  (sat/clear)
  (sat/parse-file input-file)
  (sat/build-constraint-graph)
  (sat/find-strong-components sat/constraint-graph))


(sat/check-satisfiable "tests/01")

(provide 'sat)
