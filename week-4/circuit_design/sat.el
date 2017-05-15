(require 'g)
(defvar sat/num-clauses 0)
(defvar sat/num-variables 0)
(defvar sat/clauses nil)
(defstruct sat/node number component visited )

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
      (- (abs number) 1)
    number))

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
           (make-sat/node :number i :component nil :visited nil))))
  (sat/initialize-constraints sat/constraint-graph sat/clauses))

(defun sat/dfs-visit(graph node-num component)
  (loop for neighbour-p across  (aref graph node-num)
        for j = 0  then (+ j 1)
        for node =  (aref sat/nodes j)
        finally
        (progn
          (message "Marking Visited : %d" j)
          (setf (sat/node-visited node) 'visited)
          (setf (sat/node-component node) component))
        do
        (if (and neighbour-p
                 (not (equal (sat/node-visited node) 'visited)))
            (progn
              (message "Start Visit :%d" j)
              (setf (sat/node-visited node) 'visiting)
              (sat/dfs-visit graph j component)))))
        
;; assuming the constraint graph is accurate we need to
;; traverse it and find all the strongly connected components labeling them
(defun sat/find-strong-components(graph)
  (loop for i from 0 below (g/table-nrows graph)
        for node = (aref sat/nodes i)
        for scc-number = 0 then (+ scc-number 1) do
        (if (not (sat/node-visited node))
            (sat/dfs-visit graph i scc-number ))))
        
(defun sat/clear()
  (setf sat/num-clauses 0)
  (setf sat/num-variables 0)
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

(defun sat/foo()
  (sat/clear)
  (sat/parse-file "tests/01")
  (sat/build-constraint-graph)
  ;; one tends to stop when one is on the verge of cognitive dissonance.
  (sat/find-strong-components sat/constraint-graph))


;;(sat/foo)

;;(g/print-table sat/constraint-graph)

(provide 'sat)
