(require 'an-lib)

(defstruct an/party-problem
  (size 0)
  (weights 0)
  (relations '()))

(defstruct an/tree-node
  idx
  (data nil)
  (parent nil)
  (children nil))

(defun an/party-parse-file(in-file)
  "Parse input file into an instance of the party problem."
  (let ((p (make-an/party-problem)))
  (an/file:map-over-file
   in-file    ;; input file
   (lambda(i line) ;; line number and line
     (cond
      ((= i 0) (setf (an/party-problem-size p) (string-to-number line)))
      ((= i 1) (setf (an/party-problem-weights p) (an/buffer:line-to-numbers line)))
      ((> i 1) (setf (an/party-problem-relations p)
                     (cons (an/buffer:line-to-numbers line) (an/party-problem-relations p)))))))
  p))

(defun an/party-build-tree(party-problem)
  "Construct a tree for the party problem, return the array of
nodes , with appropriate parent child relationships setup. "
  (let* ((pp party-problem)
         (relations (an/party-problem-relations pp))
         (weights   (an/party-problem-weights pp))
         (size (an/party-problem-size pp))
         (tree-nodes (an/vector:make size (lambda (i) (make-an/tree-node :idx i)))))
    
    (loop for w across weights
          for i  = 0 then (+ i 1)
          for node = (aref tree-nodes i )
          do
          (setf (an/tree-node-data node)  w))
    
    (loop for relation in relations
          for boss = (-  (aref relation 0) 1)          
          for boss-node = (aref tree-nodes boss)
          for boss-idx = (an/tree-node-idx boss-node)
          for serf = (- (aref relation 1) 1)
          for serf-node = (aref tree-nodes serf)
          for serf-idx = (an/tree-node-idx serf-node)          
          do
          (push serf-idx  (an/tree-node-children boss-node))
          (setf (an/tree-node-parent serf-node) boss-idx))    
    tree-nodes))


;;(an/party-build-tree pp2)

(setf pp1 (an/party-parse-file "tests/01"))
(setf pp2 (an/party-parse-file "tests/02"))
(setf pp3 (an/party-parse-file "tests/03"))
