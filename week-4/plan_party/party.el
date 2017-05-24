(require 'an-lib)
(require 'dash)

(defstruct an/party-problem
  (size 0)
  (weights 0)
  (relations '()))

(defstruct an/tree-node
  idx
  (data nil)
  (parent nil)
  (children nil)
  (visited nil))

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
nodes, with appropriate parent child relationships setup."
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

(defun an/tree-filter (tree-nodes filter)
  "Only nodes matching the filter function are returned as a list"
  (loop for node across tree-nodes
        if (funcall filter node) collect node))

(defun an/tree-find (tree-nodes foundp)
  "First node matching found function is returned"
  (loop for node across tree-nodes
        if (funcall foundp node) do (return node)))

(defun an/tree-node-leafp (node)
  "True if node has no children"
  (eq nil (an/tree-node-children node)))

(defun an/tree-node-rootp (node)
  "True if node has no parents"
  (eq nil (an/tree-node-parent node)))

(defun an/tree-leaves (tree-nodes)
  "Return list of tree's leaves"
  (an/tree-filter tree-nodes 'an/tree-node-leafp))

(defun an/find-tree-root (tree-nodes)
  "Find node with no parent."
 (an/tree-find tree-nodes 'an/tree-node-rootp))

(defun an/sum-optimum-values (node-idxs nodes optimal-values)
  (loop for idx in node-idxs
        for child = (aref tree-nodes idx)
        sum (an/optimal-value-node child tree-nodes optimal-values)))

(defun an/tree-node-grand-children (node tree-nodes)
  (-flatten
   (loop for idx in (an/tree-node-children node)
         for child = (aref tree-nodes idx)
         collect (an/tree-node-children child))))

(defun an/optimal-value-node (tree-node tree-nodes optimal-values)
  (let* ((idx             (an/tree-node-idx tree-node))
         (children        (an/tree-node-children tree-node))
         (leafp            (not children))
         (grand-children  (an/tree-node-grand-children tree-node tree-nodes))
         (cur-node-weight (an/tree-node-data tree-node))
         (opt             (aref optimal-values idx ))
         (optimum-with-node nil)
         (optimum-without-node nil))
    ;; Optimimum for a leaf node is just current node
    (if leafp
        cur-node-weight
      (if opt  ;; Pre-computed optimum
          opt
        (setf optimum-without-node
              (an/sum-optimum-values children tree-nodes optimal-values))
        (setf optimum-with-node
              (+ cur-node-weight
                 (an/sum-optimum-values grand-children tree-nodes optimal-values)))
        (aset optimal-values idx (max optimum-with-node optimum-without-node))))))

(defun an/party-problem-optimum (input)
  "Weight of the maximum independent vertex set ofthe tree input."
  (let* ((pp (an/party-parse-file input))
         (tree-nodes (an/party-build-tree pp))
         (root (an/find-tree-root tree-nodes))
         (optimal-values (make-vector (length tree-nodes) nil)))
    (an/optimal-value-node root tree-nodes optimal-values )))

(defvar an/party-dir "/home/aakarsh/src/c++/coursera/linear_programming/week-4/plan_party" )
(an/party-problem-optimum (concat  an/party-dir  "/tests/03" ))

(ert-deftest an/party-problem-test-01 ()
  (should (equal 1000 (an/party-problem (concat an/party-dir "/tests/01")))))

(ert-deftest an/party-problem-test-02 ()
  (should (equal 2 (an/party-problem (concat an/party-dir "/tests/02") ))))

(ert-deftest an/party-problem-test-03 ()
  (should (equal 11
                 (an/party-problem (concat  an/party-dir  "/tests/03" ))
                 )))


(setf pp1 (an/party-parse-file "tests/01"))
(setf pp2 (an/party-parse-file "tests/02"))
(setf pp3 (an/party-parse-file "tests/03"))


