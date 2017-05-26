#!/usr/bin/env python3

import sys
import threading

debug = False
max_depth = 10
depth_record ={"max_weight_subset":0}

class PartyProblem:

    def __init__(self,size=None, weights=[], relations=[]):
        self.size = size
        self.weights = weights
        self.relations = []
        for (a,b) in relations:
            self.relations.append(((a-1),(b-1)))

    def make_tree(self):
        """Create an instance of vertex tree undirected graph
        representing the party problem"""
        if debug: print("Calling make_tree")
        tree = [ Vertex(i,w) for (i,w) in zip(range(0,self.size),self.weights) ]
        for i in range(0, len(self.relations)):
            (a, b) = self.relations[i]
            tree[a].children.append(b)
            tree[b].children.append(a)
        return tree

    @staticmethod
    def from_input():
        """Read  party problem from stdin."""
        
        pp = PartyProblem()
        pp.size = int(input())
        pp.weights = map(int,input().split())
        while True:
            try:
                line = input()
            except EOFError:
                break
            a,b = tuple(map(int, line.split()))
            pp.relations.append((a-1,b-1))
        return pp

class TreeNode:

    def __init__(self,idx, weight, parent=None, children=[]):
        """Tree node """
        self.tree = None
        self.idx = idx
        self.weight = weight
        self.parent = parent
        self.children = children[:] # tricky-make sure not to attach reference.

    def __repr__(self):
        return "<TreeNode idx:%s , weight : %s , parent : %s , children : %s >"%(self.idx,self.weight,self.parent,self.children)
    
    def __str__(self):
        return self.__repr__();
        
    def grand_children(self):
        gc = []
        for child_idx in self.children:
            gc.extend(self.tree[child_idx].children)
        return gc

    @staticmethod
    def from_vertex(vertex):
        """ Construct a basic tree node without children and parent
        initialized"""
        return TreeNode(vertex.idx,vertex.weight)

    @staticmethod
    def build_tree(read_vertices):
        """Build a tree by going through it."""

        if debug: print("Read Vertices : %s " % read_vertices)
        if debug: print("Read Vertices:")
        for v in read_vertices:
            if debug: print(v)
        # Construct a Tree Node for every vertex
        tree_nodes = [TreeNode.from_vertex(v) for v in read_vertices]
        
        for node in tree_nodes:
            node.tree = tree_nodes
            if debug: print(node)

        def pre_visit(tree,node,parent):            
            if debug: print("vertex_visit: node %s , parent %s" % (node,parent))
            if not parent: # root node has no parents
                return            
            tree_nodes[node.idx].parent = parent.idx
            tree_nodes[parent.idx].children.append(node.idx)

          

        dfs_graph(read_vertices,pre_visit=pre_visit)

        for tree_node in tree_nodes:
            if debug: print(tree_node);
            
        return tree_nodes


    def root(self,nodes):
        """Recursively descend through the root node down."""
        if self.parent:
            nodes[self.parent].root()
        return self

    @staticmethod
    def find_root(nodes):
        """Find the root of a set of nodes."""
        for node in nodes:
            if not node.parent:
                return node
        return None

class Vertex:
    def __init__(self, idx , weight):
        self.weight = weight
        self.idx = idx
        self.visited = False
        self.children = []

    def __str__(self):
        return self.__repr__();

    def __repr__(self):
        return "<Vertex(idx:%d,weight:%d,children:%s)>" %(self.idx,self.weight,self.children)

def dfs(tree, vertex, parent, pre_visit = None):
    if pre_visit:
        pre_visit(tree,vertex,parent)        
    vertex.visited = "visiting"    
    for child_idx in vertex.children:
        #if parent and parent.idx != child:
        child = tree[child_idx]
        if not child.visited:
            dfs(tree,child,vertex,pre_visit)            
    vertex.visited = "visited"

def dfs_graph(tree,pre_visit = None ):
    """Assuming that it is a connected tree """
    root = tree[0] # Arbitrarily pick the first vertex as start
    dfs(tree,root,None, pre_visit)
    return # collect collect using callback.

def sum_node_opts(node_idxs, tree_nodes, optimal_values):
    s = 0
    for idx in node_idxs:
        node = tree_nodes[idx]
        s += max_weight_subset(node,tree_nodes,optimal_values)
    return s

def max_weight_subset(node,tree_nodes,optimal_values):
    """Find the maximum weighted independent tree subset for a given
    tree"""
    

    if debug: print("opts:%s"%optimal_values)
    if debug: print("node %d children %s gc %s" % (node.idx ,node.children,node.grand_children()))    
    if  len(node.children) == 0:
        return node.weight
    
    if optimal_values[node.idx] : # pre-computed optimum value
        return optimal_values[node.idx]

    opt_without_node =  sum_node_opts(node.children,tree_nodes,optimal_values)
    opt_with_node    =  node.weight + sum_node_opts(node.grand_children(),tree_nodes,optimal_values)

    # Set the value of the new optimum node
    optimal_values[node.idx] = max(opt_with_node,opt_without_node)    

    return optimal_values[node.idx]


# This code is used to avoid stack overflow issues
sys.setrecursionlimit(10**6) # max depth of recursion
threading.stack_size(2**26)  # new thread will get stack of such size

def optimum(pp):
    simple_tree = TreeNode.build_tree(pp.make_tree())
    root = TreeNode.find_root(simple_tree)
    if debug: print("Root : %s " % root)
    initial_optimum_values = [None]*len(simple_tree)
    return max_weight_subset(root,simple_tree,initial_optimum_values)


def expect_optimum(pp,expectation):
    try:
        opt = optimum(pp)
        assert(expectation == opt)
        print("SUCCESS:plan another party!")
        return 0
    except AssertionError as e:
        print("FAILURE:Expected [%d] but got [%d] " %(expectation, opt))
        return 1

def test():
    """A test for the party problem questions."""
    pp = PartyProblem(1,[1000],[])
    expect_optimum(pp,1000)
    
    pp= PartyProblem(2,[1,2], [(1,2)])
    expect_optimum(pp,2)
    
    pp = PartyProblem(5,[1,5,3,7,5],[(5,4),(2,3),(4,2),(1,2)])
    expect_optimum(pp,11)

def main():
    pp = PartyProblem.from_input()
    print(optimum(pp))

if __name__ == "__main__":
    # This is to avoid stack overflow issues
    threading.Thread(target=main).start()

