#!/usr/bin/env python3

import sys
import threading

debug = True

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
        """Parse party problem form stdin."""
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
        """tree node """
        self.idx = idx
        self.weight = weight
        self.parent = parent
        self.children = children

    @staticmethod
    def from_vertex(vertex):
        """ Construct a basic tree node without children and parent
        initialized"""
        return TreeNode(vertex.idx,vertex.weight)

    @staticmethod
    def build_tree(read_vertices):
        """Build a tree by going through it."""

        if debug: print("Read Vertices : %s " % read_vertices)
        
        tree_nodes = [TreeNode.from_vertex(v) for v in read_vertices]

        def vertex_visit(tree,node,parent):
            if parent:
                tree_nodes[node.idx].parent = parent.idx
                parent.children.append(node.idx)
                print("vertex_visit: vertex : %s parent : %s " % (node.idx,parent.idx))
            else:
                # root's children will append them selves to it
                print("vertex_visit: root_vertex : %s  " % (node.idx))

        dfs_graph(read_vertices,pre_visit=vertex_visit)
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
        return "weight: %d children : [%s]" % (self.weight , self.children)

    def __repr__(self):
        return "Vertex(idx:%d,weight:%d,children:%s)" %(self.idx,self.weight,self.children)

def dfs(tree, vertex, parent, pre_visit = None):
    """ DFS on tree does not need to worry about cyces so i think we
    can just go ahaead with it."""

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


def max_weight_subset(node,tree,optimal_values):
    """Find the maximum weighted independent tree subset for a given
    tree"""
    if  len(node.children) == 0:
        return node.weight
    
    if optimal_values[node.idx] : # pre-computed optimum value
        return optimal_values[node.idx]

    # stuck here ....
    # optimum_without_node = sum
    

    return 0

# This code is used to avoid stack overflow issues
sys.setrecursionlimit(10**6) # max depth of recursion
threading.stack_size(2**26)  # new thread will get stack of such size

def test():
    tree = PartyProblem(5,[1,5,3,7,5],[(5,4),(2,3),(4,2),(1,2)]).make_tree()

    simple_tree = TreeNode.build_tree(tree)
    root = TreeNode.find_root(simple_tree)
    
    if debug :print("max independent set weight: %d" % max_weight_subset(simple_tree))

def main():
    tree = PartyProblem.from_input().make_tree()
    weight = max_weight_subset(tree)
    print(weight)

if __name__ == "__main__":
    # This is to avoid stack overflow issues
    threading.Thread(target=main).start()
