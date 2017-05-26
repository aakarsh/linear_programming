#!/usr/bin/env python3

import sys
import threading

class PartyProblem:
    
    def __init__(self,size=None, weights=[], relations=[]):
        self.size = size
        self.weights = weights
        self.relations = []
        for (a,b) in self.relations:
            self.relations.append((a-1),(b-1))

    def make_tree(self):
        tree = [Vertex(w) for w in self.weights]
        for i in range(0, len(self.relations)):
            (a, b) = self.relations[i]
            tree[a].children.append(b)
            tree[b].children.append(a)
        return tree

    @staticmethod
    def from_input():
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

    def __init__(self,idx, weight, parent, children):
        """tree node """
        self.idx = idx
        self.weight = weight
        self.parent = parent
        self.children = children

    def root(self,nodes):
        """Recursively descend through the root node down."""
        if self.parent:
            nodes[self.parent].root()
        return self

    @staticmethod
    def find_root(nodes):
        """ Find the root of a set of nodes. """
        for node in nodes:
            if not node.parent:
                return node
        return None

class Vertex:
    def __init__(self, weight):
        self.weight = weight
        self.children = []

def dfs(tree, vertex, parent):
    for child in tree[vertex].children:
        if child != parent:
            dfs(tree, child, vertex)

def build_tree(read_tree):
    """Build a tree by going through it."""
    dfs(read_tree,read_tree)


# This is a template function for processing a tree using depth-first
# search.  Write your code here.  You may need to add more parameters
# to this function for child processing.

def MaxWeightIndependentTreeSubset(tree):

    size = len(tree)
    if size == 0:
        return 0
    dfs(tree, 0, -1)

    # You must decide what to return.
    return 0

# This code is used to avoid stack overflow issues
sys.setrecursionlimit(10**6) # max depth of recursion
threading.stack_size(2**26)  # new thread will get stack of such size

def test():
    tree = PartyProblem(5,[1,5,3,7,5],[(5,4),(2,3),(4,2),(1,2)]).make_tree()
    
    print("max independent set weight: %d" % MaxWeightIndependentTreeSubset(tree))

def main():
    tree = PartyProblem.from_input().make_tree()
    weight = MaxWeightIndependentTreeSubset(tree)
    print(weight)

if __name__ == "__main__":
    # This is to avoid stack overflow issues
    threading.Thread(target=main).start()
