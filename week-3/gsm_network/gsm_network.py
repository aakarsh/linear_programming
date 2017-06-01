#!/usr/bin/env python3
import itertools

class Gsm:
    def __init__(self,n,m,relations):
        self.n = n
        self.m = m
        self.relations = relations

    def __str__(self):
        __repr__(self)

    def __repr__(self):
        print("<n :%d,m:%d> \n %s" % (g.n,g.m,g.relations))

    @staticmethod
    def read():
        n,m = map(int, input().split())
        relations = [list(map(int, input().split())) for i in range(m) ]
        return Gsm(n,m,relations)

class Graph:
    """Represents an undirected graph"""
    def __init__(self,n,m,relations):
        self.num_vertices = n
        self.num_edges = m
        self.edges = [[] for i in range(0,self.num_vertices)]

        for [a,b] in relations:
            self.edges[a-1].append(b-1)
            self.edges[b-1].append(a-1)

    def neighbours(self,idx):
        return self.edges[idx]

    def __repr__(self):
        return "n:%d, edges:<%s>"%(self.num_vertices,self.edges)

    def __str__(self):
        return self.__repr__()


class Clause:
    """ Represent a clause usable by sat solver """

    def __init__(self,compliemnt, vertex,color):
        self.compliemnt  = compliemnt
        self.vertex = vertex
        self.color = color

    def __repr__(self):
        return "<%s,%d,%d>" %(self.compliemnt,self.vertex,self.color)
    def __str__(self):
        return __repr__(self)

    @staticmethod
    def vertex_clauses(graph,num_colors):
        """Creates a per-vertex clause list such that every vertex will be
assigned exactly one color."""
        clauses = []
        for vertex_idx in range(0,graph.num_vertices):
            vertex_clauses = []

            # every vertex_idx must have a color
            vertex_clauses.append([Clause(False,vertex_idx, c) for c in range(0,num_colors)])

            # A vertex cannot have more than one color: Penalize  [not(x_ic1) + not(x_ic2)]
            for (c_1,c_2) in itertools.combinations(range(num_colors),2):
                vertex_clauses.append([Clause(True,vertex_idx,c_1) ,
                               Clause(True,vertex_idx,c_2)])

            clauses.append(vertex_clauses)

        # flatten all vertex constraints into single level
        clauses = [inner_clause for outer in clauses for inner_clause in outer]
        return clauses
    
    @staticmethod
    def edge_clauses(graph,num_colors):
        """Create edge clauses which enforce the fact that neighbours cannot have the same color"""
        clauses = []
        for c in range(0,num_colors):
            for vertex_idx in range(0,graph.num_vertices):
                for neightbour  in graph.neighbours(vertex_idx):
                    clauses.append([Clause(True, vertex_idx, c),
                                   Clause(True, neightbour, c)])

        # flatten it again     
        clauses = [inner_clause for outer in clauses for inner_clause in outer]
        return clauses


    
def simple_test():
    print("===Start Simple Test===")
    g = Gsm(3,3,[[1,2],[2,3],[1,3]])
    graph  = Graph(g.n,g.n,g.relations)
    clauses = []
    clauses.append(Clause.vertex_clauses(graph,3))
    clauses.append(Clause.edge_clauses(graph,3))
    print(clauses)
    print("===End Simple Test===")
    return graph


if __name__ == "__main__":
    g = Gsm.read()

simple_test()
