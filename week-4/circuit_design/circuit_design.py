#!/usr/bin/env python3

debug = True

class Node:
    """ Simple node used to hold meta-data during graph traversals """
    def __init__(self,number):
        self.neighbours =[]
        self.data = None
        self.component = None
        self.visited = None

class TwoSatSolver:    
    """ Solver for boolean satisfiablity problem

    Works by building a constrait graph from boolean clauses and using
    reverse topological ordering of the strongly connected components
    to compute an assigment for the variables.
    """
    def __init__(self,clauses,num_variables):
        self.clauses = clauses
        self.num_variables = num_variables
        self.num_clauses = len(clauses)        
        self.nodes = list(map(lambda i:Node(i),range(0,2*num_variables)))

    def node_idx(self,literal):
        """ Compute the index into nodes list for literal """
        v = 2*abs(literal)
        if literal < 0:
            return v-2
        return v-1

    
    def build_constraing_graph(clauses,num_variables):
        """  Use clauses to construct graph over nodes by assigning neighbours """
        
        for clause in clauses:
            l1,l2 = clause
            # for each literal add edges:
            #      -l1 -> l2
            #      -l2 -> l1
            # TODO : Build the constraint graph here.
            n1,n2 = self.node_idx(l1),self.node_idx(l2)
            self.nodes[
        pass
        
    def is_satisfiable(self):
        """ Check the satisfiability """
        print("Clauses:%s" % self.clauses)


def simple_test():
    print("Start simple_test")
    v = TwoSatSolver([[1,-1],[1,1]],2)
    v.is_satisfiable()


# This solution tries all possible 2^n variable assignments.
# It is too slow to pass the problem.
# Implement a more efficient algorithm here.
def isSatisfiableBruteForce(clauses, num_variables):
    for mask in range(1<<n):
        result = [ (mask >> i) & 1 for i in range(n) ]
        formulaIsSatisfied = True
        for clause in clauses:
            clauseIsSatisfied = False
            if result[abs(clause[0]) - 1] == (clause[0] < 0):
                clauseIsSatisfied = True
            if result[abs(clause[1]) - 1] == (clause[1] < 0):
                clauseIsSatisfied = True
            if not clauseIsSatisfied:
                formulaIsSatisfied = False
                break
        if formulaIsSatisfied:
            return result
    return None


def main():
    num_clauses, num_variables = map(int, input().split())
    clauses = [ list(map(int, input().split())) for i in range(num_clauses) ]

    
    result = TwoSatSolver().is_satisfiable(clauses,num_variables)
    if not result:
        print("UNSATISFIABLE")
    else:
        print("SATISFIABLE");
        print(" ".join(str(-i-1 if result[i] else i+1) for i in range(n)))


if __name__ == "__main__":
    main()
