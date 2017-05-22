#!/usr/bin/env python3

debug = False

class Node:
    """ Simple node used to hold meta-data during graph traversals """
    def __init__(self,number):
        self.neighbours =[]
        self.data = []
        self.component = -1
        self.visited = False
        self.number = number

    def add_edge(self,neighbour):
        self.neighbours.append(neighbour)

    def __str__(self):
        return "[%d : ,visited :%s, component: %d, data: %s]" % \
               (self.number,self.visited,self.component,self.data)

class Graph:

    def __init__(self,nodes):
        self.nodes = nodes

    def clear_visited(self):
        for node in self.nodes:
            node.visited = False

    def edges(self):
        edges = {}

        for node in self.nodes:
            edges[node.number] = []

        for node in self.nodes:
            edges[node.number].extend(node.neighbours)

        return edges

    def reverse(self):
        """ Iterate through a graph building up a reverse graph for it. """
        self.reverse_edges = {}
        for node in self.nodes:
            self.reverse_edges[node.number] = []

        for node in self.nodes:
            for neighbour_idx in node.neighbours:
                self.reverse_edges[neighbour_idx].append(node.number)

        if debug:
            print(self.edges())
            print(self.reverse_edges)

        for (number,edges) in self.reverse_edges.items():
            self.nodes[number].neighbours = edges


    def dfs_post_order(self):
        """ Computes a post ordering for a graph represented by its nodes """
        nodes_finish_order = []
        self.dfs_visit_graph\
        (post_visit = lambda node: nodes_finish_order.append(node))
        return nodes_finish_order

    def dfs_visit_graph(self, traverse_order=None,post_dfs=None,post_visit=None,pre_visit=None):
        """DFS visit the nodes of a graph in the traveral order"""
        self.clear_visited()

        # May not be reasonable, but then who is in 2017
        import resource, sys
        resource.setrlimit(resource.RLIMIT_STACK, (2**29,-1))
        sys.setrecursionlimit(10**6)

        traverse_order = traverse_order if  traverse_order else self.nodes

        for node in traverse_order:
            if not node.visited:
                self.dfs_visit(node,post_visit=post_visit,pre_visit =pre_visit)
                if post_dfs:
                    post_dfs(node)

        self.clear_visited()


    def dfs_visit(self,node,post_visit=None,pre_visit=None):
        """ Perform depth-first visit starting with node. With optional callbacks. """
        node.visited = 'visiting'
        if pre_visit : pre_visit(node)

        for neighbour_idx  in node.neighbours:
            neighbour = self.nodes[neighbour_idx]
            if not neighbour.visited:
                self.dfs_visit(neighbour,post_visit=post_visit,pre_visit=pre_visit)

        node.visited = 'visited'
        if post_visit : post_visit(node)



    def assign_components(self):
        """ Accepts a graph consisting of nodes and assigns the nodes
        components."""

        self.component_number  = 0
        # Visit a reversed-version of graph in post order.
        self.reverse()

        def node_assign_component(node):
            node.component = self.component_number
        def increment_component(node):
            self.component_number += 1
            
        # perform traversal on the reverse graph to assign
        # nodes compoents,
        self.dfs_visit_graph(traverse_order = self.dfs_post_order(),
                             post_visit     = node_assign_component,
                             post_dfs       = increment_component)

        # return graph back to orginal state
        self.reverse()
        self.num_components = self.component_number



    def build_component_graph(self):
        """ Builds a component graph summarizing the graph """
        self.assign_components();
        component_nodes = [ Node(i) for i in range(0,self.num_components) ]

        # set the data of component nodes to be the node
        for node in self.nodes:
            component_nodes[node.component].data.append(node)

        # Iterate through all the edges and if not present add it
        # the component graph.
        for node in self.nodes:
            component_nodes[node.component].neighbours.extend(\
                list(set([self.nodes[n].component for n in node.neighbours])))
        

        return Graph(component_nodes)

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
        # cg is the self's constraint graph
        self.nodes = [ Node(i) for i in range(0,2*num_variables) ]
        self.add_constraints(self.nodes,self.clauses)
        self.cg = Graph(self.nodes)

    def node_idx(self,literal):
        """ Compute the index into nodes list for literal """
        v = 2*abs(literal)
        if literal < 0:
            return v-2
        return v-1

    def literal(self, node_idx):
        """ Get back the literal value from  """
        retval = None;
        if node_idx %2  == 0: # negative literal
            retval = -(node_idx + 2)
        else:
            retval = node_idx + 1

        return int(retval/2) # should never be fractional


    def add_constraints(self,nodes,clauses):
        """ Use clauses to construct graph over nodes by assigning
        neighbours"""

        node_idx = self.node_idx
        for clause in clauses:
            l1,l2 = clause
            nodes[node_idx(-l1)].add_edge(node_idx(l2))
            nodes[node_idx(-l2)].add_edge(node_idx(l1))


    def contains_contradiction(self):
        """ Checks if node and its complement lie in the same """
        for node in self.cg.nodes:            
            node_literal = self.literal(node.number)
            compliment_literal = node_literal * -1
            compliment_idx = self.node_idx(compliment_literal)
            compliment = self.cg.nodes[compliment_idx]
            #print("%d:(%d,%d)"% (node.number,node.component,compliment.component))
            if node.component == compliment.component:
                return True
            
        return False
            
            
    def find_sat(self):
        """ Check the satisfiability """
        if debug:
            print("Clauses:%s" % self.clauses)
            print("Node Post Order: %s" % self.cg.dfs_post_order())
        sat = [None for i in range(self.num_variables)]

        self.cg.assign_components()
        # If a literal and its complement are in the same
        # component then we have a contradiciton the graph is
        # unsatisfiable.        
        if self.contains_contradiction():
            return None 
        component_graph = self.cg.build_component_graph()        
        component_order = component_graph.dfs_post_order()
        component_order.reverse()

        for component in component_order:
            for node in component.data:
                literal = self.literal(node.number)
                literal_idx = int(abs(literal) - 1)
                if  sat[literal_idx] is None:
                    if debug: print("literal_idx : %d " % literal_idx)
                    sat[literal_idx] = 0 if (literal < 0) else 1
        return sat

def simple_test():
    print("start simple_test")
    ts = TwoSatSolver([[1,-3],[-1,2],[-2,-3]],3)
    print(ts.find_sat())
    ts = TwoSatSolver([[1,1],[-1,-1]],2)
    print(ts.find_sat())
    
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

    result = TwoSatSolver(clauses,num_clauses).find_sat()

    if not result:
        print("UNSATISFIABLE")
    else:
        print("SATISFIABLE");
        print(" ".join(str(-i-1 if result[i] else i+1) for i in range(n)))


if __name__ == "__main__":
    main()
