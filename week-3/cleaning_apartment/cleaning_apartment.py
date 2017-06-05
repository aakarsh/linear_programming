#!/usr/bin/env python3
import math
import os
import itertools

debug = False


class ApartementProblem:
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
        return ApartementProblem(n,m,relations)

    @staticmethod
    def read_file(file_name):
        input_file = None
        try:
            input_file = open(file_name,"r")
            n,m = map(int,input_file.readline().split())
            # some problems here
            relations = [list(map(int, line.split())) for line in input_file ]
            print (relations)
            return ApartementProblem(n,m,relations)
        finally:
            if input_file: input_file.close()


class Graph:
    """Represents an undirected graph."""

    def __init__(self,n,m,relations):
        self.num_vertices = n
        self.num_edges = m
        self.color = [0] * self.num_vertices
        self.edges = [[] for i in range(0,self.num_vertices)]
        for [a,b] in relations:
            self.edges[a-1].append(b-1)
            self.edges[b-1].append(a-1)

    def neighbours(self,idx):
        return self.edges[idx]

    def __repr__(self):
        return "n:%d, edges:<%s>" % (self.num_vertices,self.edges)

    def __str__(self):
        return self.__repr__()

class HamiltonianPath:

    def __init__(self,graph):
        self.graph = graph

    def vertex_at_least_once(self,vertex):
        """Ensure that a vertex will appear in at least one of the
        possible positions """
        clauses = []
        for position in range(0,self.graph.num_vertices):
            clauses.append(ClauseVariable(False,position,vertex))
        return clauses


    def vertices_at_least_once(self):
        """Iterate through all vertices creating clausese such that
        variable will appear at aleast one position on the hamiltonian
        path"""
        clauses = []
        for vertex in range(0,self.graph.num_vertices):
            clauses.append(self.vertex_at_least_once(vertex))
        return clauses

    def vertex_at_most_once(self,vertex):
        """Ensure that a vertex will appear at most once at this is
        done by considering all combinations of vertices and ensuring
        that vertex can only ever appear at one position for each pair
        of positions."""
        clauses = []
        for (p1,p2) in itertools.combinations(range(0,self.graph.num_vertices),2):
            clause = [ ClauseVariable(True,vertex,p1),
                       ClauseVariable(True,vertex,p2)]
            clauses.append(clause)
        return clauses

    def vertices_at_most_once(self):
        clauses = []
        for v in range(0,self.graph.num_vertices):
           clauses.extend(self.vertex_at_most_once(v))
        return clauses

    def no_empty_positions(self):
        """Ensure that every position is occupied by at least one vertex """
        clauses = []

        for position in range(0,self.graph.num_vertices):
            clause = []
            for vertex in range(0,self.graph.num_vertices):
                clause.append(ClauseVariable(False,vertex,position))
            clauses.append(clause)
        return clauses

    def vertex_no_simultaneos(self):
        """ Ensure that two vertices can simultaneosly occupy the same position """
        clauses = []
        for position in range(0,self.graph.num_vertices):
            for (v1,v2) in itertools.combinations(range(0,self.graph.num_vertices),2):
                clauses.append([ClauseVariable(True,v1,position),
                                ClauseVariable(True,v2,position)])
        return clauses

    def no_non_adjacent_vertices(self):
        """ Ensure that non adjacent vertices """
        clauses = []
        for v in range(0,self.graph.num_vertices):
            non_neighbours = sorted(list(set(range(0,self.graph.num_vertices))
                                         - set([v])
                                         - set(self.graph.edges[v])))
            for nv in non_neighbours:
               for position in range(0,self.graph.num_vertices-1):
                   clause = [ ClauseVariable(True,v,position),
                              ClauseVariable(True,nv,position+1)]
                   clauses.append(clause)
        return clauses


class ClauseVariable:
    """ Represent a clause usable by sat solver."""
    label_encodings  = []
    encoint_positions = {}
    max_position = 0
    max_vertex = 0
    
    def __init__(self,compliment, vertex,position):
        self.compliment  = compliment
        self.vertex = vertex
        self.position = position
        #
        if ClauseVariable.max_vertex < vertex:
            ClauseVariable.max_vertex = vertex
        if ClauseVariable.max_position < position:
            ClauseVariable.max_position = position


    def __repr__(self):
        return "<%s,%d,%d>" % (self.compliment,self.vertex,self.position)

    def __str__(self):
        return self.__repr__()

    @staticmethod
    def encoding_factor():
        return int(math.pow(10,math.ceil(math.log(ClauseVariable.max_position+1,10))))

    def minisat_encode(self):
        """ Creaes a mapping into a clause variable from """
        factor = ClauseVariable.encoding_factor()
        
        retval = (factor*(self.vertex + 1))+ (self.position + 1)
        if self.compliment:
            retval= -1*retval
        if debug: print("Encoding [factor %d] (vertex %d, position %d) -> %d " %(factor,self.vertex,self.position,retval))
        return retval

    @staticmethod
    def minisat_decode(clause_str):
        """Decodes a minisat output instance back into a clause variable"""
        factor = ClauseVariable.encoding_factor()
        int_value = int(clause_str)
        compliment = (int_value < 0)
        int_value = abs(int_value)
        position  = (int_value % factor) -1
        vertex = math.ceil(int_value/factor)-1
        return ClauseVariable(compliment,vertex,position)

class MinisatRunner:

    temp_in =  "/tmp/minisat.in"
    temp_out = "/tmp/minisat.out"

    def __init__(self,clauses):
        self.num_clauses = len(clauses)
        self.clauses = clauses
        self.label_encodings  = []
        self.encoding_positions = {}
        self.init_encoding_labels(clauses)
        self.num_variables = len(self.label_encodings)

    def init_encoding_labels(self,clauses):        
        # create unique list of encoded variables and give them a position
        self.label_encodings = list(set([abs(clause_variable.minisat_encode())
                                         for clause in clauses for clause_variable in clause]))
        self.label_encodings.sort()
        # Convert from encoding to positional value
        self.encoding_positions ={}
        for i in range(len(self.label_encodings)):
            enc = self.label_encodings[i]
            self.encoding_positions[enc] = i
            if debug: print("mapping %d -> %d " % (enc,i ))

    def minisat_encode_label(self,clause):
        """ Assuming label encodings were setup for all clauses first """
        mini_encoding = clause.minisat_encode()
        positional = self.encoding_positions[abs(mini_encoding)]
        positional += 1
        if clause.compliment:
            positional *= -1
        return positional

    def minisat_decode_label(self,label_str):
        label_int = int(label_str)
        compliment = 1
        if label_int < 0:
            compliment = -1
        label_value = abs(label_int)
        label_value = label_value-1  # back to zero index
        minisat_encoding = self.label_encodings[label_value]
        return ClauseVariable.minisat_decode("%d"%(compliment*minisat_encoding))

    def check_sat(self):
        "Run minisat and parse output as variables"
        self.write_minisat()
        os.system("minisat %s %s  >/dev/null 2>&1" % (MinisatRunner.temp_in,MinisatRunner.temp_out))
        self.read_minisat()
        return self.variables

    def read_minisat(self):
        "Parse out the resuling clause variables and satisfibilty"
        in_file = open(MinisatRunner.temp_out,"r")
        try:
            sat = in_file.readline()
            if sat.strip() == "SAT":
                self.satisfied = True
                decode = self.minisat_decode_label
                self.variables = [decode(v) for v in  map(int,in_file.readline().split(" ")) if v != 0]
            else:
                self.satisfied = False
                self.variables = []
            return self.variables
        finally:
            in_file.close()

    def write_minisat(self):
        """Write out minisait in format of minisat command runner """
        num_variables = len(self.label_encodings)
        num_clauses = self.num_clauses
        clauses = self.clauses
        outfile = MinisatRunner.temp_in
        out = open(outfile,"w")
        try:
            out.write("p cnf %3d %3d\n" % (num_variables,num_clauses))
            for clause in clauses:
                for clause_variable in clause:
                    out.write(" %3d" % self.minisat_encode_label(clause_variable));
                out.write(" 0\n")
        finally:
            out.close()

    def print_clauses(self):
        """Output format is C V : that is number of clauses followed
        by the number of variables.  Following this we lines per clause ending
        with 0. Negations represent a variable complimented.
        """
        num_variables = len(self.label_encodings)
        num_clauses = self.num_clauses
        clauses = self.clauses
        print("%3d %3d" %(num_clauses,num_variables))
        for clause in clauses:
            s=""
            for clause_variable in clause:
                s += " %3d" % self.minisat_encode_label(clause_variable)
            print("%s 0"%s)

def test_file(in_file):
    ap = ApartementProblem.read_file(in_file)
    test_common(ap)

def test_simple():
    ap = ApartementProblem(5,4,[[1,2],[2,3],[3,5],[4,5]])
    test_common(ap)
    
def test_common(ap):
    
    g = Graph(ap.n,ap.m,ap.relations)
    hp = HamiltonianPath(g)

    clauses = []
    clauses.extend(hp.vertices_at_least_once())
    clauses.extend(hp.vertices_at_most_once())
    clauses.extend(hp.no_empty_positions())
    clauses.extend(hp.vertex_no_simultaneos())
    clauses.extend(hp.no_non_adjacent_vertices())
    
    mr = MinisatRunner(clauses)
    #mr.print_clauses()
    variables = mr.check_sat()

    if len(variables) > 0:
        true_variables = [ var for var in variables if not var.compliment]
        def sort_by_position(v1):
            return v1.position        
        true_variables.sort(key=sort_by_position)
        for v in true_variables:
            print(v.vertex,end=' ')
        print("")
    else:
        print("No Hamiltonain Path Found!")


if __name__ == "__main__":
    ap = ApartementProblem.read()
    g = Graph(ap.n,ap.m,ap.relations)
    hp = HamiltonianPath(g)

    clauses = []
    clauses.extend(hp.vertices_at_least_once())
    clauses.extend(hp.vertices_at_most_once())
    clauses.extend(hp.no_empty_positions())
    clauses.extend(hp.vertex_no_simultaneos())
    clauses.extend(hp.no_non_adjacent_vertices())

    # Print clauses in appropriate order
    mr = MinisatRunner(clauses)
    mr.print_clauses();
