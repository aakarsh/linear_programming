#!/usr/bin/env python3

import os
import itertools

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
    """Represents an undirected graph"""
    
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

    def constraints_vertex_appears_once(self):
        pass

    def constraints_vertices_appear_once(self):
        pass


class ClauseVariable:
    """ Represent a clause usable by sat solver."""
    label_encodings  = []
    encoint_positions = {}
    
    def __init__(self,compliment, vertex,color):
        self.compliment  = compliment
        self.vertex = vertex
        self.color = color
    
    def __repr__(self):
        return "<%s,%d,%d>" % (self.compliment,self.vertex,self.color)
    
    def __str__(self):
        return self.__repr__()

    @staticmethod
    def init_encoding_labels(clauses):
        encode = ClauseVariable.minisat_encode

        # create unique list of encoded variables and give them a position
        ClauseVariable.label_encodings = list(set([abs(encode(clause_variable)) for clause in clauses for clause_variable in clause]))
        ClauseVariable.label_encodings.sort()

        # Convert from encoding to positional value
        ClauseVariable.encoding_positions ={}

        for i in range(len(ClauseVariable.label_encodings)):
            enc = ClauseVariable.label_encodings[i]
            ClauseVariable.encoding_positions[enc] = i
    
    @staticmethod
    def minisat_encode(clause):
        """ Creaes a mapping into a clause variable from """
        # TODO: assumes number of colors < 10
        retval = (10*(clause.vertex + 1))+ (clause.color + 1)
        if clause.compliment:
            retval= -1*retval            
        return retval
    
    @staticmethod
    def minisat_encode_label(clause):
        """ Assuming label encodings were setup for all clauses first """
        mini_encoding = ClauseVariable.minisat_encode(clause)        
        positional = ClauseVariable.encoding_positions[abs(mini_encoding)]
        positional += 1 # avoid zeros
        if clause.compliment:
            positional *= -1
        return positional
    
    @staticmethod
    def minisat_decode(clause_str):
        """Decodes a minisat output instance back into a clause variable"""
        int_value = int(clause_str)
        compliment = (int_value < 0)
        int_value = abs(int_value)
        color  = (int_value % 10) -1
        vertex = (int_value - 10 - color)/10
        return ClauseVariable(compliment,vertex,color)

    @staticmethod
    def minisat_decode_label(label_str):
        label_int = int(label_str)
        compliment = 1 
        if label_int < 0:
            compliment = -1
        label_value = abs(label_int)
        label_value = label_value-1  # back to zero index
        minisat_encoding = ClauseVariable.label_encodings[label_value]
        return ClauseVariable.minisat_decode("%d"%(compliment*minisat_encoding))
        
    @staticmethod
    def print_clauses(num_variables,clauses):
        """Output format is C V : that is number of clauses followed
by the number of variables.  Following this we lines per clause ending
with 0. Negations represent a variable complimented.
        """
        ClauseVariable.init_encoding_labels(clauses)
        num_variables = len(ClauseVariable.label_encodings)
        num_clauses = len(clauses)
        print("%3d %3d" %(num_clauses,num_variables))
        for clause in clauses:
            encode = ClauseVariable.minisat_encode_label
            s=""
            for clause_variable in clause:
                s += " %3d" % encode(clause_variable)
            print("%s 0"%s)


class MinisatRunner:
    temp_in =  "/tmp/minisat.in"
    temp_out = "/tmp/minisat.out"

    def __init__(self,num_variables,clauses):
        self.num_variables = num_variables
        self.num_clauses = len(clauses)
        self.clauses = clauses

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
                decode = ClauseVariable.minisat_decode_label
                self.variables = [decode(v) for v in  map(int,in_file.readline().split(" ")) if v != 0]
            else:
                self.satisfied = False
                self.variables = []
            return self.variables
        finally:
            in_file.close()

    def write_minisat(self):
        "Something something."
        ClauseVariable.init_encoding_labels(self.clauses)
        num_variables = len(ClauseVariable.label_encodings) #self.num_variables
        num_clauses = self.num_clauses
        clauses = self.clauses
        outfile = MinisatRunner.temp_in
        out = open(outfile,"w")        
        try:
            out.write("p cnf %3d %3d\n" %( num_variables,num_clauses))
            for clause in clauses:
                for clause_variable in clause:
                    out.write(" %3d"%ClauseVariable.minisat_encode_label(clause_variable));
                out.write(" 0\n")
        finally:
            out.close()

def test():
    ap = ApartementProblem(5,4,[[1,2],[2,3],[3,5],[4,5]])
    g = Graph(ap.n,ap.m,ap.relations)
    clauses = []
    
    

if __name__ == "__main__":
    ap = ApartementProblem.read()
    g = Graph(ap.n,ap.m,ap.relations)
