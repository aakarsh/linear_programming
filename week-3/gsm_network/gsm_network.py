#!/usr/bin/env python3

import os
import itertools

# Assert: 1 < NumClauses < 5000
# Assert: 1 < NumVariables< 3000 
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

    @staticmethod
    def read_file(file_name):
        input_file = None
        try:            
            input_file = open(file_name,"r")
            n,m = map(int,input_file.readline().split())
            relations = [list(map(int, line.split())) for line in input_file ]
            print (relations)
            return Gsm(n,m,relations)
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

    def color_by_clauses(self,clauses):
        """ Color a graph based on the result of running minisat."""
        for clause in clauses:
            if not clause.compliment:
                self.color[int(clause.vertex)] = clause.color

    def check_valid_colors(self):
        """Check the assertion that neighbouring vertices do not share colors"""
        for vertex_idx in range(0,self.num_vertices):
            for neighbour in self.edges[vertex_idx]:
                try:
                    assert(self.color[vertex_idx] != self.color[neighbour])
                except AssertionError:
                    print("Vertex %d Color :%d  same color as Vertex: %d Color: %d  "%
                          (vertex_idx,self.color[vertex_idx],
                           neighbour,self.color[neighbour]))
                          
                
    def neighbours(self,idx):
        return self.edges[idx]

    def __repr__(self):
        return "n:%d, edges:<%s>"%(self.num_vertices,self.edges)

    def __str__(self):
        return self.__repr__()


class ClauseVariable:
    """ Represent a clause usable by sat solver."""
    label_encodings  = []
    encoint_positions = {}
    
    def __init__(self,compliment, vertex,color):
        self.compliment  = compliment
        self.vertex = vertex
        self.color = color
    
    def __repr__(self):
        return "<%s,%d,%d>" %(self.compliment,self.vertex,self.color)
    
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
            
        #print("Encoding Postions %s "%ClauseVariable.encoding_positions)
        #print("Encoding Labels %s "%ClauseVariable.label_encodings)
    
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
        """Output format is C V : that is number of clauses followed by the
number of variables.  Following this we lines per clause ending with
0. Negations represent a variable complimented.
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
    

    @staticmethod
    def vertex_clauses(graph,num_colors):
        """Creates a per-vertex clause list such that every vertex will be
assigned exactly one color"""
        clauses = []
        for vertex_idx in range(0,graph.num_vertices):
            vertex_clauses = []

            # every vertex_idx must have a color
            vertex_clauses.append([ClauseVariable(False,vertex_idx, c) for c in range(0,num_colors)])

            # A vertex cannot have more than one color: Penalize  [not(x_ic1) + not(x_ic2)]
            for (c_1,c_2) in itertools.combinations(range(num_colors),2):
                vertex_clauses.append([ClauseVariable(True,vertex_idx,c_1) ,
                               ClauseVariable(True,vertex_idx,c_2)])
            clauses.append(vertex_clauses)
        # flatten all vertex constraints into single level
        clauses = [inner_clause for outer in clauses for inner_clause in outer]
        return clauses
    
    @staticmethod
    def edge_clauses(graph,num_colors):
        """Create edge clauses which enforce the fact that neighbours cannot have the same color."""        
        clauses = []
        for c in range(0,num_colors):
            for vertex_idx in range(0,graph.num_vertices):
                for neightbour in graph.neighbours(vertex_idx):                    
                    clauses.append([ClauseVariable(True, vertex_idx, c),
                                    ClauseVariable(True, neightbour, c)])
        # flatten it again     
        #clauses = [inner_clause for outer in clauses for inner_clause in outer]
        return clauses
            


class MinisatRunner:

    temp_in =  "/tmp/minisat.in"
    temp_out = "/tmp/minisat.out"
    
    def __init__(self,num_variables,clauses):
        self.num_variables = num_variables
        self.num_clauses = len(clauses)
        self.clauses = clauses

    def check_sat(self):
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
        ClauseVariable.init_encoding_labels(self.clauses)
        num_variables = len(ClauseVariable.label_encodings) #self.num_variables
        num_clauses = self.num_clauses
        clauses = self.clauses
        outfile = MinisatRunner.temp_in



        out = open(outfile,"w");
        try:
            out.write("p cnf %3d %3d\n" %( num_variables,num_clauses))
            for clause in clauses:
                for clause_variable in clause:
                    out.write(" %3d"%ClauseVariable.minisat_encode_label(clause_variable));
                out.write(" 0\n")
        finally:
            out.close()        
        
def simple_test(test_file="./tests/02"):
    print("===Start Simple Test===")
    g = Gsm.read_file(test_file)
    num_colors = 3
    
    graph  = Graph(g.n,g.n,g.relations)
    clauses = []
    clauses.extend(ClauseVariable.vertex_clauses(graph,num_colors))
    clauses.extend(ClauseVariable.edge_clauses(graph,num_colors))

    runner = MinisatRunner(10*graph.num_vertices+num_colors,clauses)
    result = runner.check_sat()
    
    if result:
        graph.color_by_clauses(result)
        graph.check_valid_colors()
    else:
        print("No valid %d coloring exists !" % num_colors)

    print("===Finish Simple Test===")
    return graph


if __name__ == "__main__":    

    gsm = Gsm.read()
    num_colors = 3
    graph  = Graph(gsm.n,gsm.m,gsm.relations)

    clauses = []
    clauses.extend(ClauseVariable.vertex_clauses(graph,num_colors))
    clauses.extend(ClauseVariable.edge_clauses(graph,num_colors))

    #+1 for luck, ok i have no idea how to procede, i guess need to
    # generate lots of three colorable graphs and check

    ClauseVariable.print_clauses(10*graph.num_vertices + num_colors + 1 , clauses)    
