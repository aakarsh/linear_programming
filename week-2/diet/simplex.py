#!/usr/bin/env python

import glob
import os
import sys
import unittest
import itertools

debug = False
global_tolerance = 1e-09

class FPHelper:

    @staticmethod
    def ispositive(x):
        return x and (not FPHelper.iszero(x)) and (x > 0.0)
    
    @staticmethod
    def isclose(a, b, rel_tol=global_tolerance, abs_tol=global_tolerance):
        return abs(a-b) <= max(rel_tol * max(abs(a), abs(b)), abs_tol)
    
    @staticmethod
    def iszero(a,rel_tol=global_tolerance, abs_tol=global_tolerance):
        return FPHelper.isclose(a,0.0,rel_tol,abs_tol)

class UnboundedError(Exception):
    "Raised when the solution for given equations is unbounded "
    pass

class InfeasibleError(Exception):
    "Raised when the solution for given equations is infeasible(has no-solution)."
    pass

class MatrixHelper:

    @staticmethod
    def set_value_all_rows(matrix,row_idxs, value):
        for row in row_idxs:
            matrix[row] = [value] * len(matrix[row])

    @staticmethod
    def set_column_value(matrix,col,value):
        for row in range(len(matrix)):
            matrix[row][col]= value

    @staticmethod
    def set_value_all_columns(matrix,col_idxs, value):
        for row in range(len(matrix)):
            for col in col_idxs:
                matrix[row][col] = value

    @staticmethod
    def set_value_all_rows_columns(matrix,value,**kwargs):
        if "columns" in kwargs:
            MatrixHelper.set_value_all_columns(matrix,kwargs["columns"],value)
        if "rows" in kwargs:
            MatrixHelper.set_value_all_rows(matrix,kwargs["rows"],value)

    @staticmethod
    def copy_matrix(m1,m2):
        for r in range(len(m2)):
            for c in range(len(m2[r])):
                m1[r][c] = m2[r][c]

    @staticmethod
    def pop_column(matrix):
        for row in matrix: row.pop()

    @staticmethod
    def pop_row(matrix):
        matrix.pop()

class ListHelper:

    @staticmethod
    def zip_set(l,member_set,by = lambda x: True):
        return [(i,l[i]) for i in member_set if by(l[i])]

    @staticmethod
    def find_first_idx(l, in_set = None, by = lambda x: True):
        "Find first element of list set in by predicate "
        if not in_set:
            in_set = set(range(len(l)))
        for (idx, value) in ListHelper.zip_set(l,in_set,by):
            return idx
        return None

    @staticmethod
    def contains(ls , predicate = lambda x: x):
        for value in ls:
            if predicate(value): return True
        return False
    
    @staticmethod
    def find_first(l, in_set = None, by = lambda x: True):
        "Find first element of list set in by predicate "
        for (idx, value) in ListHelper.zip_set(l,in_set,by):
            return value
        return None

    @staticmethod
    def set_values(l, value,idxs ):
        for idx in idxs: l[idx] = value

    @staticmethod
    def min_index(l,max=float('inf')):
        "Return a pair of (value,index) of elment with minimum index"
        zl = zip(l,range(len(l)))
        zp = min(zl, key = lambda z: z[0] if z[0] else max)
        return zp

class PrettyPrinters:

    @staticmethod
    def format_table(matrix):
        "Format matrix as a table"
        output =""
        for row in matrix:
            first_col = True
            for col in row:
                if first_col:
                    output += "| "
                    first_col=False
                if not col is None:
                    output += "%f"% float(col)
                else:
                    output +="%5s"%"None"
                output +=" | "
            output += "\n"
        return output

# singleton helpers
list_helper  =  ListHelper()
pretty_printers = PrettyPrinters()

class SlackForm:
    "Represents simplex in slack form ..."

    class Constraint:
        "Helper class to deal with constraints..."

        def __init__(self,constant,coefficients):
            self.constant = constant
            self.coefficients = coefficients

        def store(self,idx,slackform):
            "Store constraint back into slack form"
            slackform.b[idx] = self.constant
            slackform.A[idx] = self.coefficients

        def __repr__(self):
            return " (%s) %s" % (self.constant, self.coefficients)

        @staticmethod
        def substitute_objective(simplex,entering_constraint,entering_idx):
            constraint = simplex.to_objective_constraint()
            return constraint.substitute_constraint(entering_idx,entering_constraint)

        def substitute_constraint(self,entering_idx,entering_constraint):
            constraint = self
            if debug:
                print("subs: %-20s @ [%3d] => %-20s " % (entering_constraint, entering_idx, constraint))

            current_coefficients  = constraint.coefficients
            current_constant      = constraint.constant

            return_coefficients = [None] * len(current_coefficients)
            return_constant     =  None

            variable_coefficient = current_coefficients[entering_idx]

            # TODO maybe not correct return the entering constraints
            if not variable_coefficient or FPHelper.iszero(variable_coefficient):
                retval = constraint 
                if debug: print("subs => : %s " % (retval))
                return retval

            entering_constant = entering_constraint.constant
            entering_coeffs   = entering_constraint.coefficients

            if not current_constant:
                current_constant = 0.0

            return_constant = current_constant + (variable_coefficient * entering_constant)

            for var_idx in range(len(current_coefficients)):
                if var_idx == entering_idx:
                    continue

                current_coefficient = current_coefficients[var_idx]
                entering_coeff      =  entering_coeffs[var_idx]  if entering_coeffs[var_idx]  else 0

                if current_coefficient:
                    return_coefficients[var_idx] = current_coefficient + ( variable_coefficient * entering_coeff )
                else: # no current coefficent use subsitituded value
                    return_coefficients[var_idx] = variable_coefficient * entering_coeff

            retval = SlackForm.Constraint(return_constant,return_coefficients)
            
            if debug: print("subs => : %s " % (retval))

            return retval

    def replace(self,**kwargs):
        if "A" in kwargs:
            self.A = kwargs["A"]
        if "b" in kwargs:
            self.b = kwargs["b"]
        if "c" in kwargs:
            self.c = kwargs["c"]
        if "v" in kwargs:
            self.v = kwargs["v"]
        if "n" in kwargs:
            self.n = kwargs["n"]
        if "m" in kwargs:
             self.m = kwargs["m"]


    def __init__(self,**kwargs):
        # expand
        if ("simplex" in kwargs) and kwargs["simplex"]:
            simplex = kwargs["simplex"]
            n,m = (simplex.n,simplex.m)
            A = simplex.A
            b = simplex.b
            c = simplex.c
            v = simplex.v
        else:
            n,m = (kwargs["n"],kwargs["m"])
            A = kwargs["A"]
            b = kwargs["b"]
            c = kwargs["c"]
            v = kwargs["v"]

        # A represents the table of size totalxtotal
        # with None possible entreis
        nvars = n+m
        self.A = [ [None for x in range(nvars)] for y in range(nvars)]

        # We will use a numbering where
        # dependent variables will be from [x_n to x_nvars)
        # independent variables will be from [x_0 to x_n)
        # x_nvars will be a psuedo variable used in case the initial
        # simplex is not in basic form.

        for i in range(n):
            for j in range(m):
                self.A[i][j+n] = -A[i][j]

        if debug:
            print("\nA:")
            print(pretty_printers.format_table(self.A))
            print("Input Equations:")
            print(pretty_printers.format_table(A))

        if debug:
            print("orig-b:%s"% b)
        self.b = list(map(float,b))

        # Fill rest of it with None
        self.b.extend([None]*(nvars-len(b)))

        if debug:
            print("b:%s"% self.b)

        self.c = [None] * n
        self.c.extend(map(float,c))

        if debug:
            print("orig-c:%s"% c)
            print("c:%s"% self.c)

        self.v = v
        # Original variables
        self.independent   = set(range(n,nvars))

        # Slack varaibles
        self.dependent     = set(range(0,n))

        if debug:
            print("dependent : %s, independent : %s" %
                  (self.independent,self.dependent))

        leaving_coeff,leaving_idx = ListHelper.min_index(self.b)

        if debug:
            print("leaving_coeff:%d leaving_idx: %d"
                  % (leaving_coeff,leaving_idx))


    def to_objective_constraint(self):
        "Particular equation-id from simplex wrapped  equation"
        return SlackForm.Constraint(self.v,self.c)
        
    def to_constraint(self,equation_idx):
        "Particular equation-id from simplex wrapped  equation"
        return SlackForm.Constraint(self.b[equation_idx],self.A[equation_idx])

    def store(self,idx,new_eq):
        "Store constraint back into slack form"
        self.b[idx],self.A[idx] = new_eq.constant, new_eq.coefficients

    def substitute_objective(self,entering_constraint,entering_idx):
        obj_cons = self.to_objective_constraint()
        new_obj = obj_cons.substitute_constraint(entering_idx,entering_constraint)
        if debug:
            print("subs-obj: (%s,%s) => %s " % (self.c,self.v,new_obj))
        self.v,self.c = new_obj.constant,new_obj.coefficients
        return new_obj
        
    def substitute_equation(self,equation_idx,entering_constraint,entering_idx):
        "Substititue enterint constraint into equation "
        new_eq  = self.to_constraint(equation_idx).substitute_constraint(entering_idx,entering_constraint)
        self.store(equation_idx,new_eq)

    def make_pivot_constraint(self,leaving_idx, entering_idx):
        "Construct constriant based on leaving and entering ids "

        slackform = self
        A = slackform.A
        b = slackform.b

        independent = slackform.independent
        dependent   = slackform.dependent

        nvars = len(independent) + len(dependent)

        pivot_entry = A[leaving_idx][entering_idx]
        pivot_value = abs(pivot_entry)
        pivot_sign = -1 if pivot_entry > 0 else 1
        pivot_inverse = pivot_sign * (1.0/pivot_value)

        entering_constant = b[leaving_idx] * pivot_inverse
        leaving_equation  = A[leaving_idx]

        entering_equation = [None] * nvars
        for idx in independent:
            if not idx == entering_idx and not leaving_equation[idx] is None:
                entering_equation[idx] = pivot_inverse * leaving_equation[idx]

        entering_equation[entering_idx] = None
        entering_equation[leaving_idx]  = -1 * pivot_inverse

        return SlackForm.Constraint(entering_constant,entering_equation)

    
    def pivot(self,entering_idx,leaving_idx):
        "Pivot on the entering and leaving ids"
        #
        entering_constraint = self.make_pivot_constraint(leaving_idx,entering_idx)
        self.store(entering_idx,entering_constraint)
        # 
        if debug:                
            print("(Eq:%d) => :%s" % (entering_idx,entering_constraint))
            print("\nA:\n%s" % pretty_printers.format_table(self.A))
        #
        for idx in self.dependent:
            if idx == leaving_idx: continue            
            self.substitute_equation(idx,entering_constraint,entering_idx)
            

        self.substitute_objective(entering_constraint,entering_idx)

        # move leaving_idx  from dependent   to independent set
        # move entering_idx from independent to dependent set

        if debug:
            print("dependent: %s   -  %d + %d " % (self.dependent,leaving_idx,entering_idx))
            
        self.dependent.remove(leaving_idx)
        self.dependent.add(entering_idx)
        
        if debug:
            print("dependent=> %s" % self.dependent)
                  
        if debug:
            print("independent: %s -  %d + %d" % (self.independent,entering_idx,leaving_idx))
                  
        self.independent.remove(entering_idx)
        self.independent.add(leaving_idx)
                  
        if debug:
            print("independent: %s" %(self.independent))
                  
    def objective_has_positive_coefficients(self):
        contains = ListHelper.contains
        ispositive = FPHelper.ispositive
        return contains(self.c,predicate = ispositive)


    def pick_entering_idx(self):
        find_first_idx  = ListHelper.find_first_idx
        return find_first_idx(self.c,in_set = self.independent,
                                     by     = FPHelper.ispositive)

    def pick_leaving_idx(self,entering_idx):
        if debug:
            print("pick_leaving_idx: dependent:%s entering:%d" %(self.dependent,entering_idx))
            
        slack = [None] * len(self.b)

        # TODO: Seeing non-None  values in b where it is not a depenedent

        if debug:
            print("b: %s" % self.b)
            print("c: %s" %  self.c)
            print("\nA:\n %s\n" % pretty_printers.format_table(self.A))
        
        for idx in self.dependent:
            constant = self.b[idx]
            coeff    = -1 * self.A[idx][entering_idx]
            if debug:
                print("slack[%d]=:: [%s]/[%s] " % (idx,constant,coeff))
                
            if FPHelper.ispositive(coeff):
                slack[idx]  = (constant/coeff)
                if debug:
                    print("slack[%d]=> [%f]/[%f] " % (idx,constant,coeff))
                    if slack[idx]:
                        print("%2.2f",slack[idx])
                    else: print()
                    
        if debug: print("A col[%d] %s" % (entering_idx,[self.A[idx][entering_idx] for idx in self.dependent]))
        if debug: print("b %s" % [self.b[idx] for idx in self.dependent])
        
        min_slack,slack_idx = ListHelper.min_index(slack)
        if debug:
            if min_slack:
                print("slack: %s \nmin_slack[%d] :%2.2f " % (slack,slack_idx,min_slack))
            else:
                print("min_slack is None slacks: %s",slack )
                
            print("leave: %d" % slack_idx)

        return slack_idx if min_slack else None 


    def __repr__(self):
        return "A:\n%s\nb:%s" %(pretty_printers.format_table(self.A),self.b)

    def solve(self):
        if debug:
            print("Enter SlackForm.solve():")
        cnt = 0

        while self.objective_has_positive_coefficients():
            if debug:
                print(self)
            cnt+=1
            
            if debug:
                print("pivot: %d" % cnt)
                print("%s" % pretty_printers.format_table(self.A))
                print(" Objective > %s: %s " % (self.c,self.v))
            
            entering_idx = self.pick_entering_idx()
            leaving_idx  = self.pick_leaving_idx(entering_idx)

            if (leaving_idx is None)  or  (entering_idx is None):  # unbounded
                raise UnboundedError()

            if debug:
                print("pivot:  %s >> (dep) >> %s" % (entering_idx,leaving_idx))

            self.pivot(entering_idx , leaving_idx)

        if debug:
            print("\nA:\n%s\n" % pretty_printers.format_table(self.A))
            print("\nb:%s\n"   % self.b)
            print("objective after pivots: %s" % self.c)

        # Variable assignment after pivot stops.
        assignment = [0] * len(self.b)
        #
        # All dependent variables get value of constant
        for var_idx in self.dependent:
            assignment[var_idx] = self.b[var_idx]
        #
        opt_value = self.v
        for i in range(0,len(self.c)):
            coefficient = self.c[i]
            value = assignment[i]
            if coefficient and value:
                opt_value += coefficient * value

        if debug:
            print("SlackForm: optvalue : %d assignment:%s" % (opt_value,assignment))
        # does that mean all assigned variables were explicity assigned.
        # how does it correspond to initial non-slack assignmentx
        return (opt_value, assignment)


class Simplex:

    def __init__(self,A,b,c,n,m):
        self.A = A
        self.b = b
        self.c = c
        # start with (no-constant)
        # in objective function
        self.v = 0
        self.n = n
        self.m = m

    @staticmethod
    def answer_type_str(anst):
        if anst == -1:
            return "No solution"
        if anst == 0:
            return "Bounded solution"
        if anst == 1:
            return "Infinity"
        else:
            return "Unrecognized Answer : %s" % anst
    

    def find_basic_feasible(self, min_idx):
        "Find basic feasible solution."
        slackform = SlackForm(A=self.A,b=self.b,c=self.c,v=0,n=self.n,m=self.m)
        aux_simplex = self.make_auxiliary_form()
        aux_sf = SlackForm(simplex = aux_simplex)
        nvars = self.n + self.m

        if debug:
            print("%d => (dependent) => %d " % (nvars,min_idx))
        
        aux_sf.pivot( self.n + self.m , min_idx)

        (opt,ansx) = aux_sf.solve()

        if not FPHelper.iszero(opt,rel_tol=1e-06,abs_tol=1e-06):
            if debug: print("raising infeasible %f %s"%(opt,FPHelper.iszero(opt,rel_tol=1e-09,abs_tol=1e-09)))
            raise InfeasibleError()

        if debug:
            print("dependent : %s" % aux_sf.dependent)

        if debug: print("BEGIN:subsitite-auxiliary-form-objective ")

        new_obj = SlackForm.Constraint(slackform.v,slackform.c)
        for idx in aux_sf.dependent:
            constant, equation = aux_sf.b[idx],aux_sf.A[idx]
            entering_constraint = SlackForm.Constraint(constant,equation)
            new_obj = SlackForm.Constraint.substitute_constraint(new_obj,idx,entering_constraint)
            
        if debug:
            print("sub-obj: %s" % new_obj)
        if debug: print("END:subsitite-auxiliary-form-objective ")            

        ListHelper.set_values(new_obj.coefficients, None, aux_sf.dependent)
        ListHelper.set_values(aux_sf.b, None, aux_sf.independent )

        # set all unused rows  and columns to None
        MatrixHelper.set_value_all_rows_columns(aux_sf.A, None,
                                                rows= aux_sf.independent,
                                                columns= aux_sf.dependent)

        # using new objective and return new slack form need to remove
        # x_nvars
        if debug:
            print("Objective: %s" % new_obj)
            print("A: \n%s" % pretty_printers.format_table(aux_sf.A))
            print("b: \n%s" % aux_sf.b)
            print("depenedents:   \n%s"  % aux_sf.dependent)
            print("indepenedents: \n%s"  % aux_sf.independent)

        # remove last entry from rows
        MatrixHelper.pop_column(aux_sf.A)
        MatrixHelper.pop_row(aux_sf.A)

        # remove last entry from constant
        aux_sf.b.pop()

        # replace the new objective
        aux_sf.replace(c = new_obj.coefficients,
                       v = new_obj.constant)

        # remove one independent variable
        aux_sf.independent.remove(nvars)
        aux_sf.replace(m=len(aux_sf.independent)-1)

        if debug:
            print("objective: %s " % new_obj)
            print("A: \n%s" % pretty_printers.format_table(aux_sf.A))
            print("b: \n%s" % aux_sf.b)
            print("depenedents:   \n%s"  % aux_sf.dependent)
            print("indepenedents: \n%s"  % aux_sf.independent)

        return aux_sf

    def solve(self):
        if debug: print("\nSimplex solve");
        try:
            if debug:
                print("Simplex:b %s"%self.b)
            min_constant, idx = ListHelper.min_index(self.b);
            
            if  min_constant < 0: # 0-comparison
                if debug:
                    print(" Currently not in basic form :%d - index %d " % (min_constant,idx))
                simplex_basic_form = self.find_basic_feasible(idx)
                try:
                    if debug: print("-"*100)
                    opt,ansx = simplex_basic_form.solve()
                    self.optimum = opt
                    self.assignment = ansx
                    ## slack variables are the first n varialbes
                    del self.assignment[:self.n]
                    if debug:
                        print("OPTIMIMUM VALUE: %f(%s)" %(opt,debug))
                        print("ASSIGNMENT: %s " % self.assignment)
                    return (0,self.assignment)
                except UnboundedError as err:
                    return(1,None)
                except InfeasibleError as err:
                    return (-1, None)

            # basic solution is already feasible
            opt,ansx = None,None
            if min_constant > 0: # Basic form already in feasible form
                opt,ansx = SlackForm(simplex=self).solve()
                self.optimum = opt
                self.assignment = ansx
                del self.assignment[:self.n]
            if debug:
                print("Optimimum Value: %f" %opt)
                print("Assignment: %s " % self.assignment)
            return (0,self.assignment)
        except UnboundedError as err:
            return(1,None)
        except InfeasibleError as err:
            return (-1, None)

    def make_auxiliary_form(self):
        "Make auxiliiary form"
        nvars = (self.n + self.m)
        # new size
        aux_size = (nvars + 1)
        # create copy of b and extend it for x_{nvars}
        #
        aux_b = self.b[:]
        if debug:
            print("make_auxiliary_form: b:%s aux-b:%s"%(self.b,aux_b))
        #
        # set objective function: -x_{nvars}
        aux_c = ([0] * self.m)
        aux_c.append(-1)
        aux_v = 0
        #
        aux_dep = set(range(self.n))
        aux_indep = set(range(self.n,nvars))
        #
        # simplex will have one extra column and row
        # to represent x_{nvars}
        aux_A = [[None for x in range(self.m+1)]
                       for y in range(self.n)]
        # copy An
        MatrixHelper.copy_matrix(aux_A,self.A)
        
        # set nvars column to -1
        MatrixHelper.set_column_value(aux_A,self.m,-1)
        return Simplex(aux_A,aux_b,aux_c,self.n,self.m+1)

    def __repr__(self):
        return "A:\n%s\nb:\n%s\nc:\n%s\n" % (self.A,self.b,self.c)

    def __str__(self):
        return self.__repr__()

    @staticmethod
    def parse_stream(stream):
        n, m = list(map(int, stream.readline().split()))
        A = []
        for i in range(n):
            A += [list(map(int, stream.readline().split()))]
        b = list(map(int, stream.readline().split()))
        c = list(map(int, stream.readline().split()))
        return Simplex(A,b,c,n,m)

    @staticmethod
    def parse_file(fname):
        f = open(fname,"r")
        ret = Simplex.parse_stream(f)
        f.close()
        return ret


class SimplexTest(unittest.TestCase):

    def setUp(self):
        pass

    def test_01(self):
        debug=True
        A = [[-1 ,-1 ],
             [ 1 , 0 ],
             [ 0 , 1 ]]
        b = [-1 ,2 ,2]
        c = [-1 ,2]
        n = 3
        m = 2
        s = Simplex(A,b,c,n,m)
        opt,ass = s.solve()
        self.assertEqual(s.optimum,4.0)

    def test_feasible_start(self):
        A = [[1 ,1 ,3 ],
             [2 ,2 ,5 ],
             [4 ,1 ,2 ]]
        b = [30 ,24 ,36]
        c = [3 ,1 ,2]
        n = 3
        m = 3
        s = Simplex(A,b,c,n,m)
        opt,ass = s.solve()
        self.assertEqual(s.optimum,28)
    
    def test_infeasible_start(self):
        A = [[ 2 ,-1],
             [ 1 ,-5]]
        b = [2, -4]
        c = [2, -1]
        n = 2
        m = 2
        s = Simplex(A,b,c,n,m)
        opt,ass = s.solve()
        self.assertEqual(s.optimum,2.0)
    
    def test_read_01(self):
        simplex = Simplex.parse_file("./tests/bounded/01")
        self.assertIsNotNone(simplex)
        self.assertEqual(3,simplex.n)
        self.assertEqual(2,simplex.m)
        self.assertEqual(simplex.n,len(simplex.A))
    
    def test_read_04(self):
        simplex = Simplex.parse_file("./tests/bounded/04")
        anst,ansx = simplex.solve()
        if debug:
            print("%s"%ansx)
    
    def test_solve_01(self):
        simplex = Simplex.parse_file("./tests/bounded/01")
        anst,ansx = simplex.solve()
        if debug:
            print("anst:%s ansx:%s"%(anst,ansx))
        self.assertIsNotNone(anst)
        self.assertIsNotNone(ansx)

    def assertAnswerType(self,expected,fname):
        simplex = Simplex.parse_file(fname)
        anst,_=simplex.solve()
        try:
            self.assertEqual(anst,expected)
        except AssertionError:
            raise AssertionError("Checking %s expected %s got %s " % (fname, Simplex.answer_type_str(expected), Simplex.answer_type_str(anst)))
        
    def test_unbounded_files(self):
        pat = "./tests/inf/[0-9]*"
        not_answer_p = lambda fname: not fname.endswith(".a")
        for fname in filter(not_answer_p,glob.iglob(pat)):
            self.assertAnswerType(1,fname)


    def test_nosolution_files(self):
        pat = "./tests/no/[0-9]*"
        not_answer_p = lambda fname: not fname.endswith(".a")
        for fname in filter(not_answer_p,glob.iglob(pat)):
            self.assertAnswerType(-1,fname)

def run_tests():
    unittest.main(module='simplex',exit=False)

if __name__ == "__main__":

    if len(sys.argv) > 1 and (sys.argv[1] == "-d" or sys.argv[1] == "--debug") :
        debug = True
        
    simplex = Simplex.parse_stream(sys.stdin)
    anst, ansx = simplex.solve()
    print(Simplex.answer_type_str(anst))
    if anst == 0:
        print(' '.join(list(map(lambda x : '%.18f' % x, ansx))))


#run_tests()
