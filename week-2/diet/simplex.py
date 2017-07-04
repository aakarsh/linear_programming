#!/usr/bin/env python
import os
import sys
import unittest


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
            return "%s : %s" % (self.constant, self.coefficients)

        @staticmethod
        def substitute_objective(simplex,entering_constraint,entering_idx):
            constraint = SlackForm.Constraint(simplex.v,simplex.c)
            return SlackForm.Constraint.substitute_constraint(constraint,entering_idx,entering_constraint)

        @staticmethod
        def substitute_equation(simplex,equation_idx,entering_constraint,entering_idx):
            constraint =  SlackForm.Constraint(simplex.b[equation_idx],simplex.A[equation_idx])
            return SlackForm.Constraint.substitute_constraint(constraint,entering_idx,entering_constraint)

        @staticmethod
        def substitute_constraint(constraint,entering_idx,entering_constraint):
            # new_equation = Constraint.substitute_equation(self,idx,entering_constraint)
            print("substitute_constraint: ")
            print("Constraint  : %s" % entering_constraint)
            print("Entering Idx : %s" % entering_idx)
            print("Entering  : %s" % entering_constraint)

            
            current_coefficients  = constraint.coefficients
            current_constant      = constraint.constant

            print("Subsititue Into: constraint-coefficients: %s, constraint-constraint: %s" % (current_coefficients, current_constant))
            print("Equation : constraint-coefficients: %s, constraint-constraint: %s" % (entering_constraint.coefficients, entering_constraint.constant))

            return_coefficients = [None] * len(current_coefficients)
            return_constant     =  None

            variable_coefficient = current_coefficients[entering_idx]

            # TODO maybe not correct retuern the enteirng constraints
            if not variable_coefficient or variable_coefficient == 0:
                print("PREMATURE EXIT")
                return entering_constraint

            entering_constant = entering_constraint.constant
            entering_coeffs   = entering_constraint.coefficients

            if not current_constant:
                current_constant = 0.0

            return_constant = current_constant + (variable_coefficient * entering_constant)

            for var_idx in range(0,len(current_coefficients)):
                if var_idx == entering_idx:
                    continue

                current_coefficient = current_coefficients[var_idx]
                entering_coeff      =  entering_coeffs[var_idx]  if entering_coeffs[var_idx]  else 0

                if current_coefficient:
                    return_coefficients[var_idx] = current_coefficient + ( variable_coefficient * entering_coeff )
                else: # no current coefficent use subsitituded value
                    return_coefficients[var_idx] = variable_coefficient * entering_coeff

            if debug:
                print("Substitute Result : %d [ %s ] " % (return_constant,return_coefficients))

            return SlackForm.Constraint(return_constant,return_coefficients)


        @staticmethod
        def make_entering_constraint(slackform,leaving_idx,entering_idx):
            if debug:
                print("make_entering_constraint: leaving_idx: %s entering_idx: %s" % (leaving_idx,entering_idx))
            A = slackform.A
            b = slackform.b

            independent = slackform.independent
            dependent  = slackform.dependent

            nvars = len(independent) + len(dependent)

            pivot_entry = A[leaving_idx][entering_idx]
            pivot_value = abs(pivot_entry)
            pivot_sign = -1 if pivot_entry > 0 else 1
            pivot_inverse = pivot_sign * (1.0/pivot_value)

            entering_constant = b[leaving_idx] * pivot_inverse
            leaving_equation = A[leaving_idx]

            entering_equation = [None] * nvars
            for idx in independent:
                if not idx == entering_idx and not leaving_equation[idx] is None:
                    entering_equation[idx] = pivot_inverse * leaving_equation[idx]

            entering_equation[entering_idx] = None
            entering_equation[leaving_idx] = -1 * pivot_inverse

            if debug:
                print("Entering Constant: %d Equation :%s" % (entering_constant,entering_equation))

            return SlackForm.Constraint(entering_constant,entering_equation)


    def __init__(self,*args,**kwargs):
        # expand
        if kwargs["simplex"]:
            simplex = kwargs["simplex"]
            n,m = (simplex.n,simplex.m)
            A = simplex.A
            b = simplex.b
            c = simplex.c
        else:
            simplex = kwargs["simplex"]
            n,m = (kwargs["n"],kwargs["m"])
            A = kwargs["A"]
            b = kwargs["b"]
            c = kwargs["c"]

        # A represents the table of size totalxtotal
        # with None possible entreis
        nvars = n+m
        self.A = [ [None for x in range(nvars)] for y in range(nvars)]

        # We will use a numbering where
        # dependent variables will be from [x_n to x_nvars)
        # independent variables will be from [x_0 to x_n)
        # x_nvars will be a psuedo variable used in case the initial
        # simplex is not in basic form.

        for i in range(0,n):
            for j in range(0,m):
                self.A[i][j+n] = -A[i][j]

        if debug:
            print("\nA:")
            print(pretty_printers.format_table(self.A))
            print("Input Equations:")
            print(pretty_printers.format_table(simplex.A))

        if debug:
            print("orig-b:%s"% b)
        self.b = list(map(float,b))

        # Fill rest of it with None
        self.b.extend([None]*(nvars-len(b)))

        if debug:
            print("b:%s"% self.b)

        self.c = [None]* n
        self.c.extend(map(float,c))

        if debug:
            print("orig-c:%s"% c)
            print("c:%s"% self.c)

        self.v = simplex.v
        # Original variables
        self.independent   = set(range(n,nvars))

        # Slack varaibles
        self.dependent     = set(range(0,n))

        if debug:
            print("dependent : %s, independent : %s" %
                  (self.independent,self.dependent))

        leaving_coeff,leaving_idx = list_helper.min_index(self.b)

        if debug:
            print("leaving_coeff:%d leaving_idx: %d"
                  % (leaving_coeff,leaving_idx))

        # basic solution is feasible :
        # all constants are positive ?


        # TODO : Put into feasible form
        #
        # Not in basic form:
        #   - Either we can put into basic form
        #   - Or the equations are infeasible
        # TODO : Exither to do the basic form here or try to
        #        find one that is already in basic form


    def pivot(self,entering_idx,leaving_idx):
        #
        Constraint = SlackForm.Constraint
        entering_constraint = Constraint.make_entering_constraint(self,
                                                                  leaving_idx,
                                                                  entering_idx)
        entering_constraint.store(entering_idx,self)

        #
        for idx in self.dependent:
            if idx == leaving_idx:
                continue
            new_equation = Constraint.substitute_equation(self,idx,entering_constraint,entering_idx)
            new_equation.store(idx,self)

        new_objective = Constraint.substitute_objective(self,entering_constraint,entering_idx)
        print("Constraint: %s " % new_objective)
        #self.constant = constant
        #self.coefficients = coefficients
        self.c = new_objective.coefficients
        self.v = new_objective.constant
        print("New objectve %s %s "% (self.c,self.v))
        # move leaving_idx  from dependent   to independent set
        # move entering_idx from independent to dependent set

        if debug:
            print("dependent: %s leaving %d" %       (self.dependent,leaving_idx))
            print("independent: %s entering_idx %d" %(self.independent,entering_idx))

        self.dependent.remove(leaving_idx)
        self.dependent.add(entering_idx)

        self.independent.remove(entering_idx)
        self.independent.add(leaving_idx)


    def objective_has_pos_coeffs(self):
        for value in self.c:
            if value and value > 0:
                return True
        return False

    def pick_entering_idx(self):
        for idx in self.independent:
            if self.c[idx] > 0:
                return idx
        return None

    def pick_leaving_idx(self,entering_idx):
        if debug:
            print("pick_leaving_idx")
            print("Entering %d " % entering_idx)

            print("dependent: %s" % self.dependent)

        slackness = [None] * len(self.b)
        # TODO: Seeing non-None  values in b where it is not a depenedent
        if debug:
            print("b: %s"%self.b)
            print("c: %s"%self.c)
            print("\nA:\n",pretty_printers.format_table(self.A))

        for idx in self.dependent:
            constant = self.b[idx]
            coeff    = -1 * self.A[idx][entering_idx]
            if coeff > 0:
                print("%d constant[%f]/coeff[%f] = %f"%(idx,constant,coeff,constant/coeff))
                slackness[idx]  = (constant/coeff)

        if debug:
            print("slackness computed: %s ",slackness)

        # BMK - #1
        min_slack,slack_idx = list_helper.min_index(slackness)
        if min_slack:
            return slack_idx
        # TODO could not pick leaving index
        return None

    def __repr__(self):
        return "A:%s\nb:%s" %(pretty_printers.format_table(self.A),self.b)

    def solve(self):
        if debug:
            print("Enter SlackForm.solve():")

        while self.objective_has_pos_coeffs():
            if debug:
                print(self)

            entering_idx = self.pick_entering_idx()

            leaving_idx  = self.pick_leaving_idx(entering_idx)

            if not leaving_idx or not entering_idx:  # unbounded
                raise UnboundedError()

            if debug:
                print("Entering Idx : %d Objective Coefficent %d " % (entering_idx,self.c[entering_idx]))
                print("Leaving  Idx : %d Leaving Equation %s " % (leaving_idx,self.A[leaving_idx]))
                print("Calling pivot Entering: %s Leaving: %s" % (entering_idx,leaving_idx))

            self.pivot(entering_idx , leaving_idx)

        if debug:
            print("\nA:\n%s\n",pretty_printers.format_table(self.A))
            print("\nb:%s\n",self.b)
            print("objective after pivots: %s"%self.c)
        #
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

        print("SlackForm: optvalue : %d assignment:%s" % (opt_value,assignment))
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

    def find_basic_feasible(self, min_idx):
        "Find basic feasible solution."
        aux_simplex = self.make_auxiliary_form()
        aux_sf = SlackForm(simplex=aux_simplex)
        nvars = self.n + self.m
        print("Enterting id %d  Leaving id %d" % (nvars,min_idx))
        aux_sf.pivot(self.n+self.m,min_idx)
        (opt,ansx) = aux_sf.solve()
        #
        #  get x_0 and substitute it into objective function return
        #  new basic feasible solution.
        #
        # HERE
        new_objective = SlackForm.Constraint(aux_sf.v,aux_sf.c)
        for idx in aux_sf.dependent:
            equation = aux_sf.A[idx]
            constant = aux_sf.b[idx]
            
            entering_constraint = SlackForm.Constraint(constant,equation)

            # depressed because subsittution code may not be 
            # def substitute_constraint(constraint,entering_idx,entering_constraint):
            
            new_objective = SlackForm.Constraint.substitute_constraint(new_objective,idx,entering_constraint)

        if debug:
            print("Substituted Objective: %s" % new_objective)
        
        
    def solve(self):
        if debug: print("\nSimplex solve");
        try:
            print("Simplex:b %s"%self.b)
            min_constant, idx = list_helper.min_index(self.b);
            if debug and min_constant < 0:
                print(" Currently not in basic form :%d - index %d " %
                      (min_constant,idx))
                simplex_basic_form = self.find_basic_feasible(idx)
                return
            # basic solution is already feasible
            opt,ansx = None,None
            if min_constant > 0: # Basic form already in feasible form
                opt,ansx = SlackForm(simplex=self).solve()
            if debug:
                print("Optimimum Value: %f" %opt)
                print("Assignment: %s " % ansx[self.n:self.n+self.m])
            return (opt,ansx)
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
        print("make_auxiliary_form: b:%s aux-b:%s"%(self.b,aux_b))
        #
        # set objective function: -x_{nvars}
        aux_c = ([0] * self.m)
        aux_c.append(-1)
        aux_v = 0
        #
        aux_dep = set(range(0,self.n))
        aux_indep = set(range(self.n,nvars))
        #
        # simplex will have one extra column and row
        # to represent x_{nvars}
        aux_A = [[None for x in range(self.m+1)]
                       for y in range(self.n)]
        # copy A
        for r in range(self.n):
            for c in range(self.m):
                aux_A[r][c] = self.A[r][c]
        #
        # set nvars column to -1
        for i in range(self.n):
            aux_A[i][self.m]= -1
        #
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

    # def test_feasible_start(self):
    #     A=[[1 ,1 ,3 ],
    #        [2 ,2 ,5 ],
    #        [4 ,1 ,2 ]]
    #     b = [30 ,24 ,36]
    #     c = [3 ,1 ,2]
    #     n = 3
    #     m = 3
    #     s = Simplex(A,b,c,n,m)
    #     opt,ass = s.solve()
    #     self.assertEqual(opt,28)

    def test_infeasible_start(self):
        A = [[ 2 ,-1],
             [ 1 ,-5]]
        b = [2, -4]
        c = [2, -1]
        n = 2
        m = 2
        s = Simplex(A,b,c,n,m)
        opt,ass = s.solve()
        self.assertEqual(opt,2.0)

    # def test_read_01(self):
    #     simplex = Simplex.parse_file("./tests/01")
    #     self.assertIsNotNone(simplex)
    #     self.assertEqual(3,simplex.n)
    #     self.assertEqual(2,simplex.m)
    #     self.assertEqual(simplex.n,len(simplex.A))
    #
    # def test_solve_01(self):
    #     simplex = Simplex.parse_file("./tests/01")
    #     anst,ansx = simplex.solve()
    #     self.assertIsNotNone(anst)
    #     self.assertIsNotNone(ansx)



def run_tests():
    unittest.main(module='simplex',exit=False)

if __name__ == "__main__":
    simplex = Simplex.parse_stream(sys.stdin)
    anst, ansx = simplex.solve()

    if anst == -1:
        print("No solution")
    if anst == 0:
        print("Bounded solution")
        print(' '.join(list(map(lambda x : '%.18f' % x, ansx))))
    if anst == 1:
        print("Infinity")

class UnboundedError(Exception):
    "Raised when the solution for given equations is unbounded "
    pass

class InfeasibleError(Exception):
    "Raised when the solution for given equations is infeasible(has no-solution)."
    pass

class ListHelper:
    @staticmethod
    def min_index(l,max=float('inf')):
        "Return a pair of (value,index) of elment with minimum index"
        zl = zip(l,range(0,len(l)))
        zp = min(zl, key = lambda z: z[0] if z[0] else max)
        return zp

class PrettyPrinters:
    @staticmethod
    def format_table(matrix):
        "Format matrix as a table"
        table_str =""
        for row in matrix:
            first_col = True
            for col in row:
                if first_col:
                    table_str +="| "
                    first_col=False
                if not col is None:
                    table_str+="%+2.2f"%float(col)
                else:
                    table_str+="%5s"%"None"
                table_str+=" | "
            table_str+="\n"
        return table_str

# singleton helpers
list_helper  =  ListHelper()
pretty_printers = PrettyPrinters()
debug = True

#run_tests()
