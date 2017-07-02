#!/usr/bin/env python
import os
import sys
import unittest

debug = True

class UnboundedError(Exception):
    "Raised when the solution for given equations is unbounded "
    pass

class InfeasibleError(Exception):
    "Raised when the solution for given equations is infeasible(has no-solution)."
    pass

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

        @staticmethod
        def substitute_objective(simplex,idx,entering_constraint,entering_idx):
            constraint = Constraint(simplex.c,simplex.v)
            substitute_constraint(constraint,entering_idx,entering_constraint)

        @staticmethod
        def substitute_equation(simplex,equation_idx,entering_constraint,entering_idx):
            constraint =  Constraint(simblex.b[equation_idx],simplex.A[equation_idx])
            substitute_constraint(constraint,entering_idx,entering_constraint)

        @staticmethod
        def substitute_constraint(constraint,entering_idx,entering_constraint):
            # new_equation = Constraint.substitute_equation(self,idx,entering_constraint)
            current_coefficients  = constraint.coefficients
            current_constant      = constraint.constant

            return_coefficients = [None] * len(current_coefficients)
            return_constant     =  None

            variable_coefficient = entering_constraint.coefficients[entering_idx]

            # TODO maybe not correct retuern the enteirng constraints
            if not variable_coefficient or variable_coefficient == 0:
                return entering_constraint

            entering_constant = entering_constraint.constant
            entering_coeffs   = entering_coeffs.coefficients

            if not current_constant:
                current_constant = 0.0

            return_constant = current_constant + (variable_coefficient * entering_constant)

            for var_idx in range(0,len(current_coefficients)):
                current_coefficient = current_coefficients[var_idx]
                entering_coeff     = entering_coeffs[var_idx]
                #
                if var_idx == entering_idx:
                    continue
                #
                if (not entering_coeff) or (not current_coefficient):
                    continue
                #
                if not entering_coeff:
                    entering_coeff = 0
                #
                if current_coefficient:
                    return_coefficients[var_idx] = current_coefficient + ( variable_coefficient * entering_coeff )
                else: # no current coefficent use subsitituded value
                    return_coefficients[var_idx] = variable_coefficient * entering_coeff

            return Constraint(return_constant,return_coefficients)
        @staticmethod
        def make_entering_constraint(simplex,leaving_idx,entering_idx):
            A = simplex.A
            b = simplex.b

            pivot_entry = A[leaving_idx][entering_idx]
            pivot_value = abs(pivot_entry)
            pivot_sign = -1 if pivot_entry > 0 else 1
            pivot_inverse = pivot_sign * (1.0/pivot_value)

            entering_constant = b[leaving_idx] * pivot_inverse
            leaving_equation = A[leaving_idx]

            entering_equation = \
            [ pivot_inverse * leaving_equation[idx] if not idx == entering_idx else None
              for idx in indepedent ]

            entering_equation[entering_idx] = None
            entering_equation[leaving_idx] = -1 * pivot_inverse

            return Constraint(entering_constant,entering_equation)


    def __init__(self, simplex):
        # expand
        n,m = (simplex.n,simplex.m)
        A = simplex.A
        b = simplex.b
        c = simplex.c

        # A represents the table of size totalxtotal
        # with None possible entreis
        nvars = n+m
        self.A = [[None] * nvars] * nvars

        # We will use a numbering where
        # dependent variables will be from [x_n to x_nvars)
        # independent variables will be from [x_0 to x_n)
        # x_nvars will be a psuedo variable used in case the initial
        # simplex is not in basic form.
        for i in range(0,n):
            for j in range(0,m):
                self.A[i][j+n] = -A[i][j]

        self.b = [None] * nvars
        for i in range(0,n):
            self.b[i] = b[i]

        self.c = [None] * nvars
        for i in range(0,m):
            self.c[i+n] = c[i]

        self.v = simplex.v

        self.independent  = set(range(0,n))
        self.dependent     = set(range(n,nvars))


        leaving_coeff,leaving_idx = SlackForm.__min_idx__(self.b)

        # already in basic form
        if leaving_coeff > 0:
            self.infeasible = False
            return

        # TODO : Put into feasible form
        # Not in basic form:
        #   - Either we can put into basic form
        #   - Or the equations are infeasible

        self.infeasible = True
        self.aux_form()

        print("%s",self.A)

    @staticmethod
    def __min_idx__(l):
        zl = zip(l,range(0,len(l)))
        zp = min(zl, key=lambda z: z[0] if z[0] else float('inf'))
        return zp

    def pivot(self,entering_idx,leaving_idx):
        entering_constraint = Constraint.make_entering_constraint(self,leaving_idx,entering_idx)
        entering_constraint.store(entering_idx,self)

        for idx in self.dependent:
            if idx == leaving_idx:
                continue
            new_equation = Constraint.substitute_equation(self,idx,entering_constraint,entering_idx)
            new_equation.store(idx,self)

        Constraint.substitute_objective(self,entering_constraint,entering_idx)

        # move leaving_idx  from dependent   to independent set
        # move entering_idx from independent to dependent set
        
        self.dependent.remove(leaving_idx)
        self.dependent.add(entering_idx)

        self.independent.remove(entering_idx)
        self.independent.add(leaving_idx)


    def objective_has_pos_coeffs(self):
        for value in self.c:
            if value and v > 0:
                return True
        return False

    def pick_entering_idx(self):
        for idx in self.independent:
            if self.c[idx] > 0:
                return idx
        return None

    def pick_leaving_idx(self,entering_idx):
        slackness = [None] * len(self.b)

        for idx in self.dependent:
            constant = self.b[idx]
            coeff    = -1 * self.A[idx][entering_idx]
            if coeff > 0:
                slackness[idx]  = (constant/coeff)

        # BMK - #1
        min_slack,slack_idx = SlackForm.__min_idx__(slackness)
        if min_slack:
            return slack_idx
        return None

    def aux_form(self):
        pass
        # self.aux_A = [row[:]  for row in self.A]
        # self.aux_b = self.b[:]
        # self.aux_dep = set(self.dependent)
        # self.aux_indep = set(self.independent)
        # Add x_{nvars} to slack to orignal set of constraints.



    def solve(self):
        if self.infeasible:
            raise InfeasibleError();

        while self.objective_has_pos_coeffs():
            entering_idx = self.pick_entering_idx()
            leaving_idx  = self.pick_leaving_idx(entering_idx)
            if not (leaving_idx or entering_idx):  # unbounded
                raise UnboundedError()
            self.pivot(entering_idx , leaving_idx)
        
        # Variable assignment after pivot stops.
        assignment = [0] * len(self.b)

        # All dependent variables get value of constant 
        for var_idx in self.dependent:
            assignment[var_idx] = self.b[var_idx]

        opt_value = self.v
        for i in range(0,len(self.c)):
            coefficient = self.c[i]
            value = assignment[i]
            opt_value += coefficient*value
        
        return (opt_value, assignment)


class Simplex:

    def __init__(self,A,b,c,v,n,m):
        self.A = A
        self.b = b
        self.c = c
        self.v = v
        self.n = n
        self.m = m

    def solve(self):
        try:
            anst,ansx = SlackForm(self).solve()
            return (anst,ansx)
        except UnboundedError as err:
            return(1,None)
        except InfeasibleError as err:
            return (-1, None)


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
        return Simplex(A,b,c,0,n,m)

    @staticmethod
    def parse_file(fname):
        f = open(fname,"r")
        ret = Simplex.parse_stream(f)
        f.close()
        return ret


class SimplexTest(unittest.TestCase):

    def setUp(self):
        pass

    def test_read_01(self):
        simplex = Simplex.parse_file("./tests/01")
        self.assertIsNotNone(simplex)
        self.assertEqual(3,simplex.n)
        self.assertEqual(2,simplex.m)
        self.assertEqual(simplex.n,len(simplex.A))

    def test_solve_01(self):
        simplex = Simplex.parse_file("./tests/01")
        anst,ansx = simplex.solve()
        self.assertIsNotNone(ansx)


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
