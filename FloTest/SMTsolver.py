# This example requires Z3 and MathSAT to be installed (but you can
#  replace MathSAT with any other solver for QF_LRA)
#
# This examples shows how to:
# 1. Define Real valued constants using floats and fractions
# 2. Perform quantifier elimination
# 3. Pass results from one solver to another
#
from math import inf
from pysmt.shortcuts import Solver, Symbol, Real, Plus, And, Equals, Ite
from pysmt.typing import REAL
from pysmt.parsing import parse
import z3

def SMTtesting(list_var, list_cost, formula):

    list_symbols = [Symbol(s) for s in list_var]
    print(list_symbols)
    SOL = Symbol("SOL", REAL)
    zero = Real(0)

    list_cond_cost = [Ite(s, Real(c), zero) for s, c in zip(list_symbols, list_cost)]
    print(list_cond_cost)

    problem = parse(formula)
    sum = Plus(list_cond_cost)
    print(sum)

    print("")
    print("@@@@@@@@@@ SMT SOLVER Z3 @@@@@@@@@@")

    f = And(problem, Equals(SOL, sum))

    with Solver(name="z3") as sol_z3:
        converter = sol_z3.converter

        # How ??
        # Dual Simplex
        Z3_form = converter.convert(f)
        Z3_sol = converter.convert(SOL)
        o = z3.Optimize()
        o.add(Z3_form)
        print(Z3_form)
        o.minimize(Z3_sol)
        print(Z3_sol)
        print(o.check())
        print(o.reason_unknown())
        best = inf
        while o.check() == z3.sat:
            model = o.model()
            new_best = model[Z3_sol]

            if new_best.as_long() > best:
                break
            best = new_best.as_long()
            print(model)
            block = []
            for d in model:
                c = d()
                block.append(c != model[d])
            o.add(z3.Or(block))

if __name__ == "__main__":

    list_var = ["X1", "X2", "X3", "X4"]
    list_cost = [3, 1, 2, 2]
    formula = " (X1 | X2) & (X3 | X4) "

    SMTtesting(list_var, list_cost, formula)