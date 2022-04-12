# This example requires Z3 and MathSAT to be installed (but you can
#  replace MathSAT with any other solver for QF_LRA)
#
# This examples shows how to:
# 1. Define Real valued constants using floats and fractions
# 2. Perform quantifier elimination
# 3. Pass results from one solver to another
#
from math import inf
from pysmt.shortcuts import Solver, Symbol, Real, Plus, And, Equals, Ite, Times, GE, LE
from pysmt.typing import REAL
from pysmt.parsing import parse
import z3
from fractions import Fraction

# ! Instead of using Forall to compare all existing models to find the minimum -> Minimize -> Simplex Z3

def SMTformating(solutions, list_var):
    bool_only_list = []
    for l in solutions:
        tmp = [-1]*len(list_var)
        for e in l:
            if z3.is_true(l[e]):
                tmp[list_var.index(str(e()))] = 1
        bool_only_list.append(tmp)
    return list_var, bool_only_list

def SMTcost(list_var, list_cost, formula, upper_bound=None):

    list_symbols = [Symbol(s) for s in list_var]
    print(list_symbols)
    SOL = Symbol("%SOL%", REAL)
    zero = Real(0)
    list_cond_cost = [Ite(s, Real(c), zero) for s, c in zip(list_symbols, list_cost)]
    print(list_cond_cost)
    problem = parse(formula)
    sum = Plus(list_cond_cost)
    print(sum)
    f = And(problem, Equals(SOL, sum))

    if upper_bound != None:
        f = And(f, LE(SOL, Real(upper_bound)))
    print("")
    print("@@@@@@@@@@ SMT SOLVER Z3 @@@@@@@@@@")

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
        if o.check() != z3.sat:
            print(o.reason_unknown())
        first = True
        best = z3.Real(0)
        solutions = []
        while o.check() == z3.sat:
            # TODO model doesnt give every variable !!
            model = o.model()
            new_best = model[Z3_sol]

            if first:
                best = new_best
                first = False
                # MODEL COMPLETION OPTION TO GET EVERY VARIABLE
                model.eval(Z3_form, model_completion=True)
            elif z3.simplify(new_best > best):
                break

            print(model)
            solutions.append(model)
            block = []
            for d in model:
                c = d()
                block.append(c != model[d])
            o.add(z3.Or(block))

        vars, sols = SMTformating(solutions, list_var)
        return vars, sols, best

def SMTproba(list_var, list_proba, formula, lower_bound=0):

    list_symbols = [Symbol(s) for s in list_var]
    print(list_symbols)
    SOL = Symbol("%SOL%", REAL)
    one = Real(1)
    list_and_proba = [Ite(s, Real(c), one) for s, c in zip(list_symbols, list_proba)]
    print(list_and_proba)
    problem = parse(formula)
    # TODO CHANGE TO ENABLE PROBA
    sum = Times(list_and_proba)
    print(sum)
    f = And(problem, Equals(SOL, sum))

    if lower_bound > 0:
        f = And(f, GE(SOL, Real(lower_bound)))
    print("")
    print("@@@@@@@@@@ SMT SOLVER Z3 @@@@@@@@@@")

    with Solver(name="z3") as sol_z3:
        converter = sol_z3.converter
        # How ??
        # Dual Simplex
        #Z3_symbols = [converter.convert(s) for s in list_symbols]
        Z3_form = converter.convert(f)
        Z3_sol = converter.convert(SOL)
        o = z3.Optimize()
        o.add(Z3_form)
        print(Z3_form)
        o.maximize(Z3_sol)
        print(Z3_sol)
        print(o.check())
        if o.check() != z3.sat:
            print(o.reason_unknown())
        first = True
        best = z3.Real(0)
        solutions = []
        while o.check() == z3.sat:
            model = o.model()
            new_best = model[Z3_sol]

            if first:
                best = new_best
                first = False
                # MODEL COMPLETION OPTION TO GET EVERY VARIABLE
                model.eval(Z3_form, model_completion=True)
            elif z3.simplify(new_best < best):
                break

            print(model)
            solutions.append(model)
            block = []
            for d in model:
                c = d()
                block.append(c != model[d])
            o.add(z3.Or(block))

        vars, sols = SMTformating(solutions, list_var)
        return vars, sols, best

if __name__ == "__main__":

    list_var = ["X1", "X2", "X3", "X4"]
    list_cost = [3, 1.5, 2, 2]
    list_cost = [Fraction(str(x)) for x in list_cost]
    # USE GMPY LIBRARY
    #list_proba = [Fraction('0.7'), Fraction('0.2'), Fraction('0.5'), Fraction('0.5')]
    list_proba = [0.7, 0.2, 0.5, 0.5]
    list_proba = [Fraction(str(x)) for x in list_proba]
    print(list_proba)

    formula = " (X1 | X2) & (X3 | X4) "

    cost_max = Fraction(str(3.6))
    proba_min = Fraction(str(0.3))

    print("COST")
    print(SMTcost(list_var, list_cost, formula, cost_max))

    print("PROBA")
    print(SMTproba(list_var, list_proba, formula, proba_min))