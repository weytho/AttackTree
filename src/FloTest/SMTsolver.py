##
# @file
# Solve the boolean formula in term of costs or probabilities
#
from pysmt.shortcuts import Solver, Symbol, Real, Plus, And, Equals, Ite, Times, GT, LT
from pysmt.typing import REAL
from pysmt.parsing import parse
import z3
from fractions import Fraction

# ! Instead of using Forall to compare all existing models to find the minimum -> Minimize -> Simplex Z3

def SMTformating(solutions, list_var):
    bool_only_list = []
    values_array = []
    for l in solutions:
        tmp = [-1]*len(list_var)
        for e in l:
            if z3.is_true(l[e]):
                tmp[list_var.index(str(e()))] = 1
            elif e.name() == "%SOL%":
                values_array.append(l[e])
        bool_only_list.append(tmp)

    return list_var, bool_only_list, values_array

def SMTcost(list_var, list_cost, formula, upper_bound=None):
    formula = formula.replace('~', '!')
    list_symbols = [Symbol(s) for s in list_var]

    SOL = Symbol("%SOL%", REAL)
    zero = Real(0)
    list_cond_cost = [Ite(s, Real(c), zero) for s, c in zip(list_symbols, list_cost)]

    problem = parse(formula)
    sum = Plus(list_cond_cost)

    f = And(problem, Equals(SOL, sum))
    get_all = False

    if upper_bound != None:
        f = And(f, LT(SOL, Real(upper_bound)))
        get_all = True

    print("@@@@@@@@@@ SMT SOLVER Z3 COST @@@@@@@@@@")

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
            model = o.model()
            new_best = model[Z3_sol]

            if first:
                best = new_best
                first = False
                # MODEL COMPLETION OPTION TO GET EVERY VARIABLE
                model.eval(Z3_form, model_completion=True)
            elif not get_all and z3.simplify(new_best > best):
                break

            solutions.append(model)
            block = []
            for d in model:
                c = d()
                block.append(c != model[d])
            o.add(z3.Or(block))

        vars, sols, values = SMTformating(solutions, list_var)
        return vars, sols, best, values

def SMTproba(list_var, list_proba, formula, lower_bound=0):
    formula = formula.replace('~', '!')
    list_symbols = [Symbol(s) for s in list_var]

    SOL = Symbol("%SOL%", REAL)
    one = Real(1)
    list_and_proba = [Ite(s, Real(c), one) for s, c in zip(list_symbols, list_proba)]

    problem = parse(formula)
    sum = Times(list_and_proba)

    f = And(problem, Equals(SOL, sum))
    get_all = False

    if lower_bound > 0:
        f = And(f, GT(SOL, Real(lower_bound)))
        get_all = True
    print("")
    print("@@@@@@@@@@ SMT SOLVER Z3 PROBA @@@@@@@@@@")

    with Solver(name="z3") as sol_z3:
        converter = sol_z3.converter
        # How ??
        # Dual Simplex
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
            elif not get_all and z3.simplify(new_best < best):
                break

            #print(model)
            solutions.append(model)
            block = []
            for d in model:
                c = d()
                block.append(c != model[d])
            o.add(z3.Or(block))

        vars, sols, values = SMTformating(solutions, list_var)
        if len(solutions) > 0:
            values = [round(float(e.as_fraction()), 5) for e in values]
            best = round(float(best.as_fraction()), 5)
        return vars, sols, best, values

if __name__ == "__main__":

    list_var = ["X1", "X2", "X3", "X4"]
    list_cost = [3, 1, 2, 2]
    list_cost = [Fraction(str(x)) for x in list_cost]
    
    list_proba = [0.7, 0.2, 0.5, 0.5]
    list_proba = [Fraction(str(x)) for x in list_proba]

    formula = " (X1 | X2) & (X3 | ~ X4) "

    cost_max = Fraction(str(6))
    proba_min = Fraction(str(0.3))

    print("COST")
    print(SMTcost(list_var, list_cost, formula, cost_max))

    print()
    #print(SMTcost(list_var, list_cost, formula))

    print("PROBA")
    print(SMTproba(list_var, list_proba, formula, proba_min))

    print()
    #print(SMTproba(list_var, list_proba, formula))

