##
# @file
# Solve the boolean formula in term of costs or probabilities
#
from pysmt.shortcuts import Solver, Symbol, Real, Plus, And, Equals, Ite, Times, GT, LT, GE, LE
from pysmt.typing import REAL
from pysmt.parsing import parse, HRParser, InfixOpAdapter
import z3
from fractions import Fraction
from pysmt.oracles import get_logic
from collections import namedtuple

# ! Instead of using Forall to compare all existing models to find the minimum -> Minimize -> Simplex Z3

def SMTformating(solutions, list_var):
    bool_only_list = []
    values_array = []
    for l in solutions:
        tmp = [-1]*len(list_var)
        for e in l:
            if z3.is_true(e[1]):
                tmp[list_var.index(str(e[0]))] = 1
            elif str(e[0]) == "%SOL%":
                values_array.append(e[1])
        bool_only_list.append(tmp)

    return list_var, bool_only_list, values_array

def SMTcost(list_var, list_cost, formula, upper_bound=None):
    formula = formula.replace('~', '!')
    list_symbols = [Symbol(s) for s in list_var]
    list_smt_cost = [Real(c) for c in list_cost]
    zero = Real(0)

    domains = And([GE(c, zero) for c in list_smt_cost])

    SOL = Symbol("%SOL%", REAL)
    list_cond_cost = [Ite(s, c, zero) for s, c in zip(list_symbols, list_smt_cost)]

    HR = HRParser()
    Rule = namedtuple('Rule', ['regex', 'symbol', 'is_functional'])
    for r in HR.lexer.rules:
        if r[0] == r"(\^)":
            HR.lexer.rules[HR.lexer.rules.index(r)] = Rule(r"(\^)", InfixOpAdapter(HR.lexer.mgr.Xor, 10), False)
            break
    problem = HR.parse(formula)

    sum = Plus(list_cond_cost)

    if upper_bound != None:
        f = And(domains, problem, Equals(SOL, sum), LT(SOL, Real(upper_bound)))
        get_all = True
    else:
        f = And(domains, problem, Equals(SOL, sum))
        get_all = False

    #print(get_logic(f))
    print("####################### SMT SOLVER (Z3 COST) #########################")

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

            block = []
            filtered_model = []
            for d in model:
                c = d()
                if str(c) in list_var or str(c) == "%SOL%":
                    filtered_model.append((c, model[d]))
                    block.append(c != model[d])

            solutions.append(filtered_model)
            o.add(z3.Or(block))

        vars, sols, values = SMTformating(solutions, list_var)
        return vars, sols, best, values

def SMTproba(list_var, list_proba, formula, lower_bound=None):
    formula = formula.replace('~', '!')
    list_symbols = [Symbol(s) for s in list_var]
    list_smt_proba = [Real(p) for p in list_proba]
    one = Real(1)
    zero = Real(0)

    domains = And([And(LE(p, one), GE(p, zero)) for p in list_smt_proba])

    SOL = Symbol("%SOL%", REAL)
    list_and_proba = [Ite(s, p, one) for s, p in zip(list_symbols, list_smt_proba)]

    HR = HRParser()
    Rule = namedtuple('Rule', ['regex', 'symbol', 'is_functional'])
    for r in HR.lexer.rules:
        if r[0] == r"(\^)":
            HR.lexer.rules[HR.lexer.rules.index(r)] = Rule(r"(\^)", InfixOpAdapter(HR.lexer.mgr.Xor, 10), False)
            break
    problem = HR.parse(formula)

    prod = Times(list_and_proba)

    if lower_bound != None:
        f = And(domains, problem, Equals(SOL, prod), GT(SOL, Real(lower_bound)))
        get_all = True
    else:
        f = And(domains, problem, Equals(SOL, prod))
        get_all = False

    #print(get_logic(f))
    print("####################### SMT SOLVER (Z3 PROBA) #########################")

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
                # Get all min solutions with the same proba
                break

            block = []
            filtered_model = []
            for d in model:
                c = d()
                if str(c) in list_var or str(c) == "%SOL%":
                    filtered_model.append((c, model[d]))
                    block.append(c != model[d])

            solutions.append(filtered_model)
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
    
    list_proba = [0.7, 0.66, 0.5, 0.5]
    list_proba = [Fraction(str(x)) for x in list_proba]

    formula = " (X1 | X2) & (X3 ^ X4) "
    #formula = " (X1 | X2)"
    #formula = " (X1 ^ X2 ^ X3 ^ X4) "

    cost_max = Fraction(str(6))
    proba_min = Fraction(str(0.3))

    #z3.set_option(verbose=10)

    print("COST")
    print(SMTcost(list_var, list_cost, formula, cost_max))

    print()
    print(SMTcost(list_var, list_cost, formula))

    print("PROBA")
    print(SMTproba(list_var, list_proba, formula, proba_min))

    print()
    print(SMTproba(list_var, list_proba, formula))


