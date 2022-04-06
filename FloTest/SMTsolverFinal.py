# This example requires Z3 and MathSAT to be installed (but you can
#  replace MathSAT with any other solver for QF_LRA)
#
# This examples shows how to:
# 1. Define Real valued constants using floats and fractions
# 2. Perform quantifier elimination
# 3. Pass results from one solver to another
#
from math import inf
from pysmt.shortcuts import Solver, Symbol, EqualsOrIff, Or, Not, Iff, Max, ForAll, Implies, TRUE, GE, LT, Real, Plus, Int, And, Exists, LE, get_model, GT, Equals
from pysmt.shortcuts import qelim, is_sat, Ite
from pysmt.typing import REAL, INT
from pysmt.oracles import get_logic
from pysmt.parsing import parse
import z3

def all_smt(formula, keys):
    target_logic = get_logic(formula)
    print("Target Logic: %s" % target_logic)
    with Solver(logic=target_logic) as solver:
        solver.add_assertion(formula)
        while solver.solve():
            partial_model = [EqualsOrIff(k, solver.get_value(k)) for k in keys]
            print(partial_model)
            solver.add_assertion(Not(And(partial_model)))

def SMTtesting(list_var, list_cost, formula):

    print("@@@@@@@@@@ TEST OPTI MATHSAT @@@@@@@@@@")

    list_symbols = [Symbol(s) for s in list_var]
    print(list_symbols)
    SOL = Symbol("SOL", REAL)
    zero = Real(0)

    list_cond_cost = [Ite(s, Real(c), zero) for s, c in zip(list_symbols, list_cost)]
    print(list_cond_cost)

    problem = parse(formula)
    sum = Plus(list_cond_cost)
    print(sum)

    fin = And(Equals(SOL, sum), problem)

    print(fin)
    print("")

    all = And(fin, ForAll( list_symbols, Implies(problem, LE(SOL, sum))))
    print(all.serialize())
    print("")

    # Dual Simplex
    qf_f = qelim(all, solver_name="msat_fm")
    print("")
    print("Quantifier-Free equivalent: %s" % qf_f)
    res = is_sat(qf_f, solver_name="msat")
    print("SAT check using MathSAT: %s" % res)
    all_smt(all, list_symbols + [SOL])

    print("")
    print("@@@@@@@@@@ TEST OPTI Z3 @@@@@@@@@@")

    f = And(problem, Equals(SOL, sum))

    with Solver(name="z3") as sol_z3:
        converter = sol_z3.converter

        # How ??
        o = z3.Optimize()
        o.add(converter.convert(f))
        print(converter.convert(f))
        o.minimize(converter.convert(SOL))
        print(converter.convert(SOL))
        print(o.check())
        print(o.reason_unknown())
        best = inf
        while o.check() == z3.sat:
            model = o.model()
            new_best = model[converter.convert(SOL)]

            if new_best.as_long() <= best:
                best = new_best.as_long()
            else:
                break

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