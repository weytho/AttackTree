# This example requires Z3 and MathSAT to be installed (but you can
#  replace MathSAT with any other solver for QF_LRA)
#
# This examples shows how to:
# 1. Define Real valued constants using floats and fractions
# 2. Perform quantifier elimination
# 3. Pass results from one solver to another
#
from pysmt.shortcuts import Symbol, Or, Not, Iff, ForAll, Implies, TRUE, GE, LT, Real, Plus, Int, And, Exists, LE, get_model, GT, Equals
from pysmt.shortcuts import qelim, is_sat, Ite
from pysmt.typing import REAL, INT

X1 = Symbol("X1")
X2 = Symbol("X2")
X3 = Symbol("X3")
X4 = Symbol("X4")
problem = And(Or(X1,X2),Or(X3, X4))
EQ = Symbol("EQ")

arr = [X1, X2]
SOL = Symbol("SOL", REAL)
SOL2 = Symbol("SOL2", REAL)
TEST = Symbol("TEST")

m = Ite(X1, Real(3), Real(0))
print(m)
n = Ite(X2, Real(1), Real(0))
print(n)
i = Ite(X3, Real(2), Real(0))
print(i)
j = Ite(X4, Real(4), Real(0))
print(j)

m2 = Plus(m, n,i ,j)
print(m2)

fin = And(Equals(SOL, m2), problem, LE(SOL, SOL2))

print(fin)
bad = And(Not(TEST))

good = And( LE(SOL, SOL2), Equals(SOL2, m2), TEST, Iff(TEST, problem) )

all = And(fin, ForAll( [X1, X2, X3, X4], Implies(problem, LE(SOL2, m2))))

print(all.serialize())

print("all := %s" % all.serialize())
qf_f = qelim(all, solver_name="z3")
print("Quantifier-Free equivalent: %s" % qf_f)
res = is_sat(qf_f, solver_name="msat")
print("SAT check using MathSAT: %s" % res)
print(get_model(all))