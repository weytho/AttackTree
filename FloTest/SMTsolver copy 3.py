# This example requires Z3 and MathSAT to be installed (but you can
#  replace MathSAT with any other solver for QF_LRA)
#
# This examples shows how to:
# 1. Define Real valued constants using floats and fractions
# 2. Perform quantifier elimination
# 3. Pass results from one solver to another
#
from pysmt.shortcuts import Symbol, Or, Not, Iff, ForAll, GE, LT, Real, Plus, Int, And, Exists, LE, get_model, GT, Equals
from pysmt.shortcuts import qelim, is_sat, Ite
from pysmt.typing import REAL, INT

x, y, z = [Symbol(s, REAL) for s in "xyz"]

f = ForAll([x], Or(LT(x, Real(5.0)),
                   GE(Plus(x, y, z), Real((17,2))))) # (17,2) ~> 17/2
print("f := %s" % f)
#f := (forall x . ((x < 5.0) | (17/2 <= (x + y + z))))

qf_f = qelim(f, solver_name="z3")
print("Quantifier-Free equivalent: %s" % qf_f)
#Quantifier-Free equivalent: (7/2 <= (z + y))

res = is_sat(qf_f, solver_name="msat")
print("SAT check using MathSAT: %s" % res)
#SAT check using MathSAT: True


a, b = [Symbol(s, INT) for s in "ab"]

#f2 = Exists([a], And(LT(Int(0), a), LT(Int(1), b) , LE(a, b) ))
f2 = And(LT(Int(0), a), LT(Int(1), b) , LE(a, b) )
print("f2 := %s" % f2)
print(get_model(f2))

qf_f = qelim(f2, solver_name="z3")
print("Quantifier-Free equivalent: %s" % qf_f)

res = is_sat(qf_f, solver_name="msat")
print("SAT check using MathSAT: %s" % res)

print(get_model(f2, solver_name="z3"))


X1 = Symbol("X1")
X2 = Symbol("X2")
problem = Or(X1,X2)
EQ = Symbol("EQ")

arr = [X1, X2]
SOL = Symbol("SOL", INT)
SOL2 = Symbol("SOL2", INT)

m = Ite(X1, Int(3), Int(0))
print(m)
n = Ite(X2, Int(1), Int(0))
print(n)

m2 = Plus(m, n)
print(m2)

fin = And(Equals(SOL, m2), problem)

print(fin)
bad = And(Not(problem))
good = And( LE(SOL, SOL2), LE(SOL2, m2), problem )
all = And(fin, ForAll( [X1, X2], Or(good, bad) ))

print(all.serialize())

print("all := %s" % all.serialize())
qf_f = qelim(all, solver_name="z3")
print("Quantifier-Free equivalent: %s" % qf_f)
res = is_sat(qf_f, solver_name="msat")
print("SAT check using MathSAT: %s" % res)
print(get_model(all))



G = Symbol("G", INT)
G2 = Symbol("G2", INT)
g1 =And(GE(G, Int(0)), ForAll([G2], And(GE(G2, G))))
print(g1)
print(is_sat(g1))
print(get_model(g1))