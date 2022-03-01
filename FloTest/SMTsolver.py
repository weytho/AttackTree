from sympy import *
from pysat.solvers import Glucose3
import os
import time
from pysmt.shortcuts import Symbol, And, GE, LT, Plus, Equals, Int, get_model, Not, get_env
from pysmt.typing import INT
from pysmt.rewritings import CNFizer

def main():
    # pas E I N O Q en première lettre ! 
    #str_formula = "(a & b) | (~(a & c) & (a | c | d))"
    str_formula = "(~((p | q) & r)) | (~s) "
    #str_formula = "( ( ( node000 | node001 ) & node01 & ( ( node0200 & node0201 & node0202 & ( node000 | node001 ) ) | ( node0210 & node0211 & node0212 & node000 ) | node01 ) ) | ( ( node100 | node101 ) & node11 & ( node120 & ( node1210 | node1211 ) | ( node1220 & node1221 & node11 ) & node01 ) ) | ( ( node200 & node201 ) | node21 | node001 ) )"
    #str_formula = "( a | (c & (d | z | t) & ~a) | ( z & a & b & ~t) | ( b & (c | (d | ~c | (t & a & b)))))"
    str_formula = " (a & b) | (c | d) | (c & f) | (g & ~c) | (i & j & k) | z"

    varA = Symbol("A")
    varB = Symbol("B")
    f = And([varA, Not(varB)])
    print(f)
    f = f.simplify()
    print(f)
    cnfizer = CNFizer(environment=get_env())
    cnf = cnfizer.convert(f)
    print(cnf)
    for clause in cnf:
        print(clause)

    ######################
    print("PART 222222 !")
    
    hello = [Symbol(s, INT) for s in "hello"]
    world = [Symbol(s, INT) for s in "world"]
    letters = set(hello+world)
    domains = And([And(GE(l, Int(1)),
                    LT(l, Int(10))) for l in letters])

    sum_hello = Plus(hello) # n-ary operators can take lists
    sum_world = Plus(world) # as arguments
    problem = And(Equals(sum_hello, sum_world),
                Equals(sum_hello, Int(25)))
    formula = And(domains, problem)

    print("Serialization of the formula:")
    print(formula)

    model = get_model(formula)
    if model:
        print(model)
    else:
        print("No solution found")


if __name__ == "__main__":
    main()