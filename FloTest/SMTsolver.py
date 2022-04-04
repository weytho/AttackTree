from sympy import *
from pysat.solvers import Glucose3
import os
import time
from pysmt.shortcuts import Solver, Symbol, And, Or, Array, Ite, Equals, TRUE, ForAll, Exists, Iff, GT, GE, LE, LT, Plus, Equals, Int, get_model, Not, get_env, is_sat, Real, Min
from pysmt.shortcuts import qelim, is_sat
from pysmt.typing import INT, REAL
from pysmt.rewritings import CNFizer
from pysmt.parsing import parse, HRParser
from pysmt.oracles import get_logic

def cost(symbol):
    #ret_list = []
    #for symbol in symbol_list:
    print(symbol)
    print(symbol.is_symbol())
    print(symbol.symbol_name())
    if symbol == "x":
        return Int(2)
    else:
        return Int(4)

def cost_array(symbol_list):
    ret_list = []
    for symbol in symbol_list:

        return Iff(symbol == TRUE(), TRUE())

def main():

    x = Symbol("x")
    y = Symbol("y")
    problem = Or(x,y)
    arr = [x, y]

    print("§§§§§§§")

    full_cost = Int(0) #Plus(cost_array(arr))

    print("@@@@@@@########")

    X1 = Symbol("X1")
    X2 = Symbol("X2")
    SOL = Symbol("SOL", INT)
    SOL2 = Symbol("SOL2", INT)

    m = Ite(X1, Int(1), Int(0))
    print(m)
    n = Ite(X2, Int(2), Int(0))
    print(n)

    m2 = Plus(m, n)
    print(m2)

    problem = Or(X1,X2)

    fin = And(problem, Equals(SOL, m2))
    print(fin.serialize())
    print(get_model(fin))


    F = Symbol("F", INT)
    FFF = ForAll([F], And(LE(F,F), GT(F, Int(0))))
    print(FFF)

    print(get_model(FFF))



    F = Symbol("F", INT)
    F3 = Symbol("F3", INT)
    cond = And(Equals(F, Int(10)), Equals(F, Plus(F3, Int(100))))
    FF = ForAll([F], cond)
    print(FF)

    #Fourier-Motzkin or Loos-Weisspfenning
    qf_f = qelim(FF, solver_name="z3")

    print("elim : " + str(qf_f))

    print(get_model(FF))

    target_logic = get_logic(FF)
    print("Target Logic: %s" % target_logic)

    FFF = ForAll([SOL],And( fin, LE(SOL2, SOL)) )
    print(FFF)
    FFF = Exists([SOL2], And(Equals(SOL2, m2), FFF))
    print(FFF.serialize())
    qf_f = qelim(FFF, solver_name="z3")
    print("elim : " + str(qf_f))

    print(get_model(qf_f))


    T = Symbol("T", INT)
    T2 = Symbol("T2", INT)

    form1 = ForAll([T], And( GT(T, Int(0)), LE(T2, T) ))
    print(form1)
    form1 = Exists([T2], And( GE(T2, Int(0)), form1))

    print(form1.serialize())
    qf_f = qelim(form1, solver_name="z3")
    print("elim : " + str(qf_f))

    print(get_model(qf_f))

if __name__ == "__main__":
    main()