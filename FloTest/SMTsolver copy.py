from sympy import *
from pysat.solvers import Glucose3
import os
import time
from pysmt.shortcuts import Symbol, And, Or, Array, Ite, Equals, TRUE, ForAll, Iff, GE, LT, Plus, Equals, Int, get_model, Not, get_env, is_sat, Real, Min
from pysmt.typing import INT, REAL
from pysmt.rewritings import CNFizer
from pysmt.parsing import parse, HRParser

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
    #print("DDDDDDDDDDDDDDDDDDDDDDDDdddd")

def cost_array(symbol_list):
    ret_list = []
    for symbol in symbol_list:
        #print(symbol)
        #print(symbol.is_symbol())
        print(symbol.symbol_name())
        '''
        if Iff(symbol == TRUE(), Int(2)):
            #ret_list.append(Ite(Equals(symbol, TRUE), Int(2), Int(0)))
            ret_list.append(Int(2))
        else:
            ret_list.append(Int(4))
        '''
        return Iff(symbol == TRUE(), TRUE())
    #print(ret_list)
    #return ret_list
    #print("DDDDDDDDDDDDDDDDDDDDDDDDdddd")

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
    world = [Symbol(s, INT) for s in "worl"]
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

    print("##")

    str_formula = " (a & b) | c "

    p = HRParser()

    #a,b,c,d = (Symbol(v) for v in "abcd")

    print("@@")

    '''
    glob = {}
    exec('from sympy.core import Symbol', glob) # ok for I, E, S, N, C, O, or Q
    formula = parse_expr(str_formula, global_dict=glob)
    cnf_formula = to_cnf(formula)
    '''

    #formula = p.parse(str_formula)

    print("(((())))")

    '''
    problem = And(
                Equals(a, Real(10)),
                Equals(b, Real(20)),
                Equals(c, Real(40))
            )
    '''


    #f = ForAll([x], Or(LT(x, Real(5.0)), GE(Plus(x, y, z), Real((17,2))))) # (17,2) ~> 17/2
    #print("f := %s" % f)
    #f := (forall x . ((x < 5.0) | (17/2 <= (x + y + z))))

    #a, b = [Symbol(s, INT) for s in "ab"]
    #problem = And(Equals(a, Int(10)),Equals(b, cost(b)))
    #problem = And(problem, Min(a,b))
    #problem = Min(a,b)

    x = Symbol("x")
    y = Symbol("y")
    problem = Or(x,y)
    arr = [x, y]

    A0 = Symbol("A0", INT)

    # FORALL ALL SUM IN MODEL
    # CHECK WHICH IS LOWEST

    sum_total = Plus(cost(x), cost(y))

    problem = And(problem, Iff(sum_total <= sum_total, problem))

    print(problem)

    print("§§§§§§§")

    full_cost = Int(0) #Plus(cost_array(arr))

    FFF = ForAll(arr, full_cost <= Int(10))

    print(FFF)

    #formula = parse(str_formula)

    print(formula)
    print(problem)

    print(get_model(problem))
    ##print(is_sat(cnf_formula))

    #add cost function
    #boolean -> iff and minimize cost

    z = Array(INT, Int(0)) #mauvaise idée
    print(z)


    X1 = Symbol("X1")
    SOL = Symbol("SOL", INT)
    m = Ite(Iff(X1,TRUE()), Int(1), Int(3))
    print(m)
    m2 = Plus(m, m)
    print(m2)
    fin = And(Not(X1), Equals(SOL,m2))
    print(fin)
    print(get_model(fin))

    T = Symbol("T")
    T = TRUE()
    #T2 = Symbol("T2")
    #T2 = TRUE()
    hhhh = Iff(T,TRUE())
    print(hhhh)

if __name__ == "__main__":
    main()