##
# @file
# Retrieve the ctype Structure representing the tree
# Retrieve the tree boolean formula
# Use a Sat-Solver to solve the formula
from json.encoder import INFINITY
from pysat.solvers import Glucose3
from sympy import *
# From folder

def sat_solver(formula, list_var, assumptions=[], max_val=20):
    print("####################### SAT SOLVER !!! (Glucose3) #########################")
    print(formula)
    print(list_var)
    
    if formula == None:
        return
    if max_val < 0:
        max_val = INFINITY

    dict_var = {}
    i = 1
    for v in list_var:
        dict_var[v] = i
        i = i + 1

    g = Glucose3()

    if(type(formula) is And):
        list_and = formula.args

        for x in list_and:
            l = []
            if(type(x) is Or):
                list_or = x.args

                for y in list_or:
                    if(type(y) is Not):
                        val = str(y.args[0])
                        l.append(-dict_var[val])
                    else:
                        val = str(y)
                        l.append(dict_var[val])

            elif(type(x) is Not):
                val = str(x.args[0])
                l.append(-dict_var[val])

            else:
                val = str(x)
                l.append(dict_var[val])

            g.add_clause(l)

    elif(type(formula) is Or):
        l = []
        list_or = formula.args

        for x in list_or:
            if(type(x) is Not):
                val = str(x.args[0])
                l.append(-dict_var[val])
            else:
                val = str(x)
                l.append(dict_var[val])
        g.add_clause(l)

    elif(type(formula) is Not):
        l = []
        val = str(formula.args[0])
        l.append(-dict_var[val])
        g.add_clause(l)

    b = g.solve(assumptions=assumptions)
    print(b)
    sol_array = []

    if(b):
        # TODO LIMIT TO 20 FOR PERFORMANCE ISSUE
        cnt = 0
        for m in g.enum_models(assumptions=assumptions):
            if cnt >= max_val :
                break
            sol_array.append(m)
            cnt += 1
        # Sort by fewest nbr of nodes taken
        sorter = lambda x: sum(1 for i in x if i >= 0)
        sol_array = sorted(sol_array, key=sorter)

    return list_var, sol_array