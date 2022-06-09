##
# @file
# Solve the boolean formula
#
from json.encoder import INFINITY
from pysat.solvers import Glucose3
from sympy import *
# From folder

def sat_solver(formula, list_var, assumptions=[], max_val=20, to_print=True):
    if to_print:
        print("####################### SAT SOLVER (Glucose3) #########################")
        print(formula)
        #print(list_var)
    
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

    else:
        l = []
        val = str(formula)
        l.append(dict_var[val])
        g.add_clause(l)

    b = g.solve(assumptions=assumptions)
    print(b)
    sol_array = []

    if(b):
        # if no limit -> limit to 20 for performance issue
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

if __name__ == "__main__":

    list_var = ["node", "node2"]

    formula = " ( ( node ) & ( node2 ) ) "
    #formula = " ( node & node2 ) "

    glob = {}
    exec('from sympy.core import Symbol', glob) # ok for I, E, S, N, C, O, or Q
    parsed_formula = parse_expr(formula, global_dict=glob)
    print("PARSED")
    print(parsed_formula)
    cnf_formula = to_cnf(parsed_formula)
    print("CNF")
    print(cnf_formula)

    print("SAT SOLVER")
    print(sat_solver(cnf_formula, list_var, [], -1))