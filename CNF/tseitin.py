from sympy import *
from pysat.solvers import Glucose3
import os
import time

# https://en.wikipedia.org/wiki/Tseytin_transformation

def sat_solver(formula, list_var, assumptions=[]):

        if formula == None:
            return

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

        if(b):
            model = g.get_model()
            print(model)
            for m in g.enum_models(assumptions=assumptions):
                pass
                #print(m)
    

def recur_formula(formula, list_subformulas, dict_subs, var_cnt, set_var):
    #print("Current Formula : " + str(formula))
    if(type(formula) is Symbol):
        set_var.add(str(formula))
        return var_cnt

    dict_subs[formula] = Symbol("%" + str(var_cnt))
    var_cnt = var_cnt + 1

    if(type(formula) is And):
        list_subformulas.append(formula)
        list_and = formula.args
        for x in list_and:
            var_cnt = recur_formula(x, list_subformulas, dict_subs, var_cnt, set_var)

    elif(type(formula) is Or):
        list_subformulas.append(formula)
        list_or = formula.args
        for x in list_or:
            var_cnt = recur_formula(x, list_subformulas, dict_subs, var_cnt, set_var)

    elif(type(formula) is Not):
        list_subformulas.append(formula)
        arg_not = formula.args[0]

        if(type(arg_not) is And):
            list_and = arg_not.args
            for x in list_and:
                var_cnt = recur_formula(x, list_subformulas, dict_subs, var_cnt, set_var)

        elif(type(arg_not) is Or):
            list_or = arg_not.args
            for x in list_or:
                var_cnt = recur_formula(x, list_subformulas, dict_subs, var_cnt, set_var)

        else:
            var_cnt = recur_formula(arg_not, list_subformulas, dict_subs, var_cnt, set_var)
    
    return var_cnt

def tseitin(formula):

    # Notation new varibles : %1 %2 %3 ...
    list_subformulas = []
    var_cnt = 0
    dict_subs = {}
    set_var = set()

    recur_formula(formula, list_subformulas, dict_subs, var_cnt, set_var)

    list_new_var = list_subformulas[:]

    index_expr = []

    for index in range(len(list_new_var)):
        index_expr.append(dict_subs[list_new_var[index]])
        list_new_var[index] = list_new_var[index].subs({k: v for k, v in dict_subs.items() if k != list_new_var[index]})

    list_and_cnf = []
    # Add the whole substitution !
    list_and_cnf.append([index_expr[0]])

    for val, expr in zip(index_expr, list_new_var):
        if(type(expr) is And):
            list_1 = []
            for x in expr.args:
                list_1.append(Not(x))
                list_and_cnf.append([x, Not(val)])
            list_1.append(val)
            list_and_cnf.append(list_1)

        elif(type(expr) is Or):
            list_1 = []
            for x in expr.args:
                list_1.append(x)
                list_and_cnf.append([Not(x), val])
            list_1.append(Not(val))
            list_and_cnf.append(list_1)

        elif(type(expr) is Not):
            arg_not = expr.args[0]

            if(type(arg_not) is And):
                list_1 = []
                for x in arg_not.args:
                    list_1.append(Not(x))
                    list_and_cnf.append([x, val])
                list_1.append(Not(val))
                list_and_cnf.append(list_1)

            elif(type(arg_not) is Or):
                list_1 = []
                for x in arg_not.args:
                    list_1.append(x)
                    list_and_cnf.append([Not(x), Not(val)])
                list_1.append(val)
                list_and_cnf.append(list_1)

            else:
                list_and_cnf.append([Not(arg_not), Not(val)])
                list_and_cnf.append([arg_not, val])

    list_and_cnf = [Or(*l) for l in list_and_cnf]
    list_and_cnf = And(*list_and_cnf)

    return list_and_cnf, set_var, index_expr


# pas E I N O Q en première lettre ! 
#str_formula = "(a & b) | (~(a & c) & (a | c | d))"
str_formula = "(~((p | q) & r)) | (~s) "
str_formula = "( ( ( node000 | node001 ) & node01 & ( ( node0200 & node0201 & node0202 & ( node000 | node001 ) ) | ( node0210 & node0211 & node0212 & node000 ) | node01 ) ) | ( ( node100 | node101 ) & node11 & ( node120 & ( node1210 | node1211 ) | ( node1220 & node1221 & node11 ) & node01 ) ) | ( ( node200 & node201 ) | node21 | node001 ) )"
#str_formula = "( a | (c & (d | z | t) & ~a) | ( z & a & b & ~t) | ( b & (c | (d | ~c | (t & a & b)))))"
#str_formula = " (a & b) | (c | d) | (c & f) | (g & ~c) | (i & j & k) | z"

glob = {}
exec('from sympy.core import Symbol', glob) # ok for I, E, S, N, C, O, or Q
formula = parse_expr(str_formula, global_dict=glob)

print(formula)
print("SYMPY CNF")
start = time.time()
cnf_formula = to_cnf(formula)
end = time.time()
print(end - start)

print("TSEITIN CNF")
start = time.time()
list_and_cnf, set_var, index_expr = tseitin(formula)
end = time.time()
print(end - start)

print("OUTPUT")
print(list_and_cnf)
print(cnf_formula)

list_var = list(set_var) + [str(l) for l in index_expr]

print(list_var)

print("Solve SYMPY CNF")
start = time.time()
sat_solver(cnf_formula, list(set_var))
end = time.time()
print(end - start)

print("Solve TSEITIN CNF")
start = time.time()
sat_solver(list_and_cnf, list_var)
end = time.time()
print(end - start)
