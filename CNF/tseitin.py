from sympy import *
import os

def recur_formula(formula, list_subformulas, dict_subs, var_cnt):
    print("Current Formula : " + str(formula))
    if(type(formula) is Symbol):
        return
    dict_subs[formula] = Symbol("%" + str(var_cnt))

    if(type(formula) is And):
        list_subformulas.append(formula)
        list_and = formula.args

        for x in list_and:
            var_cnt = var_cnt + 1
            recur_formula(x, list_subformulas, dict_subs, var_cnt)

    elif(type(formula) is Or):
        list_subformulas.append(formula)
        list_or = formula.args

        for x in list_or:
            var_cnt = var_cnt + 1
            recur_formula(x, list_subformulas, dict_subs, var_cnt)

    elif(type(formula) is Not):
        list_subformulas.append(formula)
        arg_not = formula.args[0]

        if(type(arg_not) is And):
            list_and = arg_not.args

            for x in list_and:
                var_cnt = var_cnt + 1
                recur_formula(x, list_subformulas, dict_subs, var_cnt)

        elif(type(arg_not) is Or):
            list_or = arg_not.args

            for x in list_or:
                var_cnt = var_cnt + 1
                recur_formula(x, list_subformulas, dict_subs, var_cnt)

        else:
            var_cnt = var_cnt + 1
            recur_formula(arg_not, list_subformulas, dict_subs, var_cnt)

# pas E I N O Q en première lettre ! 
print(to_cnf("(a & b) | (~c & a & d)"))

str_formula = "(a & b) | (~(a & b) & (a | c | d))"

glob = {}
exec('from sympy.core import Symbol', glob) # ok for I, E, S, N, C, O, or Q
formula = parse_expr(str_formula, global_dict=glob)

print(formula)

cnf_formula = to_cnf(formula)

print(cnf_formula)

list_var = ["a","b","c","d"]

# Notation new varibles : %1 %2 %3 ...

list_subformulas = []
var_cnt = 0
dict_subs = {}

recur_formula(formula, list_subformulas, dict_subs, var_cnt)

print(list_subformulas)
for i in list_subformulas:
    print(i)

list_new_var = list_subformulas[:]

print("")
print(dict_subs)
print("")

'''
for index in range(len(list_new_var)):
    list_args = list_new_var[index].args
    for a in list_args:
        if a in list_new_var:
            list_new_var[index] = list_new_var[index].subs(a,dict_subs[a])
'''
index_expr = []

for index in range(len(list_new_var)):
    index_expr.append(dict_subs[list_new_var[index]])
    list_new_var[index] = list_new_var[index].subs({k: v for k, v in dict_subs.items() if k != list_new_var[index]})

print(index_expr)
print(list_new_var)
for i in list_new_var:
    print(i)

final_cnf = None
list_and_cnf = []

for expr in list_new_var:
    if(type(expr) is And):
        pass

    elif(type(expr) is Or):
        pass

    elif(type(expr) is Not):
        arg_not = formula.args[0]

        if(type(arg_not) is And):
            pass

        elif(type(arg_not) is Or):
            pass

        else:
            pass

list = [Symbol("A"), Symbol("DDD"), Symbol("ZZZZZZ")]
print(And(*list))
