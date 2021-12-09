from sympy import *
from sympy.parsing.sympy_parser import parse_expr
from sympy.logic.utilities.dimacs import load
from pysat.solvers import Glucose3


glob = {}
exec('from sympy.core import Symbol', glob)

list_var = ['E', 'I', 'S', 'N', 'C', 'O', 'Q', 'lol12']



dict_var = {}
dict_index = {}
i = 1
for v in list_var:
    dict_var[v] = i
    dict_index[i] = v
    i = i + 1

print(dict_var)
print(dict_index)

str0 = "( E & I ) | ( S | N ) & ( C & O & Q & lol12 )"

str2 = to_cnf(parse_expr(str0, global_dict=glob))

print(str2)

list_and = str2.args

print(list_and)

g = Glucose3()

for x in list_and:
    list_or = x.args
    l = []
    for var in list_or:
        print(var)
        #print(type(var))
        val = str(var)
        l.append(dict_var[val])
    print(l)
    g.add_clause(l)

print(g.solve())
print(g.get_model())

for m in g.enum_models():
    print(m)