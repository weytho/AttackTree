from sympy.logic.boolalg import to_cnf
from sympy.logic.boolalg import Not
from sympy.parsing.sympy_parser import parse_expr
from pysat.solvers import Glucose3
glob = {}
exec('from sympy.core import Symbol', glob)

list_var = ['E', 'I', 'S', 'N', 'C', 'O', 'Q', 'lol12']
list_var = ['CM0', 'CM11', 'CM12', 'a', 'CM2', 'b', 'c', 'CM3', 'd', 'CM4', 'e', 'f']

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
str0 = "~ ( CM0 ) & (  ~ ( CM11 | CM12 ) & a & (  ~ ( CM2 ) & b & c ) &  ~ ( CM3 ) & ( d |  ~ ( CM4 ) & e ) & f )"
str2 = to_cnf(parse_expr(str0, global_dict=glob))
print(str2)

list_and = str2.args
print(list_and)

g = Glucose3()

for x in list_and:
    l = []
    list_or = x.args
    if not list_or:
        val = str(x)
        l.append(dict_var[val])
    else:
        for var in list_or:
            list_not = var.args
            if not list_not:
                val = str(var)
                l.append(dict_var[val])
            else:
                val = str(list_not[0])
                l.append(dict_var[val])
    print(l)
    g.add_clause(l)

# check if sat ok
print(g.solve()) # True
#get first model
model = g.get_model()
print(model) # [1, 2, -3, -4, -5, -6, -7, -8]

result = []
for n in model:
    if(n < 0):
        result.append("Not("+dict_index[-n]+")")
    else:
        result.append(dict_index[n])

print(result) # ['E', 'I', 'Not(S)', 'Not(N)', 'Not(C)', 'Not(O)', 'Not(Q)', 'Not(lol12)']

# get all models
for m in g.enum_models():
    print(m)