from sympy import *
from sympy.parsing.sympy_parser import parse_expr
from sympy.logic.utilities.dimacs import load
from nnf import dimacs

f1 = """c  simple example
c Resolution: SATISFIABLE
c
p cnf 3 2
1 -3 0
2 3 -1 0
"""
str_formula = "(A | B) & (C | D)"

print(to_cnf(parse_expr(str_formula)))

str = str(to_cnf(parse_expr(str_formula)))

test = load(f1)
print(test)

#test2 = dimacs.dump(str)
#print(test2)