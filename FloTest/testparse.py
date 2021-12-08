from sympy.logic.boolalg import to_cnf
from sympy.parsing.sympy_parser import parse_expr
from sympy.core.sympify import sympify
from sympy import Symbol
import sympy

str = "( E & I ) | ( S | N )"
print(str)
print("1")

#I, E, S, N, C, O, or Q can't be used

list_ban = ['I', 'E', 'S', 'N', 'C', 'O', 'Q']

#sympy.var('I')
#sympy.var('E')
#sympy.var('S')
#sympy.var('N')

glob = {}
exec('from sympy.core import Symbol', glob)#
print(len(glob))
#exec('from sympy.core.function import arity, Function', glob)
print(len(glob))
#exec('from sympy.core.basic import Basic', glob)
print(len(glob))
#exec('from sympy.core.compatibility import iterable', glob)
print(len(glob))

#exec('from sympy.assumptions.ask import AssumptionKeys', glob)
print(len(glob))

#exec('from sympy.utilities.misc import filldedent, func_name', glob)
print(len(glob))

#exec('from keyword import iskeyword', glob)
print(len(glob))

#exec('from tokenize import (generate_tokens, untokenize, TokenError, NUMBER, STRING, NAME, OP, ENDMARKER, ERRORTOKEN, NEWLINE)', glob)
print(len(glob))

#exec('import ast', glob)
print(len(glob))

#exec('import unicodedata', glob)
print(len(glob))

#exec('from io import StringIO', glob)
print(len(glob))

str = "( A & B ) | ( E | H & type )"

str = "( E & I ) | ( S | N ) & ( C & O & Q & quit )"


for letter in list_ban:
   #print(glob[letter])
   #glob.pop(letter)
   pass

loc = {'I': Symbol("I"), 'E': Symbol("E"), 'S': Symbol("S"), 'N': Symbol("N")}


str_parsed = parse_expr(str, global_dict=glob)
#print(glob)

print(str_parsed)
print("2")

str2 = to_cnf(parse_expr(str, global_dict=glob))

print(str2)
print("3")