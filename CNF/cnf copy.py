from sympy import *
from sympy.parsing.sympy_parser import parse_expr
from sympy import sympify

def cnf(s,nbrvar):
    lst_symbol = [None] * nbrvar
    lst_char   = [None] * nbrvar
    for elem in s:
        if elem != ' ' and elem != '(' and elem != ')' and elem != '&' and elem != '|':
            done = 0
            for i in range(0,nbrvar):
                if (lst_symbol[i] == None or lst_symbol[i] == elem) and done == 0:
                    lst_symbol[i] = symbols(elem)
                    lst_char[i]   = symbols(elem)
                    done = 1
    print(lst_symbol)
    s = to_cnf(tran(lst_symbol,lst_char,s,0,len(s)))
    print(s)

def tran(lst_symbol,lst_char,s,min,max):
    print("min : "+str(min)+" max : "+str(max))
    if max-min == 1:
        char = s[min]
        cnt2 = 0
        for elem in lst_char:
            if elem == char:
                return lst_symbol[cnt2]
            cnt2+=1
    cnt = 0
    par = 0
    for elem in s:
        if cnt >= min and cnt < max:
            if elem != " ":
                if elem == "(":
                    par+=1
                elif elem == ")":
                    par-=1
                elif par == 0:
                    if elem == "|":
                        return Or(tran(lst_symbol,lst_char,s,min,cnt-1),tran(lst_symbol,lst_char,s,cnt+2,max))
        cnt+=1

def cnf2(str):
    print(to_cnf(str))


# pas E I N O Q en première lettre ! 
print(to_cnf("(a & flo) | (z & a)"))
print(to_cnf("(B & s) | (M & a)"))

list = ["n12", "n13", "n15"] 

list2 = [None] * 3
print(list2)

N1 = symbols("n12")
N2 = symbols("n13")
N3 = symbols("n15")

list2[0] = symbols(list[0])
list2[1] = symbols(list[1])
list2[2] = symbols(list[2])

print(to_cnf((list2[0] & list2[1]) | (list2[0] & list2[2])))

print(parse_expr("(~SE&D&RS)|(SE&SI)"))
print(to_cnf(parse_expr("(~SE&D&RS)|(SE&SI)")))

print(sympify("(~SE&D&RS)|(SE&SI)"))
print(to_cnf(sympify("(~SE&D&RS)|(SE&SI)")))


print(to_cnf(parse_expr("(a & flo) | (z & a)")))

print(to_cnf(parse_expr("(node112 & n12) | (node450 & n)")))

str = to_cnf(parse_expr("( CVE0 | ( ( node100 & ( node1010 | node1011 ) & ( node1020 & node1021 & node1022 ) ) | node11 ) )"))

print(str)
