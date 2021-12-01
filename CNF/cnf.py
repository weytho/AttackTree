from sympy import *

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
print(to_cnf("(a & flo) | (thomas & a)"))

print(to_cnf("(B & s) | (M & a) | (g & i)"))
