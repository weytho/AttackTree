import seaborn as sns
import pandas as pd
import pylab as plt
import numpy as np
import itertools
import random
import time

# https://davefernig.com/2018/05/07/solving-sat-in-python/

def brute_force(cnf):
    literals = set()
    for conj in cnf:
        for disj in conj:
            literals.add(disj[0])

    literals = list(literals)
    n = len(literals)
    
    for seq in itertools.product([True,False], repeat=n):
        #print(seq)
        a = set(zip(literals, seq))
        #print(a)

        if all([bool(disj.intersection(a)) for disj in cnf]):
            print(True)
            print(a)
            #return True, a

    return False, None

def random_kcnf(n_literals, n_conjuncts, k=3):
    result = []
    for _ in range(n_conjuncts):
        conj = set()
        for _ in range(k):
            index = random.randint(0, n_literals)
            conj.add((
                str(index).rjust(10, '0'),
                bool(random.randint(0,2)),
            ))
        result.append(conj)
    return result


print("GOOO")

'''
for n_literals in range(4):
    for _ in range(100):
        n_conjuncts = random.randint(0, n_literals*6)
        s = random_kcnf(n_literals, n_conjuncts)
        brute_force(s)
'''

s = random_kcnf(2, 2)
s = [{('c', True)}, {('d', True), ('e', True)}]
# (c) and (b or e)

print(s)
x, y = brute_force(s)
print(x)
print(y)