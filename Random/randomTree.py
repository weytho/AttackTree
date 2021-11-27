import math
import sys
import random

def nodeGeneration(txt, costs, node, depth, maxdepth, branching_factor, first):

    rng = random.randint(0,maxdepth)
    # this is a leaf
    if rng < depth:
        if first !=0:
            costs += "\n"
        costs += node+":"+str(random.randint(1,10))
        return txt,costs,1
    if depth!=0:
        txt += "\n"
    # leaf logic
    rnglogic = random.randint(1,3)
    txt += node
    if rnglogic == 1:
        txt += "-OR->"
    elif rnglogic == 2:
        txt += "-AND->"
    else:
        txt += "-SAND->"
    # leaf child
    rngchild = random.randint(2,branching_factor)
    txt += "{"
    child = [node+str(i) for i in range(1,rngchild+1)]
    for i in range(0,rngchild):
        txt += child[i]
        if i!=rngchild-1:
            txt += ","
    txt += "}"
    # Next child
    if depth == maxdepth:
        for i in range(0,rngchild):
            if first !=0:
                costs += "\n"
            first = 1
            costs += child[i]+":"+str(random.randint(1,10))
        return txt,costs,1
    else:
        for i in range(0,rngchild):
            txt,costs,first = nodeGeneration(txt,costs,child[i],depth+1,maxdepth,branching_factor,first)
    return txt,costs,first

# Initialization
maxdepth = 3
branching_factor = 2
if len(sys.argv)>=3:
    maxdepth = int(sys.argv[1])
    branching_factor = int(sys.argv[2])
maxdepth = max(1,maxdepth)
branching_factor = max(2,branching_factor)
ret = """"""
costs = """"""
string,costs,first = nodeGeneration(ret,costs,"node",0,maxdepth, branching_factor,0)
print(string)
print(costs)