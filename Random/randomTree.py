import math
import sys
import random

def nodeGeneration(Relations, CounterMeasures, Properties, node, depth, maxdepth, branching_factor, first):

    rng = random.randint(0,maxdepth)
    # this node is a leaf
    if rng < depth:
        if first !=0:
            Properties += "\n"
        Properties += node+":{"+"cost = "+str(random.randint(1,10))+","+"prob = "+"1.0"+"}"
        if random.randint(0,10)<2 :
            CounterMeasures += "\nCM"+node+" ("+node+")"
        return Relations,CounterMeasures,Properties,1
    if depth!=0:
        Relations += "\n"
    # node logic
    rnglogic = random.randint(1,3)
    Relations += node
    if rnglogic == 1:
        Relations += " -OR-> "
    elif rnglogic == 2:
        Relations += " -AND-> "
    else:
        Relations += " -SAND-> "
    # node child
    rngchild = random.randint(2,branching_factor)
    Relations += "{"
    child = [node+str(i) for i in range(0,rngchild)]
    for i in range(0,rngchild):
        Relations += child[i]
        if i!=rngchild-1:
            Relations += ","
    Relations += "}"
    # Add CM if unlucky
    if random.randint(0,10)<1 :
        CounterMeasures += "\nCM"+node+" ("+node+")"
    # node child
    if depth == maxdepth:
        for i in range(0,rngchild):
            if first !=0:
                Properties += "\n"
            first = 1
            Properties += child[i]+":{"+"cost = "+str(random.randint(1,10))+","+"prob = "+"1.0"+"}"
            if random.randint(0,10)<2 :
                CounterMeasures += "\nCM"+child[i]+" ("+child[i]+")"
        return Relations,CounterMeasures,Properties,1
    else:
        for i in range(0,rngchild):
            Relations,CounterMeasures,Properties,first = nodeGeneration(Relations,CounterMeasures,Properties,child[i],depth+1,maxdepth,branching_factor,first)
    return Relations,CounterMeasures,Properties,first

# complexity 1 : only relations
# complexity 2 : 
# 
def TreeGen(maxdepth, branching_factor, complexity):
    maxdepth = max(1,maxdepth)
    branching_factor = max(2,branching_factor)
    Relations = """RELATIONS\n"""
    CounterMeasures = """COUNTERMEASURES"""
    Properties = """PROPERTIES\n"""
    if complexity == 1:
        Relations,CounterMeasures,Properties,first = nodeGeneration(Relations,CounterMeasures,Properties,"node",0,maxdepth, branching_factor,0)
    if complexity == 2:
        Relations,CounterMeasures,Properties,first = nodeGeneration2(Relations,CounterMeasures,Properties,"node",0,maxdepth, branching_factor,0)
    return Relations,CounterMeasures,Properties

maxdepth = 3
branching_factor = 2
if len(sys.argv)>=3:
        maxdepth = int(sys.argv[1])
        branching_factor = int(sys.argv[2])
maxdepth = max(1,maxdepth)
branching_factor = max(2,branching_factor)   
Relations = """RELATIONS\n"""
CounterMeasures = """COUNTERMEASURES"""
Properties = """PROPERTIES\n"""
Relations,CounterMeasures,Properties,first = nodeGeneration(Relations,CounterMeasures,Properties,"node",0,maxdepth, branching_factor,0)

print(Relations)
print(CounterMeasures)
print(Properties)