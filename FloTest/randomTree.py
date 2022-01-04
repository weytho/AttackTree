##
# @file
# Random Tree Generation with Grammar
#
import math
import sys
import random

##
# recursive tree generator 1
# This recursive generator will generate a simple tree using the grammar 
# The maxdepth and branchingfactor arguments will forge the global shape of the tree
# arguments : ----------------------
# Relations : the string of relations
# CounterMeasures : the string of CounterMeasures
# Properties : the string of Properties
# node : the string naming the parent of the node (used to gerenate its own name)
# depth : the actual depth of the recursive calls
# maxdepth : the maximum depth of the tree
# branching_factor : the maximu branching factor of each node
def nodeGeneration(Relations, CounterMeasures, Properties, node, depth, maxdepth, branching_factor):

    rng = random.randint(0,maxdepth)
    # this node is a leaf
    if rng < depth:
        Properties += "\n"+node+":{"+"cost = "+str(random.randint(1,10))+","+"prob = "+"1.0"+"}"
        if random.randint(0,10)<3 :
            CounterMeasures += "\nCM"+node+" ("+node+")"
        return Relations,CounterMeasures,Properties
    # node logic
    rnglogic = random.randint(1,3)
    Relations += "\n"+node
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
            Properties += "\n"+child[i]+":{"+"cost = "+str(random.randint(1,10))+","+"prob = "+"1.0"+"}"
            if random.randint(0,10)<3 :
                CounterMeasures += "\nCM"+child[i]+" ("+child[i]+")"
        return Relations,CounterMeasures,Properties
    else:
        for i in range(0,rngchild):
            Relations,CounterMeasures,Properties = nodeGeneration(Relations,CounterMeasures,Properties,child[i],depth+1,maxdepth,branching_factor)
    return Relations,CounterMeasures,Properties

##
# recursive tree generator 2
# This recursive generator will generate a simple tree using the grammar  
# The maxdepth and branchingfactor arguments will forge the global shape of the tree
# The generation is more complex and can generate shared childrens between the nodes
# (this function does not produce countermeasures)
# arguments : ----------------------
# NodeList : the list of nodes of the tree
# Relations : the string of relations
# Properties : the string of Properties
# node : the string naming the parent of the node (used to gerenate its own name)
# depth : the actual depth of the recursive calls
# maxdepth : the maximum depth of the tree
# branching_factor : the maximum branching factor of each node
def nodeGeneration2(NodeList, Relations, Properties, node, depth, maxdepth, branching_factor):

    rng = random.randint(0,maxdepth)
    NodeList.append(node)
    # this node is a leaf
    if rng < depth:
        Properties += "\n"+node+":{"+"cost = "+str(random.randint(1,10))+","+"prob = "+"1.0"+"}"
        return Relations,Properties
    # node logic
    rnglogic = random.randint(1,3)
    Relations += "\n"+node
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
    # Random shared children
    if random.randint(0,10)<8:
        #print("proba shared node! ")
        #print(NodeList)
        existingnode = random.choice(NodeList)
        cnt = 5
        while(existingnode in node and cnt > 0):
            existingnode = random.choice(NodeList)
            cnt-=1
        if cnt > 0:
            #print("Shared node! ")
            Relations += ","+existingnode
    Relations += "}"
    # node child
    if depth == maxdepth:
        for i in range(0,rngchild):
            NodeList.append(child[i])
            Properties += "\n"+child[i]+":{"+"cost = "+str(random.randint(1,10))+","+"prob = "+"1.0"+"}"
        return Relations,Properties
    else:
        for i in range(0,rngchild):
            Relations,Properties = nodeGeneration2(NodeList, Relations,Properties,child[i],depth+1,maxdepth,branching_factor)
    return Relations,Properties

##
# recursive countermeasure generator 2
# This recursive countermeasure generator will generate shared countermeasures with the list of node of the already generated tree 
# arguments : ----------------------
# NodeList : list of nodes of the generated tree
# CounterMeasures : the string of CounterMeasures
def CMGeneration2(NodeList, CounterMeasures):
    l = len(NodeList)
    if l == 0:
        return CounterMeasures
    if l == 1:
        CounterMeasures += "\nCM1"+" ("+NodeList[0]+")"
        return CounterMeasures
    if l == 2:
        CounterMeasures += "\nCM1"+" ("+NodeList[0]+","+NodeList[1]+")"
        return CounterMeasures
    nbrCM = round(l/3)
    #print(nbrCM)
    for i in range(1,nbrCM+1):
        CounterMeasures += "\nCM"+str(i)+" ("+random.choice(NodeList)+","+random.choice(NodeList)+")"
    return CounterMeasures


##
# recursive tree generator 3
# This recursive generator will generate a simple tree using the grammar  
# The maxdepth and branchingfactor arguments will forge the global shape of the tree
# The generation is more complex and can generate shared childrens between the nodes
# The generated tree can be inconsistent
# (this function does not produce countermeasures)
# arguments : ----------------------
# NodeList : the list of nodes of the tree
# Relations : the string of relations
# Properties : the string of Properties
# node : the string naming the parent of the node (used to gerenate its own name)
# depth : the actual depth of the recursive calls
# maxdepth : the maximum depth of the tree
# branching_factor : the maximum branching factor of each node
def nodeGeneration3(NodeList, Relations, Properties, node, depth, maxdepth, branching_factor):

    rng = random.randint(0,maxdepth)
    NodeList.append(node)
    # this node is a leaf
    if rng < depth:
        Properties += "\n"+node+":{"+"cost = "+str(random.randint(1,10))+","+"prob = "+"1.0"+"}"
        return Relations,Properties
    # node logic
    rnglogic = random.randint(1,3)
    Relations += "\n"+node
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
    # Random shared children
    if random.randint(0,10)<2:
        #print("proba shared node! ")
        #print(NodeList)
        existingnode = random.choice(NodeList)
        Relations += ","+existingnode
    Relations += "}"
    # node child
    if depth == maxdepth:
        for i in range(0,rngchild):
            NodeList.append(child[i])
            Properties += "\n"+child[i]+":{"+"cost = "+str(random.randint(1,10))+","+"prob = "+"1.0"+"}"
        return Relations,Properties
    else:
        for i in range(0,rngchild):
            Relations,Properties = nodeGeneration3(NodeList, Relations,Properties,child[i],depth+1,maxdepth,branching_factor)
    return Relations,Properties

##
# recursive countermeasure generator 3
# This recursive countermeasure generator will generate shared countermeasures with the list of node of the already generated tree 
# arguments : ----------------------
# NodeList : list of nodes of the generated tree
# CounterMeasures : the string of CounterMeasures
def CMGeneration3(NodeList, CounterMeasures):
    l = len(NodeList)
    if l == 0:
        return CounterMeasures
    if l == 1:
        CounterMeasures += "\nCM1"+" ("+NodeList[0]+")"
        return CounterMeasures
    if l == 2:
        CounterMeasures += "\nCM1"+" ("+NodeList[0]+","+NodeList[1]+")"
        return CounterMeasures
    nbrCM = round(l/3)
    #print(nbrCM)
    for i in range(1,nbrCM+1):
        node1 = random.choice(NodeList)
        node2 = random.choice(NodeList)
        while node2 == node1:
            node2 = random.choice(NodeList)
        CounterMeasures += "\nCM"+str(i)+" ("+node1+","+node2+")"
    return CounterMeasures

##
# Main function to call to generate a random tree with the grammar
# arguments : ----------------------
# maxdepth : the maximum depth of he tree
# branching_factor : the branching factor of each node
# complexity = 1 : relations + Countermeasures + Properties
# complexity = 2 : 1 + shared child + shared CM
# complexity = 3 : 2 + probably inconsistent tree
def TreeGen(maxdepth, branching_factor, complexity):
    maxdepth = max(1,maxdepth)
    branching_factor = max(2,branching_factor)
    Relations = """RELATIONS"""
    CounterMeasures = """COUNTERMEASURES"""
    Properties = """PROPERTIES"""
    if complexity == 1:
        Relations,CounterMeasures,Properties = nodeGeneration(Relations,CounterMeasures,Properties,"node",0,maxdepth, branching_factor)
    if complexity == 2:
        NodeList = []
        Relations,Properties = nodeGeneration2(NodeList,Relations,Properties,"node",0,maxdepth, branching_factor)
        CounterMeasures = CMGeneration2(NodeList,CounterMeasures)
    if complexity == 3:
        NodeList = []
        Relations,Properties = nodeGeneration3(NodeList,Relations,Properties,"node",0,maxdepth, branching_factor)
        CounterMeasures = CMGeneration3(NodeList,CounterMeasures)
    return Relations,CounterMeasures,Properties

maxdepth = 3
branching_factor = 2
if len(sys.argv)>=3:
        maxdepth = int(sys.argv[1])
        branching_factor = int(sys.argv[2])
maxdepth = max(1,maxdepth)
branching_factor = max(2,branching_factor)   
Relations = """RELATIONS"""
CounterMeasures = """COUNTERMEASURES"""
Properties = """PROPERTIES"""
NodeList = []
Relations,CounterMeasures,Properties = nodeGeneration(Relations,CounterMeasures,Properties,"node",0,maxdepth, branching_factor)

#Relations,Properties,first = nodeGeneration3(NodeList,Relations,Properties,"node",0,maxdepth, branching_factor,0)
#CounterMeasures = CMGeneration3(NodeList,CounterMeasures)

#print(Relations)
#print(CounterMeasures)
#print(Properties)

rel,cm,prop = TreeGen(2,3,3)
print(rel)
print(cm)
print(prop)