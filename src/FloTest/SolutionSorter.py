# This solution sorter reduce the solution space by removing non minimal solutions
# @param l : The list of solutions to reduce
def sorter(l):
    if len(l)<2:
        return l
    ln = len(l[0])
    slist = []
    slist.append(l[0])
    for e in l[1:]:
        rmlist = []
        toadd = 1
        for e2 in slist:
            ret = cmp(e,e2,ln)
            if ret == 1:
                rmlist.append(e2)
            if ret == 2:
                toadd = 2
        for erm in rmlist:
            slist.remove(erm)
        if toadd==1:
            slist.append(e)
    return slist

# Compare two solutions 
# return 1 : l1 should replace old entry l2
# return 2 : l1 is not better than entry l2
# return 3 : l1 is a new possible best path
# @param l1 : The new entry solution to compare
# @param l2 : The old entry solution to compare with
# @param ln : The length of any solution 
def cmp(l1,l2,ln):
    flag1 = 1
    flag2 = 1
    for i in range(0,ln):
        # Can not be worse
        if l1[i]=='False' and l2[i]=='True':
            flag2 = 0
        # Not better OU autre sol 
        if l1[i]=='True' and l2[i]=='False':
            flag1 = 0
    if flag1:
        return 1
    if flag2:
        return 2
    return 3

if __name__ == "__main__":
    test = []
    test.append(['True', 'False', 'False', 'True'])
    test.append(['True', 'True', 'False', 'True'])
    test.append(['False', 'False', 'True', 'False'])
    test.append(['True', 'False', 'True', 'False'])
    test.append(['True', 'False', 'True', 'True'])
    test.append(['True', 'True', 'True', 'False'])

    print(sorter(test))

    test2 = []
    test2.append(['True', 'False', 'False'])
    test2.append(['False', 'False', 'True'])
    test2.append(['False', 'True', 'False'])
    test2.append(['True', 'False', 'True'])
    test2.append(['False', 'True', 'True'])
    test2.append(['True', 'True', 'False'])
    test2.append(['True', 'True', 'True'])

    print(sorter(test2))