import random

def sorter(l):
    if len(l)<2:
        return l
    ln = len(l[0])
    slist = []
    slist.append(l[0])
    l.remove(l[0])
    for e in l:
        print("========================")
        print("Looking for new entry : ",e)
        print("len slist : ",len(slist))
        rmlist = []
        toadd = 1
        for e2 in slist:
            ret = cmp(e,e2,ln)
            if ret == 1:
                rmlist.append(e2)
                print("Removed old entry")
            if ret == 2:
                print("Entry not better")
                toadd = 2
        for erm in rmlist:
            slist.remove(erm)
        if toadd==1:
            slist.append(e)
            print("Added that entry")
        else:
            print("NOT Added that entry")
    return slist

# return 1 : l1 should replace that entry
# return 2 : l1 not better than l2
# return 3 : l1 new possible best path
def cmp(l1,l2,ln):
    print("Cmp l1: ",l1)
    print("Cmp l2: ",l2)
    flag1 = 1
    flag2 = 1
    for i in range(0,ln):
        # Can not be worse
        if l1[i]==False and l2[i]==True:
            flag2 = 0
        # Not better OU autre sol 
        if l1[i]==True and l2[i]==False:
            flag1 = 0
    if flag1:
        print("should replace that entry")
        return 1
    if flag2:
        print("l1 not better than l2")
        return 2
    print("l1 new possible best path")   
    return 3


Test_instance = []
Test_instance.append([False, True, False, True])
Test_instance.append([True, False, False, True])
Test_instance.append([False, False, False, True])
Test_instance.append([False, False, True, False])
Test_instance.append([False, True, True, False])
Test_instance.append([True, True, True, False])
Test_instance.append([True, True, False, False])

random.shuffle(Test_instance)

print(sorter(Test_instance))