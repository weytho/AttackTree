##
# @file

from collections import Counter

def get_global_proba(ln, le):
    # Compute Global Probability of Successful Attack

    full_dict = dict(ln)
    dict_proba = dict()
    dict_children = dict()
    dict_edges = dict()
    leaves = []
    for n in ln:
        if n[1]['type'] == "LEAF":
            leaves.append(n[0])
        dict_proba[n[0]] = n[1]['prob']
        dict_children[n[0]] = []

    for e in le:
        if e[1][:2] != "CM":
            dict_children[e[0]].append(e[1])
            dict_edges[e[1]] = e[0]

    for curr in leaves:
        while curr != None:
            n = full_dict[curr]
            if n['leaf'] == 1:
                pass
            elif n['type'] == 'OR':
                curr_proba = 1
                for child in dict_children[curr]:
                    curr_proba = curr_proba * (1 - dict_proba[child])
                dict_proba[curr] = 1 - curr_proba
            elif n['type'] == 'NOT':
                curr_proba = 1
                for child in dict_children[curr]:
                    curr_proba = 1 - dict_proba[child]
                dict_proba[curr] = curr_proba
            elif n['type'] == 'XOR':
                # substitution and distribution
                curr_proba = 0
                for child in dict_children[curr]:
                    curr_proba = (1 - curr_proba) * dict_proba[child] +  (1 - dict_proba[child]) * curr_proba
                dict_proba[curr] = curr_proba
            else:
                curr_proba = 1
                for child in dict_children[curr]:
                    curr_proba = curr_proba * dict_proba[child]
                dict_proba[curr] = curr_proba

            curr = dict_edges.get(curr, None)

    return dict_proba

def test():
    ln = [('node', {'type': 'AND', 'leaf': 0, 'root': 1, 'cost': 0, 'prob': 1.0, 'CM': 0, 'variable': 'node'}), ('node0', {'type': 'OR', 'leaf': 0, 'root': 0, 'cost': 0, 'prob': 1.0, 'CM': 0, 'variable': 'node0'}), ('node00', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 5, 'prob': 0.5, 'CM': 1, 'variable': 'node00'}), ('node01', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 2, 'prob': 0.3, 'CM': 0, 'variable': 'node01'}), ('node1', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 6, 'prob': 0.4, 'CM': 0, 'variable': 'node1'})]
    
    le = [('node', 'node0'), ('node0', 'node00'), ('node0', 'node01'), ('node', 'node1')]
    
    cnt = Counter(elem[1] for elem in le)
    print(cnt)
    has_subtree = cnt.most_common(1)
    print(has_subtree)
    if le and has_subtree[0][1] > 1:
        # Multiple parents 
        print("Has Shared Subtrees")
        return
    else:
        print("Compute global proba")
        global_prob = get_global_proba(ln, le)

if __name__ == "__main__":
    test()