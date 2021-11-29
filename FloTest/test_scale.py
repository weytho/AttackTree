import matplotlib.pyplot as plt
import networkx as nx


plt.figure(figsize=(20,20)) #2000,2000
#plt.figure()

g = nx.DiGraph()
ln = [('node', {'type': 'OR', 'leaf': 0, 'root': 1, 'cost': 0}), ('node1', {'type': 'SAND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node11', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node12', {'type': 'AND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node121', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node122', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node123', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node13', {'type': 'AND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node131', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node132', {'type': 'AND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node1321', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node1322', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node2', {'type': 'SAND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node21', {'type': 'AND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node211', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node212', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node22', {'type': 'SAND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node221', {'type': 'SAND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node2211', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node2212', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node222', {'type': 'AND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node2221', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node2222', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node223', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node23', {'type': 'AND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node231', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node232', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node233', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node3', {'type': 'SAND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node31', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node32', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0})]
le = [('node', 'node1'), ('node1', 'node11'), ('node1', 'node12'), ('node12', 'node121'), ('node12', 'node122'), ('node12', 'node123'), ('node1', 'node13'), ('node13', 'node131'), ('node13', 'node132'), ('node132', 'node1321'), ('node132', 'node1322'), ('node', 'node2'), ('node2', 'node21'), ('node21', 'node211'), ('node21', 'node212'), ('node2', 'node22'), ('node22', 'node221'), ('node221', 'node2211'), ('node221', 'node2212'), ('node22', 'node222'), ('node222', 'node2221'), ('node222', 'node2222'), ('node22', 'node223'), ('node2', 'node23'), ('node23', 'node231'), ('node23', 'node232'), ('node23', 'node233'), ('node', 'node3'), ('node3', 'node31'), ('node3', 'node32')]
g.add_nodes_from(ln)
g.add_edges_from(le)

pos = nx.nx_agraph.graphviz_layout(g, prog='dot')
nx.draw_networkx_edges(g, pos, connectionstyle='arc3, rad=0.0')
plt.axis('off')
plt.show()

print("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@")
#https://stackoverflow.com/questions/21978487/improving-python-networkx-graph-layout
#https://github.com/matplotlib/matplotlib/issues/13043