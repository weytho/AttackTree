from PyQt5.QtCore import QTextDecoder, QUrl, Qt
import matplotlib.pyplot as plt
import networkx as nx
from matplotlib.backends.backend_qt5 import NavigationToolbar2QT
from networkx.drawing import layout
from pyvis.network import Network
import plotly.graph_objects as go
from PyQt5.QtWebEngineWidgets import QWebEngineView
#import PyQtWebEngine
from PyQt5.QtWidgets import QApplication, QMainWindow
from plotly.graph_objects import Figure, Scatter
import plotly
import numpy as np
import pyvis

from netgraph import Graph, InteractiveGraph, EditableGraph


class MainWindow(QMainWindow):

    def __init__(self):

        super(MainWindow, self).__init__()

        plot_widget = QWebEngineView()
        #plot_widget.setContextMenuPolicy(Qt.NoContextMenu)

        local_url = QUrl.fromLocalFile('/home/flo/Desktop/Github/AttackTree/nxtest.html')

        plot_widget.load(local_url)

        self.setCentralWidget(plot_widget)

#plt.figure(figsize=(20,20), dpi=
# 100)
#plt.figure(figsize=(20,12)
# , dpi=100)

plt.figure(figsize=(18,18))

g = nx.DiGraph()
ln = [('node', {'type': 'OR', 'leaf': 0, 'root': 1, 'cost': 0}), ('node1', {'type': 'SAND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node11', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node12', {'type': 'AND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node121', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node122', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node123', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node13', {'type': 'AND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node131', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node132', {'type': 'AND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node1321', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node1322', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node2', {'type': 'SAND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node21', {'type': 'AND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node211', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node212', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node22', {'type': 'SAND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node221', {'type': 'SAND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node2211', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node2212', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node222', {'type': 'AND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node2221', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node2222', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node223', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node23', {'type': 'AND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node231', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node232', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node233', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node3', {'type': 'SAND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node31', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node32', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0})]
le = [('node', 'node1'), ('node1', 'node11'), ('node1', 'node12'), ('node12', 'node121'), ('node12', 'node122'), ('node12', 'node123'), ('node1', 'node13'), ('node13', 'node131'), ('node13', 'node132'), ('node132', 'node1321'), ('node132', 'node1322'), ('node', 'node2'), ('node2', 'node21'), ('node21', 'node211'), ('node21', 'node212'), ('node2', 'node22'), ('node22', 'node221'), ('node221', 'node2211'), ('node221', 'node2212'), ('node22', 'node222'), ('node222', 'node2221'), ('node222', 'node2222'), ('node22', 'node223'), ('node2', 'node23'), ('node23', 'node231'), ('node23', 'node232'), ('node23', 'node233'), ('node', 'node3'), ('node3', 'node31'), ('node3', 'node32')]
#ln = [('node', {'lvl': 0}),('node1', {'lvl': 1}),('node2', {'lvl': 1}),('node11', {'lvl': 2}),('node12', {'lvl': 2})]
#le = [('node', 'node1'),('node', 'node2'),('node2', 'node11'),('node2', 'node12')]

g.add_nodes_from(ln)
g.add_edges_from(le)

labels = {n: n for n in g}

#g.graph_attr.update(size="10,6")

pos = nx.nx_agraph.pygraphviz_layout(g, prog='dot') #, args='-Gsize=100,60\! -Gdpi=100')
print(pos)
#nx.draw_networkx_edges(g, pos, connectionstyle='arc3, rad=0.0')

#nx.draw_networkx_labels(g, pos, labels, font_size=14, font_color='black', font_family='sans-serif', bbox=dict(facecolor="white", edgecolor='black', boxstyle='round,pad=0.8'))
#plt.axis('off')

nt = Network('600px', '1000px')

nt.toggle_physics(False)

for (n, d) in ln:
    nt.add_node(n_id=n, x=pos[n][0], y=-pos[n][1], label=n)

for (n, d) in le:
    nt.add_edge(n, d)

nt.save_graph('nxtest.html')

#plot_instance = InteractiveGraph(list_pos)
#plt.show()

#nt.from_nx(g)
#nt.enable_physics(True)
#nt.show('nxtest.html')


#print(nt)

#nx.drawing.nx_pydot.write_dot(g,'test.dot')

app = QApplication([])
window = MainWindow()
window.show()
app.exec_()

print("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@")
#https://stackoverflow.com/questions/21978487/improving-python-networkx-graph-layout
#https://github.com/matplotlib/matplotlib/issues/13043

#