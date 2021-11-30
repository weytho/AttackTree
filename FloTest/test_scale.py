import matplotlib.pyplot as plt
import networkx as nx
from matplotlib.backends.backend_qt5 import NavigationToolbar2QT
from networkx.drawing import layout
from pyvis.network import Network
import plotly.graph_objects as go
#from PyQt5.QtWebEngineWidgets import QWebEngineView
import PyQtWebEngine
from PyQt5.QtWidgets import QApplication, QMainWindow
from plotly.graph_objects import Figure, Scatter
import plotly
import numpy as np


class MainWindow(QMainWindow):

    def __init__(self):

        super(MainWindow, self).__init__()

        # we create html code of the figure
        #html = '<html><body>'
        #html += plotly.offline.plot(fig, output_type='div', include_plotlyjs='cdn')
        #html += '</body></html>'

        # we create an instance of QWebEngineView and set the html code
        plot_widget = QWebEngineView()
        plot_widget.setHtml('nx.html')

        # set the QWebEngineView instance as main widget
        self.setCentralWidget(plot_widget)

plt.figure(figsize=(20,20), dpi=100) #2000,2000
#plt.figure()

class NavigationToolbar(NavigationToolbar2QT):
    # only display the buttons we need
    toolitems = [t for t in NavigationToolbar2QT.toolitems if
                 t[0] in ('Home', 'Pan', 'Zoom')]

g = nx.DiGraph()
ln = [('node', {'type': 'OR', 'leaf': 0, 'root': 1, 'cost': 0}), ('node1', {'type': 'SAND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node11', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node12', {'type': 'AND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node121', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node122', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node123', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node13', {'type': 'AND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node131', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node132', {'type': 'AND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node1321', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node1322', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node2', {'type': 'SAND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node21', {'type': 'AND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node211', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node212', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node22', {'type': 'SAND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node221', {'type': 'SAND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node2211', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node2212', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node222', {'type': 'AND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node2221', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node2222', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node223', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node23', {'type': 'AND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node231', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node232', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node233', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node3', {'type': 'SAND', 'leaf': 0, 'root': 0, 'cost': 0}), ('node31', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0}), ('node32', {'type': 'LEAF', 'leaf': 1, 'root': 0, 'cost': 0})]
le = [('node', 'node1'), ('node1', 'node11'), ('node1', 'node12'), ('node12', 'node121'), ('node12', 'node122'), ('node12', 'node123'), ('node1', 'node13'), ('node13', 'node131'), ('node13', 'node132'), ('node132', 'node1321'), ('node132', 'node1322'), ('node', 'node2'), ('node2', 'node21'), ('node21', 'node211'), ('node21', 'node212'), ('node2', 'node22'), ('node22', 'node221'), ('node221', 'node2211'), ('node221', 'node2212'), ('node22', 'node222'), ('node222', 'node2221'), ('node222', 'node2222'), ('node22', 'node223'), ('node2', 'node23'), ('node23', 'node231'), ('node23', 'node232'), ('node23', 'node233'), ('node', 'node3'), ('node3', 'node31'), ('node3', 'node32')]
g.add_nodes_from(ln)
g.add_edges_from(le)

labels = {n: n for n in g}

pos = nx.nx_agraph.graphviz_layout(g, prog='dot')
nx.draw_networkx_edges(g, pos, connectionstyle='arc3, rad=0.0')

nx.draw_networkx_labels(g, pos, labels, font_size=14, font_color='black', font_family='sans-serif', bbox=dict(facecolor="white", edgecolor='black', boxstyle='round,pad=0.8'))
plt.axis('off')
#plt.show()

nx.write_gexf(g, "test.gexf")

nt = Network('500px', '500px', layout=True)

# populates the nodes and edges data structures
nt.from_nx(g)
#nt.enable_physics(True)
#nt.show('nx.html')

app = QApplication([])
window = MainWindow()
window.show()
app.exec_()

print("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@")
#https://stackoverflow.com/questions/21978487/improving-python-networkx-graph-layout
#https://github.com/matplotlib/matplotlib/issues/13043

'''
# edges trace
edge_x = []
edge_y = []
for edge in g.edges():
    x0, y0 = pos[edge[0]]
    x1, y1 = pos[edge[1]]
    edge_x.append(x0)
    edge_x.append(x1)
    edge_x.append(None)
    edge_y.append(y0)
    edge_y.append(y1)
    edge_y.append(None)

edge_trace = go.Scatter(
    x=edge_x, y=edge_y,
    line=dict(color='black', width=1),
    hoverinfo='none',
    showlegend=False,
    mode='lines')

# nodes trace
node_x = []
node_y = []
text = []
for node in g.nodes():
    x, y = pos[node]
    node_x.append(x)
    node_y.append(y)
    text.append(node)

node_trace = go.Scatter(
    x=node_x, y=node_y, text=text,
    mode='markers+text',
    showlegend=False,
    hoverinfo='none',
    marker=dict(
        color='pink',
        size=50,
        line=dict(color='black', width=1)))

# layout
layout = dict(plot_bgcolor='white',
                paper_bgcolor='white',
                margin=dict(t=10, b=10, l=10, r=10, pad=0),
                xaxis=dict(linecolor='black',
                            showgrid=False,
                            showticklabels=False,
                            mirror=True),
                yaxis=dict(linecolor='black',
                            showgrid=False,
                            showticklabels=False,
                            mirror=True))

# figure
fig = go.Figure(data=[edge_trace, node_trace], layout=layout)

fig.show()
'''