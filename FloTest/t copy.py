import sys
from PyQt5 import QtCore, QtGui
from PyQt5 import QtWidgets
from matplotlib.backends.backend_qt5 import NavigationToolbar2QT
# pyuic5 -o main_window_ui.py ui/main_window.ui
# https://stackoverflow.com/questions/44726280/include-matplotlib-in-pyqt5-with-hover-labels
# https://networkx.org/documentation/stable/reference/classes/digraph.html
# https://stackoverflow.com/questions/56424297/how-to-draw-a-digraph-in-a-org-chart-fashion
import matplotlib.pyplot as plt
import numpy as np
import networkx as nx
import graphviz
import time

from PyQt5.QtWidgets import (
    QApplication, QDialog, QPushButton, QVBoxLayout
)

from matplotlib.backends.backend_qt5agg import FigureCanvasQTAgg as FigureCanvas

class Window(QDialog):
    def __init__(self, parent=None):
        super().__init__()

        # a figure instance to plot on
        self.figure = plt.figure()

        self.width = 1000
        self.height = 800
        self.setGeometry(0, 0, self.width, self.height)

        # this is the Canvas Widget that 
        # displays the 'figure'it takes the
        # 'figure' instance as a parameter to __init__
        self.canvas = FigureCanvas(self.figure)
        # this is the Navigation widget
        # it takes the Canvas widget and a parent
        self.toolbar = NavigationToolbar2QT(self.canvas, self)
        # Just some button connected to 'plot' method
        self.button = QPushButton('Import')
        # adding action to the button
        self.button.clicked.connect(self.getfiles)
        # print file path
        self.pathFile = QtWidgets.QTextEdit(self)
        self.pathFile.setFixedSize(self.width, 30)

        # creating a Vertical Box layout
        layout = QVBoxLayout()
        # adding tool bar to the layout
        layout.addWidget(self.toolbar)         
        # adding canvas to the layout
        layout.addWidget(self.canvas)    
        # adding push button to the layout
        layout.addWidget(self.button)   

        layout.addWidget(self.pathFile)  
        # setting layout to the main window
        self.setLayout(layout)

    def get_canvas(self):

        # example stackoverflow

        le = [('D', 'N', {'weight': 3}), ('D', 'I', {'weight': 3}), ('D', 'E', {'weight': 1}), ('I', 'J', {'weight': 2}), ('L', 'M', {'weight': 2}), ('G', 'H', {'weight': 2}), ('H', 'C', {'weight': 1}), ('C', 'D', {'weight': 2}), ('C', 'K', {'weight': 1}), ('B', 'C', {'weight': 2}), ('A', 'B', {'weight': 2}), ('K', 'L', {'weight': 2}), ('E', 'F', {'weight': 2})]
        ln = [('D', {'leaf': 'no', 'root': 'no'}), ('N', {'leaf': 'yes', 'root': 'no'}), ('I', {'leaf': 'no', 'root': 'no'}), ('L', {'leaf': 'no', 'root': 'no'}), ('M', {'leaf': 'yes', 'root': 'no'}), ('J', {'leaf': 'yes', 'root': 'no'}), ('G', {'leaf': 'no', 'root': 'yes'}), ('H', {'leaf': 'no', 'root': 'no'}), ('C', {'leaf': 'no', 'root': 'no'}), ('B', {'leaf': 'no', 'root': 'no'}), ('A', {'leaf': 'no', 'root': 'yes'}), ('K', {'leaf': 'no', 'root': 'no'}), ('E', {'leaf': 'no', 'root': 'no'}), ('F', {'leaf': 'yes', 'root': 'no'})]
    
        g = nx.DiGraph()
        g.add_nodes_from(ln)
        g.add_edges_from(le)

        elarge = [(u, v) for (u, v, d) in g.edges(data=True) if d['weight'] == 3 ]
        enormal = [(u, v) for (u, v, d) in g.edges(data=True) if d['weight'] == 2 ]
        esmall = [(u, v) for (u, v, d) in g.edges(data=True) if d['weight'] == 1 ]

        nleaf = [(u) for (u, d) in g.nodes(data=True) if d['leaf'] == 'yes' ]
        nroot = [(u) for (u, d) in g.nodes(data=True) if d['root'] == 'yes' ]

        edge_labels = dict([((u,v,),d['weight']) for u,v,d in g.edges(data=True)])

        pos = nx.nx_agraph.graphviz_layout(g, prog='dot')

        # nodes
        nx.draw_networkx_nodes(g, pos, node_size=500, node_color='#AAAAAA')
        nx.draw_networkx_nodes(g, pos, nodelist=nleaf, node_color='#00BB00', node_size=500)
        nx.draw_networkx_nodes(g, pos, nodelist=nroot, node_color='#9999FF', node_size=500)

        # edges
        nx.draw_networkx_edges(g, pos, edgelist=elarge, width=2, alpha=0.8, edge_color='g', style='dotted')
        nx.draw_networkx_edges(g, pos, edgelist=enormal, width=2, alpha=0.8, edge_color='b', style='dashed')
        nx.draw_networkx_edges(g, pos, edgelist=esmall, width=2, alpha=0.8, edge_color='b', style='solid')

        # labels
        nx.draw_networkx_edge_labels(g,pos,edge_labels=edge_labels)
        nx.draw_networkx_labels(g, pos, font_size=14, font_color='w', font_family='sans-serif')

        plt.axis('off')
        plt.subplots_adjust(left=0.00, right=1.0, bottom=0.00, top=1.0, hspace = 0, wspace=0)
        self.figure = plt.gcf()

    # action called by the import button
    def plot(self):
        # clearing old figure
        self.figure.clear()
        self.get_canvas()
        self.canvas.draw()
        print("pressed")

    # file explorer
    def getfiles(self):
        fileName, _ = QtWidgets.QFileDialog.getOpenFileName(self, 'Single File', QtCore.QDir.currentPath() , '*.json')
        self.pathFile.setText(fileName)
        self.plot()

# driver code
if __name__ == '__main__':
    print("Ya")
    app = QApplication(sys.argv)
    print("Yo")
    win = Window()
    win.show()
    sys.exit(app.exec())
    exit()