import sys
from PyQt5 import QtCore, QtGui
from PyQt5 import QtWidgets
from matplotlib.backends.backend_qt5 import NavigationToolbar2QT
# gcc -shared -Wl,-soname,testlib -o testlib.so -fPIC testlib.c
# pyuic5 -o main_window_ui.py ui/main_window.ui
# https://stackoverflow.com/questions/44726280/include-matplotlib-in-pyqt5-with-hover-labels
# https://networkx.org/documentation/stable/reference/classes/digraph.html
# https://stackoverflow.com/questions/56424297/how-to-draw-a-digraph-in-a-org-chart-fashion
# https://stackoverflow.com/questions/38661635/ctypes-struct-returned-from-library
import matplotlib.pyplot as plt
from networkx.algorithms.traversal.edgebfs import edge_bfs
import numpy as np
import networkx as nx
import graphviz
import time
from PyQt5.QtCore import QObject, QThread, pyqtSignal
import ctypes
import os
import itertools
import PIL

from PyQt5.QtWidgets import (
    QApplication, QDialog, QPushButton, QVBoxLayout
)

from matplotlib.backends.backend_qt5agg import FigureCanvasQTAgg as FigureCanvas


class CustomNode(ctypes.Structure):
    _fields_ = [('title', ctypes.c_char * 50),
        ('type', ctypes.c_char * 5),
        ('root', ctypes.c_int),
        ('leaf', ctypes.c_int)]

class EdgeNode(ctypes.Structure):
    _fields_ = [('parent', ctypes.c_char * 50),
        ('child', ctypes.c_char * 50)]

class FormulaNode(ctypes.Structure):
    _fields_ = [('data', ctypes.c_char_p),
        ('next', ctypes.c_void_p)]

class CustomList(ctypes.Structure):
    _fields_ = [('next', ctypes.c_void_p),
        ('data', ctypes.c_void_p)]

class FullList(ctypes.Structure):
    _fields_ = [('nl', ctypes.c_void_p),
        ('el', ctypes.c_void_p),
        ('fo', ctypes.c_void_p)]

class Worker(QObject):
    finished = pyqtSignal()

    def run(self):
        print("WORKER")
        self.node_list= []
        self.edge_list = []
        self.formula = []
        dirname = os.path.dirname(__file__)
        so_file = os.path.join(dirname, 'testlib.so')
        my_function = ctypes.CDLL(so_file)
        print("YOOOOO")
        s = ctypes.create_string_buffer(self.pathFile.encode('utf-8'))
        print("KEN")
        my_function.mainfct.restype = ctypes.c_void_p
        my_function.mainfct.argtypes = [ctypes.c_char_p]
        print("2")
        fulllist = FullList.from_address(my_function.mainfct(s))
        print("2")
        newlist = CustomList.from_address(fulllist.nl)

        # .decode('utf-8') better way ?
        if newlist != None :
            tmp_node = CustomNode.from_address(newlist.data)
            newdict = {'type': tmp_node.type.decode('utf-8'),'leaf': tmp_node.leaf, 'root': tmp_node.root}
            newtuple = (tmp_node.title.decode('utf-8'), newdict)
            self.node_list.append(newtuple)

            while newlist.next != None:
                newlist = CustomList.from_address(newlist.next)
                tmp_node = CustomNode.from_address(newlist.data)
                newdict = {'type': tmp_node.type.decode('utf-8'),'leaf': tmp_node.leaf, 'root': tmp_node.root}
                newtuple = (tmp_node.title.decode('utf-8'), newdict)
                self.node_list.append(newtuple)

        newEdgeList = CustomList.from_address(fulllist.el)

        if newEdgeList != None :
            tmp_node = EdgeNode.from_address(newEdgeList.data)
            newtuple = (tmp_node.parent.decode('utf-8'),tmp_node.child.decode('utf-8'))
            self.edge_list.append(newtuple)

            while newEdgeList.next != None:
                newEdgeList = CustomList.from_address(newEdgeList.next)
                tmp_node = EdgeNode.from_address(newEdgeList.data)
                newtuple = (tmp_node.parent.decode('utf-8'),tmp_node.child.decode('utf-8'))
                self.edge_list.append(newtuple)

        newFormula = FormulaNode.from_address(fulllist.fo)

        if newFormula != None :
            newdata = newFormula.data.decode('utf-8')
            self.formula.append(newdata)

            while newFormula.next != None:
                newFormula = FormulaNode.from_address(newFormula.next)
                newdata = newFormula.data.decode('utf-8')
                self.formula.append(newdata)

        print("SELF FORMULA ONE")
        print(self.formula)

        good_formula = []
        str_formula = ""
        for e in self.formula:
            str_formula = str_formula + e
            #print(e)
            d = set()
            t = ()
            d.add((
                e,
                True
            ))
            good_formula.append(d)

        print(good_formula)
        print(str_formula)
        self.str_formula = str_formula
        #brute_force(good_formula)

        my_function.freeList(newlist)
        #my_function.freeEList(newEdgeList)
        #my_function.freeForm(newFormula)
        time.sleep(2)
        #self.data.emit(node_list, edge_list)
        self.finished.emit()
        #self.plot

def brute_force(cnf):
    literals = set()
    for conj in cnf:
        for disj in conj:
            literals.add(disj[0])

    literals = list(literals)
    n = len(literals)
    
    for seq in itertools.product([True,False], repeat=n):
        a = set(zip(literals, seq))

        if all([bool(disj.intersection(a)) for disj in cnf]):
            print(True)
            print(a)


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

        self.tracesFound = QtWidgets.QTextEdit(self)
        self.tracesFound.setFixedSize(self.width, 60)

        # creating a Vertical Box layout
        layout = QVBoxLayout()
        # adding tool bar to the layout
        layout.addWidget(self.toolbar)         
        # adding canvas to the layout
        layout.addWidget(self.canvas)    
        # adding push button to the layout
        layout.addWidget(self.button)   

        layout.addWidget(self.pathFile)  
        layout.addWidget(self.tracesFound)  
        # setting layout to the main window
        self.setLayout(layout)
        # TODO ENLEVER :
        self.getfiles()

    def get_canvas(self, ln, le):

        # example stackoverflow

        # Image URLs for graph nodes
        icons = {
            "AND": "icons/router_black_144x144.png",
            "OR": "icons/switch_black_144x144.png",
            "SAND": "icons/computer_black_144x144.png",
        }
        
        g = nx.DiGraph()

        g.add_nodes_from(ln)
        labels = {n: n for n in g}
        #g.add_edges_from(le)

        types = [(u, d['type']) for (u, d) in g.nodes(data=True)]
        types_dict= {}

        for i in range(len(types)):
            types_dict[types[i][0]] = types[i][1]

        logic_nodes = []
        new_le = []
        labels_logic = {}
        logic_edge = []
        for (u, d) in g.nodes(data=True):
            if d['leaf'] == 0:
                name = u + '_' + "LOGIC"#d['type']
                print(name)
                node = (name, {'type': 'logic'})
                logic_nodes.append(node)
                edge = (u, name)
                labels_logic[name] = d['type']
                logic_edge.append(edge)

        g.add_nodes_from(logic_nodes)
        
        for (u, v) in le:
            edge = (u + '_' + "LOGIC", v)
            new_le.append(edge)

        g.add_edges_from(logic_edge)
        g.add_edges_from(new_le)

        pos = nx.nx_agraph.graphviz_layout(g, prog='dot')

        # edges
        nx.draw_networkx_edges(g, pos, edgelist=logic_edge, arrows=False, width=2, alpha=0.8, edge_color='black', style='solid')
        nx.draw_networkx_edges(g, pos, edgelist=new_le, arrows=False, width=2, alpha=0.8, edge_color='black', style='solid')
        # labels
        nx.draw_networkx_labels(g, pos, labels, font_size=14, font_color='black', font_family='sans-serif', bbox=dict(facecolor="white", edgecolor='black', boxstyle='round,pad=0.8'))
        nx.draw_networkx_labels(g, pos, labels_logic, font_size=14, font_color='b', font_family='sans-serif', bbox=dict(facecolor="white", edgecolor='black', boxstyle='round,pad=0.8'))

        plt.axis('off')
        plt.subplots_adjust(left=0.00, right=1.0, bottom=0.00, top=1.0, hspace = 0, wspace=0)
        self.figure = plt.gcf()

    # action called by the import button
    def plot(self, node_list, edge_list):
        # clearing old figure
        self.figure.clear()
        self.get_canvas(node_list, edge_list)
        self.canvas.draw()
        print("pressed")

    # file explorer
    def getfiles(self):
        fileName, _ = QtWidgets.QFileDialog.getOpenFileName(self, 'Single File', QtCore.QDir.currentPath() , '*.json')
        self.pathFile.setText(fileName)
        # Step 2: Create a QThread object
        self.thread = QThread()
        # Step 3: Create a worker object
        self.worker = Worker()

        self.worker.pathFile = fileName
        # Step 4: Move worker to the thread
        self.worker.moveToThread(self.thread)
        # Step 5: Connect signals and slots
        self.thread.started.connect(self.worker.run)
        #self.worker.finished.connect(lambda: print(self.worker.finished))
        self.worker.finished.connect(self.thread.quit)
        # A REMETTRE
        self.worker.finished.connect(self.cleaning)
        self.thread.finished.connect(self.thread.deleteLater)
        # Step 6: Start the thread
        self.thread.start()

        # Final resets
        self.button.setEnabled(False)
        self.thread.finished.connect(
            lambda: self.button.setEnabled(True)
        )

    def cleaning(self):
        #print("INSIDE")
        #print(self.worker.node_list)
        new_nl = self.worker.node_list
        new_el = self.worker.edge_list
        self.tracesFound.setText(self.worker.str_formula)
        self.worker.deleteLater
        self.plot(new_nl, new_el)
        print(new_nl)
        

# driver code
if __name__ == '__main__':
    app = QApplication(sys.argv)
    win = Window()
    win.show()
    sys.exit(app.exec())