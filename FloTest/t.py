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
    QApplication, QDialog, QHBoxLayout, QPushButton, QVBoxLayout
)

from matplotlib.backends.backend_qt5agg import FigureCanvasQTAgg as FigureCanvas


class CustomNode(ctypes.Structure):
    _fields_ = [('title', ctypes.c_char * 50),
        ('type', ctypes.c_char * 5),
        ('root', ctypes.c_int),
        ('leaf', ctypes.c_int),
        ('cost', ctypes.c_int),
        ('CM', ctypes.c_int),]

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
            newdict = {'type': tmp_node.type.decode('utf-8'),'leaf': tmp_node.leaf, 'root': tmp_node.root, 'cost': tmp_node.cost}
            newtuple = (tmp_node.title.decode('utf-8'), newdict)
            self.node_list.append(newtuple)

            while newlist.next != None:
                newlist = CustomList.from_address(newlist.next)
                tmp_node = CustomNode.from_address(newlist.data)
                newdict = {'type': tmp_node.type.decode('utf-8'),'leaf': tmp_node.leaf, 'root': tmp_node.root, 'cost': tmp_node.cost}
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

class ParserWorker(QObject):
    finished = pyqtSignal()

    def run(self):

        self.node_list= []

        dirname = os.path.dirname(__file__)
        so_file = os.path.join(dirname, 'testlib.so')
        my_function = ctypes.CDLL(so_file)

        s = ctypes.create_string_buffer(self.fullText.encode('utf-8'))

        my_function.parser.restype = ctypes.c_int
        my_function.parser.argtypes = [ctypes.c_char_p]
        ret = FullList.from_address(my_function.parser(s))

        time.sleep(2)
        self.finished.emit()

        if ret != None :
            print("NICE WE GOT HERE")
            pass


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
        self.buttonParse = QPushButton('Create JSON')
        # adding action to the button
        self.button.clicked.connect(self.getfiles)
        self.buttonParse.clicked.connect(self.parser)
        # print file path
        self.pathFile = QtWidgets.QTextEdit(self)
        self.pathFile.setFixedSize(self.width, 30)

        self.tracesFound = QtWidgets.QTextEdit(self)
        self.tracesFound.setFixedSize(self.width, 60)

        layout = QHBoxLayout()
        # creating a Vertical Box layout
        Vlayout_left = QVBoxLayout()
        Vlayout_right= QVBoxLayout()
        layout.addLayout(Vlayout_left)
        layout.addLayout(Vlayout_right)
        # adding tool bar to the layout
        Vlayout_left.addWidget(self.toolbar)         
        # adding canvas to the layout
        Vlayout_left.addWidget(self.canvas)    
        # adding push button to the layout
        Vlayout_left.addWidget(self.button)   

        Vlayout_left.addWidget(self.pathFile)  
        Vlayout_left.addWidget(self.tracesFound)  
        # setting layout to the main window

        self.grammarText = QtWidgets.QTextEdit(self)
        self.grammarText.setFixedWidth(400)
        Vlayout_right.addWidget(self.grammarText)
        Vlayout_right.addWidget(self.buttonParse)

        self.setLayout(layout)
        # TODO ENLEVER :
        #self.getfiles()
        '''
        str = """
            A1 -AND-> { B1, A12}
            G -OR-> {A1, A2}
            """
        '''
        str = """
        D3 -OR-> {F3, R, S}
        F3 -AND-> {F12}
        R -AND-> {F12}
        S -OR-> {F12}
        R -OR-> {F13}
        """
        
        self.grammarText.setText(str)
        self.parser()
        

    def get_canvas(self, ln, le):

        # example stackoverflow

        print("###########################################")

        g = nx.DiGraph()

        
        g.add_nodes_from(ln)
        print(ln)
        print(le)
        labels = {n: n for n in g}
        #g.add_edges_from(le)  

        types = [(u, d['type']) for (u, d) in g.nodes(data=True)]
        counter_list = [u for (u, d) in g.nodes(data=True) if d['type'] == 'CntMs']
        labels_counter = {u: u for (u, d) in g.nodes(data=True) if d['type'] == 'CntMs'}
       
        types_dict= {}

        for i in range(len(types)):
            types_dict[types[i][0]] = types[i][1]

        logic_nodes = []
        nodes_not_leaf = []
        new_le = []
        labels_logic = {}
        labels_cost = {}
        logic_edge = []
        for (u, d) in g.nodes(data=True):
            labels_cost[u] = d['cost']
            print("HEHEHEHEHEHEHEHEEH")
            if d['leaf'] == 0:
                nodes_not_leaf.append(u)
                name = u + '_' + "LOGIC"#d['type']
                print(name)
                node = (name, {'type': 'logic', 'parent': u})
                logic_nodes.append(node)
                # if has no CM
                edge = (u, name)
                labels_logic[name] = d['type']
                logic_edge.append(edge)


                # else...

            #if d['type'] == 'CntMs':
                #name = u + '_' + "LOGIC"#d['type']
                #print("e")
                #node = (name, {'type': 'logic', 'parent': u})
                #logic_nodes.append(node)
                #edge = (u, name)
                #labels_logic[name] = d['type']
                #logic_edge.append(edge)
                

        print("COPYPYPYPYP")
        print(logic_nodes)
        g.add_nodes_from(logic_nodes)
        for (u, d) in g.nodes(data=True):
            print(u, d)
        print("COPYPYPYPYP")
        #for (u, d) in g.nodes(data=True):
        #    print(u, d)
        
        #g.add_edges_from(new_le)

        # attention aux CM !!
        for (u, v) in le:
            # if type != cntms
            if v not in counter_list:
                edge = (u + '_' + "LOGIC", v)
                print(edge)
                new_le.append(edge)
            else:
                if u in nodes_not_leaf:
                    edge = (u + '_' + "LOGIC", v)
                    print(edge)
                    new_le.append(edge)
                else:
                    new_le.append((u, v))

        g.add_edges_from(logic_edge)
        g.add_edges_from(new_le)

        pos = nx.nx_agraph.graphviz_layout(g, prog='dot')

        # CM entre noeud et noeud logic

        for (u, d) in g.nodes(data=True):
            print(u, d)
            
            if(d['type'] == 'logic'):
                new_pos = list(pos[u])
                new_pos[0] = pos[d['parent']][0]
                pos[u] = tuple(new_pos)
    

        print("BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB")
        for (u, v, d) in g.edges(data=True):
            print(u, v, d)

        print("AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA")

        print(le)
        
        # edges
        #nx.draw_networkx_edges(g, pos, edgelist=logic_edge, arrows=False, width=2, alpha=0.8, edge_color='black', style='solid', connectionstyle='angle')
        #n x.draw_networkx_edges(g, pos, edgelist=new_le, arrows=False, width=2, alpha=0.8, edge_color='black', style='solid'), connectionstyle='aangle3')
        nx.draw_networkx_edges(g, pos, edgelist=logic_edge, connectionstyle='arc3, rad=0.0')#angleA=0, angleB=90, rad=0.0')
        nx.draw_networkx_edges(g, pos, edgelist=new_le, connectionstyle='arc3, rad=0.0')
        # labels
        nx.draw_networkx_labels(g, pos, labels, font_size=14, font_color='black', font_family='sans-serif', bbox=dict(facecolor="white", edgecolor='black', boxstyle='round,pad=0.8'))
        nx.draw_networkx_labels(g, pos, labels_logic, font_size=14, font_color='b', font_family='sans-serif', bbox=dict(facecolor="white", edgecolor='black', boxstyle='round,pad=0.8'))
        nx.draw_networkx_labels(g, pos, labels_counter, font_size=14, font_color='g', font_family='sans-serif', bbox=dict(facecolor="white", edgecolor='black', boxstyle='round,pad=0.8'))

        pos_higher = {}
        y_off = -20  # offset on the y axis

        for k, v in pos.items():
            pos_higher[k] = (v[0], v[1]+y_off)

        nx.draw_networkx_labels(g, pos_higher, labels_cost,  font_size=10, font_color='b', font_family='sans-serif', bbox=dict(facecolor="white", edgecolor='black', boxstyle='round,pad=0.2'))

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

    def parser(self):
        self.parser_thread = QThread()
        self.parser_worker = ParserWorker()
        self.parser_worker.fullText = self.grammarText.toPlainText()
        self.parser_worker.moveToThread(self.parser_thread)
        self.parser_thread.started.connect(self.parser_worker.run)
        self.parser_worker.finished.connect(self.parser_thread.quit)
        self.parser_worker.finished.connect(self.parser_worker.deleteLater)
        self.parser_thread.finished.connect(self.parser_thread.deleteLater)
        self.parser_thread.start()
        # Final resets
        self.buttonParse.setEnabled(False)
        self.parser_thread.finished.connect(
            lambda: self.buttonParse.setEnabled(True)
        )
        

# driver code
if __name__ == '__main__':
    app = QApplication(sys.argv)
    win = Window()
    win.show()
    sys.exit(app.exec())