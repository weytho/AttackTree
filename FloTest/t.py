from random import random
import sys
from PyQt5 import QtCore, QtGui, QtWidgets
from PyQt5.QtWidgets import QLabel, QMessageBox
from PyQt5.QtWebEngineWidgets import QWebEngineView
from matplotlib.backends.backend_qt5 import NavigationToolbar2QT
# gcc -shared -Wl,-soname,testlib -o testlib.so -fPIC testlib.c
# pyuic5 -o main_window_ui.py ui/main_window.ui
# https://stackoverflow.com/questions/44726280/include-matplotlib-in-pyqt5-with-hover-labels
# https://networkx.org/documentation/stable/reference/classes/digraph.html
# https://stackoverflow.com/questions/56424297/how-to-draw-a-digraph-in-a-org-chart-fashion
# https://stackoverflow.com/questions/38661635/ctypes-struct-returned-from-library
import matplotlib.pyplot as plt
from networkx.algorithms.traversal.edgebfs import edge_bfs
from networkx.drawing.nx_agraph import graphviz_layout, pygraphviz_layout
import numpy as np
import networkx as nx
import graphviz
import time
from PyQt5.QtCore import QObject, QThread, QUrl, pyqtSignal, Qt
import ctypes
import os
from pyvis.network import Network
import randomTree
from pysat.solvers import Glucose3
import re
from math import inf
from collections import Counter
from sympy import *
from sympy.parsing.sympy_parser import parse_expr
import json

dirname = os.path.dirname(__file__)


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
        ('prob', ctypes.c_double),
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
        self.leaf_cnt = 0
        self.formula = []
        dirname = os.path.dirname(__file__)
        so_file = os.path.join(dirname, 'testlib.so')
        my_function = ctypes.CDLL(so_file)

        s = ctypes.create_string_buffer(self.pathFile.encode('utf-8'))
     
        my_function.mainfct.restype = ctypes.c_void_p
        my_function.mainfct.argtypes = [ctypes.c_char_p]
 
        fulllist = FullList.from_address(my_function.mainfct(s))
        newlist = CustomList.from_address(fulllist.nl)

        # .decode('utf-8') better way ?
        if newlist != None :
            tmp_node = CustomNode.from_address(newlist.data)
            newdict = {'type': tmp_node.type.decode('utf-8'),'leaf': tmp_node.leaf, 'root': tmp_node.root, 'cost': tmp_node.cost, 'prob': tmp_node.prob}
            if( newdict['leaf'] == 1 ):
                self.leaf_cnt = self.leaf_cnt + 1
            newtuple = (tmp_node.title.decode('utf-8'), newdict)
            self.node_list.append(newtuple)

            while newlist.next != None:
                newlist = CustomList.from_address(newlist.next)
                tmp_node = CustomNode.from_address(newlist.data)
                newdict = {'type': tmp_node.type.decode('utf-8'),'leaf': tmp_node.leaf, 'root': tmp_node.root, 'cost': tmp_node.cost, 'prob': tmp_node.prob}
                if( newdict['leaf'] == 1 ):
                    self.leaf_cnt = self.leaf_cnt + 1
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

        #print(good_formula)
        #print(str_formula)
        #self.str_formula = str_formula

        #print(type(str_formula))
        #print(str_formula)
        #print(parse_expr(str_formula))
        #print(to_cnf(parse_expr(str_formula)))

        # STR TO CNF SYMPY
        self.str_formula = str(to_cnf(parse_expr(str_formula)))

        my_function.freeList(newlist)
        #my_function.freeEList(newEdgeList)
        #my_function.freeForm(newFormula)
        time.sleep(2)
        #self.data.emit(node_list, edge_list)
        self.finished.emit()
        #self.plot

class ParserWorker(QObject):
    finished = pyqtSignal(int)

    def run(self):

        self.node_list= []

        dirname = os.path.dirname(__file__)
        so_file = os.path.join(dirname, 'testlib.so')
        my_function = ctypes.CDLL(so_file)

        strTest = self.fullText
        new_s = strTest.split("RELATIONS")
        print(new_s)
        new_s2 = new_s[1].split("COUNTERMEASURES")
        print(new_s2)
        new_s3 = new_s2[1].split("PROPERTIES")
        print(new_s3)

        if(len(new_s3) <= 1):
            print("Boolean mode")
            s = ctypes.create_string_buffer(new_s2[0].encode('utf-8'))
            s2 = ctypes.create_string_buffer(new_s3[0].encode('utf-8'))

            my_function.parser.restype = ctypes.c_int
            my_function.parser.argtypes = [ctypes.c_char_p]
            ret = my_function.parser(s, "", s2)
        else:
            print(new_s2[0])
            print(new_s3[0])
            print(new_s3[1])

            # sanitize and check input
            s = ctypes.create_string_buffer(new_s2[0].encode('utf-8'))
            s2 = ctypes.create_string_buffer(new_s3[0].encode('utf-8'))
            s3 = ctypes.create_string_buffer(new_s3[1].encode('utf-8'))

            my_function.parser.restype = ctypes.c_int
            my_function.parser.argtypes = [ctypes.c_char_p]
            ret = my_function.parser(s, s3, s2)

        time.sleep(2)
        self.finished.emit(ret)

        if ret == 0 :
            print("NICE WE GOT HERE")
            pass
        else:
            print("ERROR IN PARSER")
            print("Code : " + str(ret))
            pass


class Window(QDialog):
    def __init__(self, parent=None):
        super().__init__()
        # a figure instance to plot on
        #self.figure = plt.figure(figsize=(20,20))
        self.figure = plt.figure()
        self.width = 1000
        self.height = 800
        self.setGeometry(0, 0, self.width, self.height)
        # this is the Canvas Widget that 
        # displays the 'figure'it takes the
        # 'figure' instance as a parameter to __init__
        # TODO
        #self.canvas = FigureCanvas(self.figure)
        #self.canvas.setParent(self)
        self.canvas = QWebEngineView()
        # this is the Navigation widget
        # it takes the Canvas widget and a parent
        #self.toolbar = NavigationToolbar2QT(self.canvas, self)
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
        #Vlayout_left.addWidget(self.toolbar)         
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
        RELATIONS
            D3-OR-> {F3, R, S}
            F3 -AND-> {F12}
            R -AND-> {F12}
            S -OR-> {F13}
        COUNTERMEASURES
            CM1 (F13, F12)
        PROPERTIES
            F12 : {cost = 10, prob = 1.0}
            F13 : {cost = 1, prob = 2.5}
            CM1 : {cost = 2}
        """
        '''

        str = """
        RELATIONS
            D3-OR-> {F3, R, S}
            F3 -AND-> {F12}
            R -AND-> {F12}
            S -OR-> {F13}
        COUNTERMEASURES
            CM1 (F13, F12)
        """
        

        # TODO
        #str,cost = randomTree.TreeGen(5, 3)

        '''
        g = Glucose3()
        g.add_clause([-1, 2])
        g.add_clause([-2, 3])
        print(g.solve())
        print(g.get_model())
        '''

        # TODO
        self.grammarText.setText(str)
        self.parser()        

    def get_canvas(self, ln, le, leaf_cnt):

        # example stackoverflow

        print("###########################################")     
        #self.figure.set_size_inches(10*3, 6*3, forward=True)

        g = nx.DiGraph()
        
        g.add_nodes_from(ln)
        print(ln)
        print(le)
        labels = {n: n for n in g}

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
            if d['leaf'] == 0:
                nodes_not_leaf.append(u)
                name = u + '_' + "LOGIC"#d['type']
                node = (name, {'type': 'logic', 'parent': u})
                logic_nodes.append(node)
                # if has no CM
                edge = (u, name)
                labels_logic[name] = d['type']
                logic_edge.append(edge)
                
        g.add_nodes_from(logic_nodes)
        #for (u, d) in g.nodes(data=True):
         #   print(u, d)

        # attention aux CM !!
        for (u, v) in le:
            # if type != cntms
            if v not in counter_list:
                edge = (u + '_' + "LOGIC", v)
                new_le.append(edge)
            else:
                if u in nodes_not_leaf:
                    edge = (u + '_' + "LOGIC", v)
                    new_le.append(edge)
                else:
                    new_le.append((u, v))

        g.add_edges_from(logic_edge)
        g.add_edges_from(new_le)

        #ng = nx.nx_agraph.to_agraph(g)
        #ng.graph_attr.update(size="100,100")
        
        #ng.layout(prog="dot")
        #print(ng)
        #g = nx.nx_agraph.from_agraph(ng)
        pos = nx.nx_agraph.graphviz_layout(g, prog='dot', args='-Gnodesep=0.2 -Gsize=10,6\! -Gdpi=100 -Gratio=fill')

        '''
        for k, v in pos.items():
            #pos[k][0] = pos[k][0] *1.5

            new_pos = list(pos[k])
            new_pos[1] = pos[k][1]# * 5
            pos[k] = tuple(new_pos)
        '''
        
        print("HHHHHH")
        
        '''ng.layout(prog="dot")
        list = ng.nodes()
        print(list)
        for element in list:
            print(element)
        #print(ng.nodes)
        '''
        #print(pos)

        # RESIZE figure
        list_width = []
        for k, v in pos.items():
            list_width.append(v[1])
        # TODO CA AVANCE
        # 10 * 6 inches
        # 100 dpi
        # For 5 leaves ?
        # 1000 * 600 pixels
        current_size_x = 10
        current_size_y = 6
        current_dpi = 100
        list_level = Counter(list_width).most_common()
        biggest_level = list_level[0][1]
        biggest_trace = len(list_level)
        #print("HERE IS THE BIGGEST")
        #print(list_level)
        #print(biggest_level)
        #print(biggest_trace)
        if( biggest_level > 7 or biggest_trace > 9):
            # TODO FIXE THIS NBR
            max_number_on_line = 7
            coeff1 = (biggest_level + 1) / max_number_on_line
            max_number_on_trace = 7
            coeff2 = (biggest_trace + 1) / max_number_on_trace
            coeff = max(coeff1, coeff2)
            self.figure.set_size_inches(current_size_x*coeff, current_size_y*coeff, forward=True)
            self.figure.set_dpi(current_dpi/coeff)
        else:
            self.figure.set_size_inches(current_size_x, current_size_y, forward=True)
            self.figure.set_dpi(current_dpi)
            #pass

        #self.figure.set_size_inches(current_size_x, current_size_y, forward=True)

        # CM entre noeud et noeud logic

        for (u, d) in g.nodes(data=True):
            print(u, d)
            
            if(d['type'] == 'logic'):
                new_pos = list(pos[u])
                new_pos[0] = pos[d['parent']][0]
                pos[u] = tuple(new_pos)
    

        print("@@@@@@@@@@@@@ NODES @@@@@@@@@@@@@")
        for (u, v, d) in g.edges(data=True):
            print(u, v, d)

        print("######### EDGES #############")
        #print(le)
        
        # edges
        nx.draw_networkx_edges(g, pos, edgelist=logic_edge, connectionstyle='arc3, rad=0.0')
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
        #self.figure = plt.gcf()

        plt.savefig('testingImage.png')
        nt = Network(height="100%", width="100%")#('600px', '1000px') 
        
        # Title can be html

        for (n, d) in ln:
            if (d['leaf'] == 1):
                nt.add_node(n_id=n, x=pos[n][0], y=-pos[n][1], label=n, shape='box', title=n + ": cost = " + str(d['cost']) + ", prob = " + str(d['prob']), group="leaf")
                # htmlTitle("Go wild <'span style='display: inline-block; animation: be-tacky 5s ease-in-out alternate infinite; margin: 5px;'>!<'/span>")
            else:
                nt.add_node(n_id=n, x=pos[n][0], y=-pos[n][1], label=n, shape='box', title=n + ": cost = " + str(d['cost']) + ", prob = " + str(d['prob']))

        for (n, d) in logic_nodes:
            nt.add_node(n_id=n, x=pos[n][0], y=-pos[n][1], label=labels_logic[n], shape='box', group="logic")

        for (n, d) in new_le:
            nt.add_edge(n, d)

        for (n, d) in logic_edge:
            nt.add_edge(n, d)

        #nt.from_nx(g)
        # https://networkx.org/documentation/stable/_modules/networkx/drawing/nx_agraph.html#pygraphviz_layout
        #nt.show_buttons()
  
        settings_file = os.path.join(dirname, 'pyvis_param.json')
        with open(settings_file, 'r') as file:
            data_options = json.load(file)
        nt.set_options("var options = " + json.dumps(data_options))
        nt.save_graph('nx.html') 
        
        print("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@")

    # action called by the import button
    def plot(self, node_list, edge_list, leaf_cnt):
        # clearing old figure
        self.figure.clear()
        self.get_canvas(node_list, edge_list, leaf_cnt)    
        #self.canvas.setContextMenuPolicy(Qt.NoContextMenu)
        html_file = os.path.join(dirname, 'nx.html')
        local_url = QUrl.fromLocalFile(html_file)
        self.canvas.load(local_url)
        #self.canvas.draw()
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
        new_nl = self.worker.node_list
        new_el = self.worker.edge_list
        leaf_cnt = self.worker.leaf_cnt
        self.tracesFound.setText(self.worker.str_formula)
        self.worker.deleteLater
        self.plot(new_nl, new_el, leaf_cnt)
        print(new_nl)

    def parser(self):
        self.parser_thread = QThread()
        self.parser_worker = ParserWorker()
        self.parser_worker.fullText = self.grammarText.toPlainText()
        self.parser_worker.moveToThread(self.parser_thread)
        self.parser_thread.started.connect(self.parser_worker.run)
        self.parser_worker.finished.connect(self.parser_thread.quit)
        self.parser_worker.finished.connect(self.show_popup)
        self.parser_worker.finished.connect(self.parser_worker.deleteLater)
        self.parser_thread.finished.connect(self.parser_thread.deleteLater)
        self.parser_thread.start()
        # Final resets
        self.buttonParse.setEnabled(False)
        self.parser_thread.finished.connect(
            lambda: self.buttonParse.setEnabled(True)
        )

    def show_popup(self, error_id):
        if( error_id == 0):
            return
        msg = QMessageBox()
        msg.setWindowTitle("Error in Grammar during Tree generation")
        if(error_id == 1):
            msg.setText("Empty !")
        elif(error_id == 2):
            msg.setText("Redefinition of relation !")
        elif(error_id == 3):
            msg.setText("Loop detected in tree !")
        else:
            msg.setText("This is the main text!")
        msg.setIcon(QMessageBox.Critical)
        x = msg.exec_()
        

# driver code
if __name__ == '__main__':
    app = QApplication(sys.argv)
    win = Window()
    win.show()
    sys.exit(app.exec())