from random import random
import sys
from PyQt5 import QtCore, QtWidgets
from PyQt5.QtWidgets import QMessageBox
from PyQt5.QtWebEngineWidgets import QWebEngineView
# gcc -shared -Wl,-soname,testlib -o testlib.so -fPIC testlib.c
# pyuic5 -o main_window_ui.py ui/main_window.ui
# https://stackoverflow.com/questions/44726280/include-matplotlib-in-pyqt5-with-hover-labels
# https://networkx.org/documentation/stable/reference/classes/digraph.html
# https://stackoverflow.com/questions/56424297/how-to-draw-a-digraph-in-a-org-chart-fashion
# https://stackoverflow.com/questions/38661635/ctypes-struct-returned-from-library
import matplotlib.pyplot as plt
from networkx.drawing.nx_agraph import graphviz_layout, pygraphviz_layout
import numpy as np
import networkx as nx
import graphviz
import time
from PyQt5.QtCore import QObject, QThread, QUrl, pyqtSignal
import ctypes
import os
from pyvis.network import Network
import randomTree
from pysat.solvers import Glucose3
import re
from math import inf
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
            newdict = {'type': tmp_node.type.decode('utf-8'),'leaf': tmp_node.leaf, 'root': tmp_node.root, 'cost': tmp_node.cost, 'prob': tmp_node.prob, 'CM': tmp_node.CM}
            if( newdict['leaf'] == 1 ):
                self.leaf_cnt = self.leaf_cnt + 1
            newtuple = (tmp_node.title.decode('utf-8'), newdict)
            self.node_list.append(newtuple)

            while newlist.next != None:
                newlist = CustomList.from_address(newlist.next)
                tmp_node = CustomNode.from_address(newlist.data)
                newdict = {'type': tmp_node.type.decode('utf-8'),'leaf': tmp_node.leaf, 'root': tmp_node.root, 'cost': tmp_node.cost, 'prob': tmp_node.prob, 'CM': tmp_node.CM}
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

        str_formula = ""
        for e in self.formula:
            str_formula = str_formula + e

        # STR TO CNF SYMPY
        print(str_formula)

        glob = {}
        exec('from sympy.core import Symbol', glob) # ok for I, E, S, N, C, O, or Q
        self.str_formula = str(to_cnf(parse_expr(str_formula, global_dict=glob)))

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
        self.figure = plt.figure()
        self.width = 1000
        self.height = 800
        self.setGeometry(0, 0, self.width, self.height)
        self.canvas = QWebEngineView()
        self.button = QPushButton('Import')
        self.buttonParse = QPushButton('Create JSON')
        self.button.clicked.connect(self.getfiles)
        self.buttonParse.clicked.connect(self.parser)

        self.pathFile = QtWidgets.QTextEdit(self)
        self.pathFile.setFixedSize(self.width, 30)
        self.tracesFound = QtWidgets.QTextEdit(self)
        self.tracesFound.setFixedSize(self.width, 60)

        layout = QHBoxLayout()

        Vlayout_left = QVBoxLayout()
        Vlayout_right= QVBoxLayout()
        layout.addLayout(Vlayout_left)
        layout.addLayout(Vlayout_right)
        Vlayout_left.addWidget(self.canvas)
        Vlayout_left.addWidget(self.button)   

        Vlayout_left.addWidget(self.pathFile)  
        Vlayout_left.addWidget(self.tracesFound)

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

        str = """
        RELATIONS
            A-AND->{B,C}
            C-AND->{F,H}
            B-OR->{E,H}
            H-OR->{I,J}
        COUNTERMEASURES
            CM1 (A, B)
            CM2 (A, C, B)
            CM3 (J)
        """

        # TODO
        #str,cost = randomTree.TreeGen(5, 3)

        # TODO
        self.grammarText.setText(str)
        self.parser()        

    def get_canvas(self, ln, le, leaf_cnt):

        # example stackoverflow

        print("###########################################")

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
        logic_leaf = []
        nodes_not_leaf = []
        new_le = []
        labels_logic = {}
        labels_cost = {}
        logic_edge = []
        for (u, d) in g.nodes(data=True):
            labels_cost[u] = d['cost']
            if d['leaf'] == 0:
                if d['CM'] == 1:
                    nodes_not_leaf.append(u)

                    name_nor = u + '_' + "CMLOGIC"
                    node_nor = (name_nor, {'type': 'logic', 'parent': u, 'CM': 0})
                    logic_nodes.append(node_nor)

                    name_not = u + '_' + "NOT"
                    node_not = (name_not, {'type': 'cmlogic', 'parent': name_nor, 'CM': 0})
                    logic_nodes.append(node_not)

                    name = u + '_' + "LOGIC"
                    node = (name, {'type': 'logic', 'parent': name_not, 'CM': 0})
                    logic_nodes.append(node)

                    edge = (u, name_nor)
                    labels_logic[name_nor] = "NOR"
                    logic_edge.append(edge)

                    edge = (name_nor, name_not)
                    labels_logic[name_not] = "NOT"
                    logic_edge.append(edge)

                    edge = (name_not, name)
                    labels_logic[name] = d['type']
                    logic_edge.append(edge)
                else:
                    nodes_not_leaf.append(u)
                    name = u + '_' + "LOGIC"
                    node = (name, {'type': 'logic', 'parent': u, 'CM': 0})
                    logic_nodes.append(node)
                    # if has no CM
                    edge = (u, name)
                    labels_logic[name] = d['type']
                    logic_edge.append(edge)
            elif d['CM'] == 1:
                
                name_nor = u + '_' + "CMLOGIC"
                node_nor = (name_nor, {'type': 'logic', 'parent': u, 'CM': 0})
                logic_nodes.append(node_nor)

                logic_leaf.append(name_nor)

                edge = (u, name_nor)
                labels_logic[name_nor] = "CM"
                logic_edge.append(edge)


        # attention aux CM !!

        for (u, v) in le:
            if v not in counter_list:
                edge = (u + '_' + "LOGIC", v)
                new_le.append(edge)
            else:
                edge = (u + '_' + "CMLOGIC", v)
                new_le.append(edge)

        g.add_nodes_from(logic_nodes)
        g.add_edges_from(logic_edge)
        g.add_edges_from(new_le)

        pos = nx.nx_agraph.graphviz_layout(g, prog='dot', args='-Gnodesep=0.2 -Gsize=10,6\! -Gdpi=100 -Gratio=fill')

        # RESIZE figure

        # TODO CA AVANCE

        # CM entre noeud et noeud logic
        for (u, d) in g.nodes(data=True):
            print(u,d)    
            if(d['type'] == 'logic'):
                new_pos = list(pos[u])
                new_pos[0] = pos[d['parent']][0]
                pos[u] = tuple(new_pos)

    

        print("@@@@@@@@@@@@@ NODES @@@@@@@@@@@@@")
        for (u, v, d) in g.edges(data=True):
            print(u, v, d)

        print("######### EDGES #############")
        print(le)
        
        nt = Network(height="100%", width="100%")#('600px', '1000px') 
        
        # Title can be html
        for (n, d) in ln:
            title_str = n + ": cost = " + str(d['cost']) + ", prob = " + str(d['prob'])
            if d['CM'] == 1:
                nt.add_node(n_id=n, x=pos[n][0], y=-pos[n][1], label=n, shape='box', title=title_str, group="test")
            elif d['type'] == 'CntMs':
                split_t = n.split("_")
                print(n)
                nt.add_node(n_id=n, x=pos[n][0], y=-pos[n][1], label=n, shape='box', title=split_t[0] + ": cost = " + str(d['cost']) + ", prob = " + str(d['prob']), group="cm")
            elif (d['leaf'] == 1):
                nt.add_node(n_id=n, x=pos[n][0], y=-pos[n][1], label=n, shape='box', title=title_str, group="leaf")
                # htmlTitle("Go wild <'span style='display: inline-block; animation: be-tacky 5s ease-in-out alternate infinite; margin: 5px;'>!<'/span>")
            else:
                nt.add_node(n_id=n, x=pos[n][0], y=-pos[n][1], label=n, shape='box', title=title_str)

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
        msg.exec_()       

# driver code
if __name__ == '__main__':
    app = QApplication(sys.argv)
    win = Window()
    win.show()
    sys.exit(app.exec())