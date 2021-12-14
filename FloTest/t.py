from random import random
import sys
from PyQt5 import QtCore, QtWidgets
from PyQt5.QtWidgets import QMessageBox, QToolBar, QToolButton
from PyQt5.QtWebEngineWidgets import QWebEngineView
# gcc -shared -Wl,-soname,testlib -o testlib.so -fPIC testlib.c
# pyuic5 -o main_window_ui.py ui/main_window.ui
# https://stackoverflow.com/questions/44726280/include-matplotlib-in-pyqt5-with-hover-labels
# https://networkx.org/documentation/stable/reference/classes/digraph.html
# https://stackoverflow.com/questions/56424297/how-to-draw-a-digraph-in-a-org-chart-fashion
# https://stackoverflow.com/questions/38661635/ctypes-struct-returned-from-library
import matplotlib.pyplot as plt
from networkx.drawing.nx_agraph import graphviz_layout, pygraphviz_layout
import networkx as nx
from PyQt5.QtCore import QThread, QUrl, Qt
import os
from pyvis.network import Network
from randomTree import *
from sympy import *
from sympy.parsing.sympy_parser import parse_expr
import json
# From Folder
from Worker import *
from ParserWorker import *
from Struct import *

dirname = os.path.dirname(__file__)

from PyQt5.QtWidgets import (
    QApplication, QDialog, QHBoxLayout, QPushButton, QVBoxLayout
)

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
        self.tracesFound.setFixedSize(1400, 60)

        base_layout = QVBoxLayout()

        layout = QHBoxLayout()
        base_layout.addLayout(layout)

        #Vlayout_toolbar = QVBoxLayout()
        Vlayout_left = QVBoxLayout()
        Vlayout_right= QVBoxLayout()
        #layout.addLayout(Vlayout_toolbar)
        layout.addLayout(Vlayout_left)
        layout.addLayout(Vlayout_right)
        Vlayout_left.addWidget(self.canvas)
        Vlayout_left.addWidget(self.button)   

        Vlayout_left.addWidget(self.pathFile)  
        ##Vlayout_left.addWidget(self.tracesFound)

        # Create pyqt toolbar
        #toolBar = QToolBar()
        #toolBar.setOrientation(Qt.Vertical)
        #Vlayout_toolbar.addWidget(toolBar)

        # Add buttons to toolbar
        '''
        toolButton = QToolButton()
        toolButton.setText("CNF Formula")
        toolButton.setCheckable(True)
        toolButton.setAutoExclusive(True)
        toolBar.addWidget(toolButton)
        toolButton = QToolButton()
        toolButton.setText("Complete Formula")
        toolButton.setCheckable(True)
        toolButton.setAutoExclusive(True)
        toolBar.addWidget(toolButton)
        '''

        result_layout = QHBoxLayout()
        result_layout.addWidget(self.tracesFound)
        base_layout.addLayout(result_layout)

        self.grammarText = QtWidgets.QTextEdit(self)
        self.grammarText.setFixedWidth(400)
        Vlayout_right.addWidget(self.grammarText)
        Vlayout_right.addWidget(self.buttonParse)

        self.setLayout(base_layout)
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
        str,str1,str2 = TreeGen(3, 3, 2)

        print("GOT FROM RANDOM TREE")

        print(str + "\n" + str1 + "\n" + str2)

        # TODO
        self.grammarText.setText(str + "\n" + str1 + "\n" + str2)
        self.parser()        

    def get_canvas(self, ln, le):

        # example stackoverflow

        print("###########################################")

        g = nx.DiGraph()
        
        g.add_nodes_from(ln)
        print(ln)
        print(le)

        types = [(u, d['type']) for (u, d) in g.nodes(data=True)]
        counter_list = [u for (u, d) in g.nodes(data=True) if d['type'] == 'CntMs']
       
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
                    node_nor = (name_nor, {'type': 'cmlogic', 'parent': u, 'CM': 0})
                    logic_nodes.append(node_nor)

                    name = u + '_' + "LOGIC"
                    node = (name, {'type': 'logic', 'parent': u, 'CM': 0})
                    logic_nodes.append(node)

                    edge = (u, name_nor)
                    labels_logic[name_nor] = "CM"
                    logic_edge.append(edge)

                    edge = (u, name)
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
                node_nor = (name_nor, {'type': 'cmlogic', 'parent': u, 'CM': 0})
                logic_nodes.append(node_nor)

                logic_leaf.append(name_nor)

                edge = (u, name_nor)
                labels_logic[name_nor] = "CM"
                logic_edge.append(edge)


        # attention aux CM !!

        for (u, v) in le:
            if v in counter_list:
                edge = (u + '_' + "CMLOGIC", v)
                new_le.append(edge)
            else:
                edge = (u + '_' + "LOGIC", v)
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

    

        print("@@@@@@@@@@@@@ NODES @@@@@@@@@@@@@")
        for (u, v, d) in g.edges(data=True):
            print(u, v, d)

        print("######### EDGES #############")
        print(le)
        
        nt = Network(height="100%", width="100%")#('600px', '1000px') 
        
        # Title can be html
        for (n, d) in ln:
            title_str = n + ": cost = " + str(d['cost']) + ", prob = " + str(d['prob'])
            #if d['CM'] == 1:
            #    nt.add_node(n_id=n, x=pos[n][0], y=-pos[n][1], label=n, shape='box', title=title_str, group="test")
            if d['type'] == 'CntMs':
                nt.add_node(n_id=n, x=pos[n][0], y=-pos[n][1], label=d['variable'], shape='box', title=d['variable'] + ": cost = " + str(d['cost']) + ", prob = " + str(d['prob']), group="cm")
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
            nt.add_edge(n, d, color="#000000", width=4)

        #nt.from_nx(g)
        # https://networkx.org/documentation/stable/_modules/networkx/drawing/nx_agraph.html#pygraphviz_layout
        #nt.show_buttons()

        #https://visjs.github.io/vis-network/docs/network/nodes.html
  
        settings_file = os.path.join(dirname, 'pyvis_param.json')
        with open(settings_file, 'r') as file:
            data_options = json.load(file)
        nt.set_options("var options = " + json.dumps(data_options))
        nt.save_graph('nx.html') 
        
        print("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@")

    # action called by the import button
    def plot(self, node_list, edge_list):
        # clearing old figure
        self.figure.clear()
        self.get_canvas(node_list, edge_list)    
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