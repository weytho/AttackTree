##
# @file
# Main file of the python GUI interface
# Create GUI using PyQt5

import sys
from PyQt5 import QtCore, QtWidgets
from PyQt5.QtWidgets import QMessageBox, QToolBar, QToolButton
from PyQt5.QtWebEngineWidgets import QWebEngineView
import matplotlib.pyplot as plt
import networkx as nx
from PyQt5.QtCore import QThread, QUrl, Qt
import os
from pyvis.network import Network
from randomTree import *
import json
# From Folder
from Worker import *
from ParserWorker import *
from Struct import *
import copy

dirname = os.path.dirname(__file__)

from PyQt5.QtWidgets import (
    QApplication, QDialog, QHBoxLayout, QPushButton, QVBoxLayout, QLabel, QSpinBox, QWidget
)

class Window(QDialog):
    def __init__(self, parent=None):
        super().__init__()
        self.figure = plt.figure()
        self.width = 1000
        self.height = 800
        self.setGeometry(0, 0, self.width, self.height)

        font = self.font()
        font.setPointSize(10)
        QApplication.instance().setFont(font)

        self.canvas = QWebEngineView()
        self.buttonImportJson = QPushButton('Import JSON')
        self.buttonImportGrammar = QPushButton('Import Grammar')
        self.buttonParse = QPushButton('Create JSON')
        self.buttonImportJson.clicked.connect(self.getfileJSON)
        self.buttonImportGrammar.clicked.connect(self.getfileGrammar)
        self.buttonParse.clicked.connect(self.parser)


        self.pathFile = QtWidgets.QTextEdit(self)
        self.pathFile.setFixedSize(self.width, 24)
        self.tracesFound = QtWidgets.QTextEdit(self)
        self.tracesFound.setFixedHeight(60)
        self.tracesFound.setAlignment(Qt.AlignHCenter)

        base_layout = QVBoxLayout()

        layout = QHBoxLayout()
        base_layout.addLayout(layout)

        Vlayout_toolbar = QVBoxLayout()
        Vlayout_left = QVBoxLayout()
        Vlayout_right= QVBoxLayout()
        layout.addLayout(Vlayout_toolbar)
        layout.addLayout(Vlayout_left)
        layout.addLayout(Vlayout_right)
        Vlayout_left.addWidget(self.canvas)
        Vlayout_left.addWidget(self.buttonImportJson)   

        Vlayout_left.addWidget(self.pathFile)  
        ##Vlayout_left.addWidget(self.tracesFound)

        # Create pyqt toolbar
        toolBar = QToolBar()
        toolBar.setOrientation(Qt.Vertical)
        #toolBar.setFixedWidth(170)
        
        toolBar.addSeparator()
        section_output = QLabel("Output Format")
        section_output.setAlignment(Qt.AlignHCenter)
        section_output.setStyleSheet("font-weight: bold")
        toolBar.addWidget(section_output)

        # Add buttons to toolbar
        toolButton = QToolButton()
        toolButton.setText("CNF Formula")
        toolButton.setCheckable(True)
        toolButton.setAutoExclusive(True)
        toolButton.clicked.connect(self.outputCNFformula)
        toolBar.addWidget(toolButton)
        self.cnf_button = toolButton

        toolButton = QToolButton()
        toolButton.setText("Complete Formula")
        toolButton.setCheckable(True)
        toolButton.setAutoExclusive(True)
        toolButton.clicked.connect(self.outputCompleteformula)
        toolBar.addWidget(toolButton)
        self.complete_button = toolButton

        solution = QWidget()
        sol_layout = QHBoxLayout()
        solution.setLayout(sol_layout)

        toolButton = QToolButton()
        toolButton.setText("Solve (max=0)")
        toolButton.setCheckable(False)
        toolButton.setAutoExclusive(True)
        toolButton.clicked.connect(self.outputSolution)
        toolButton.setFixedWidth(100)
        sol_layout.addWidget(toolButton)
        self.sol_button = toolButton

        toolSpinSol = QSpinBox()
        sol_layout.addWidget(toolSpinSol)
        self.sol_spin = toolSpinSol

        toolBar.addWidget(solution)

        toolButton = QToolButton()
        toolButton.setText("Clear")
        toolButton.setCheckable(True)
        toolButton.setAutoExclusive(True)
        toolButton.clicked.connect(self.outputClear)
        toolBar.addWidget(toolButton)
        self.clear_button = toolButton

        toolBar.addSeparator()
        toolButton = QToolButton()
        toolButton.setText("Random Tree")
        toolButton.clicked.connect(self.getRandomTree)
        toolBar.addWidget(toolButton)
        self.rndtree_button = toolButton

        Vlayout_toolbar.addWidget(toolBar)        

        result_layout = QHBoxLayout()
        result_layout.addWidget(self.tracesFound)
        base_layout.addLayout(result_layout)

        self.grammarText = QtWidgets.QTextEdit(self)
        self.grammarText.setFixedWidth(400)
        Vlayout_right.addWidget(self.grammarText)
        Vlayout_right.addWidget(self.buttonImportGrammar)
        Vlayout_right.addWidget(self.buttonParse)

        self.setLayout(base_layout)

        # TODO ENLEVER :
        #self.getfiles()

        self.curr_formula = None
        self.curr_cnf = None
        self.sol_array = None
        
        str = """
        RELATIONS        self.parser_thread.finished.connect(
            lambda: self.buttonParse.setEnabled(True)
        )
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

        str = """
        RELATIONS
        A -AND-> {B,C,D}
        C -AND-> {E,F}
        D -AND-> {~E}

        COUNTERMEASURES

        PROPERTIES
        """

        str = """
        RELATIONS
        node -AND-> {node0,node1}
        COUNTERMEASURES
        CM1 (node0,node0)
        PROPERTIES
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

        self.current_network = nt
        
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
    def getfileJSON(self):
        fileName, _ = QtWidgets.QFileDialog.getOpenFileName(self, 'Single File', QtCore.QDir.currentPath() , '*.json')
        if not fileName :
            return

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
        self.buttonImportJson.setEnabled(False)
        self.thread.finished.connect(
            lambda: self.buttonImportJson.setEnabled(True)
        )

    def getfileGrammar(self):
        fileName, _ = QtWidgets.QFileDialog.getOpenFileName(self, 'Single File', QtCore.QDir.currentPath() , '*.txt')
        if not fileName :
            return

        self.buttonImportGrammar.setEnabled(False)
        with open(fileName, 'r') as f: 
            self.grammarText.setText(f.read())
        self.buttonImportGrammar.setEnabled(True)

    def outputCNFformula(self):
        if self.curr_cnf is not None :
            self.tracesFound.setText(self.curr_cnf)
            self.tracesFound.repaint()

    def outputCompleteformula(self):
        if self.curr_formula is not None :
            self.tracesFound.setText(self.curr_formula)
            self.tracesFound.repaint()

    def outputSolution(self):
        if self.curr_formula is not None :
            index = self.sol_spin.value()
            self.tracesFound.setText(' '.join(map(str, self.var_array)) + "\n" + ' '.join(map(str, self.sol_array[index])))
            self.tracesFound.repaint()

            list = []
            old_nodes = copy.deepcopy(self.current_network.nodes)
            for i, v in enumerate(self.sol_array[index]) :
                if v >= 0 :
                    list.append(self.var_array[i])

            for n in self.current_network.nodes :
                if n['id'] in list :
                    n['group'] = 'model'
                    for e in self.current_network.edges :
                        if e['to'] == n['id']:
                            self.recur_path(e['from'])

            self.current_network.save_graph('nx_with_sol.html')

            self.current_network.nodes = old_nodes

            html_file = os.path.join(dirname, 'nx_with_sol.html')
            local_url = QUrl.fromLocalFile(html_file)
            self.canvas.load(local_url)

    def recur_path(self, current):
        for n in self.current_network.nodes :
            if n['id'] == current :
                n['group'] = 'model'
                for e in self.current_network.edges :
                    if e['to'] == n['id']:
                        self.recur_path(e['from'])

    def outputClear(self):
        self.tracesFound.setText("")
        self.tracesFound.repaint()
        html_file = os.path.join(dirname, 'nx.html')
        local_url = QUrl.fromLocalFile(html_file)
        self.canvas.load(local_url)

    def getRandomTree(self):
        str,str1,str2 = TreeGen(3, 3, 2)
        self.rndtree_button.setEnabled(False)
        self.grammarText.setText(str + "\n" + str1 + "\n" + str2)
        self.grammarText.repaint()
        self.parser()

    def cleaning(self):
        new_nl = self.worker.node_list
        new_el = self.worker.edge_list
        self.tracesFound.setText(self.worker.str_formula)
        self.curr_formula = self.worker.str_formula
        self.curr_cnf = self.worker.str_cnf

        self.sol_array = self.worker.sol_array
        self.var_array = self.worker.var_array

        self.sol_spin.setMinimum(0)
        self.sol_spin.setMaximum(len(self.sol_array) - 1)
        self.sol_button.setText("Solve (max=" + str(len(self.sol_array)) + ")")

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
            lambda: self.enable_parser()
        )

    def enable_parser(self):
        self.buttonParse.setEnabled(True)
        self.rndtree_button.setEnabled(True)

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