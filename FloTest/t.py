##
# @file
# Main file of the python GUI interface
# Create GUI using PyQt5

import sys
from PyQt5 import QtCore, QtWidgets, QtGui
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
from Comparison import *
import copy
from functools import partial
import csv

dirname = os.path.dirname(__file__)
os.chdir(dirname)

from PyQt5.QtWidgets import (
    QApplication, QDialog, QHBoxLayout, QPushButton, QVBoxLayout, QLabel, QSpinBox, QWidget, QGridLayout, QListWidget, QListWidgetItem
)

## Window Class
#
#  Main GUI interface of the application
class Window(QDialog):
    ## The constructor.
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
        Vlayout_right = QVBoxLayout()
        layout.addLayout(Vlayout_toolbar)
        layout.addLayout(Vlayout_left)
        layout.addLayout(Vlayout_right)
        Vlayout_left.addWidget(self.canvas)
        Vlayout_left.addWidget(self.buttonImportJson)   

        Vlayout_left.addWidget(self.pathFile)

        # Create pyqt toolbar
        toolBar = QToolBar()
        toolBar.setOrientation(Qt.Vertical)
        toolBar.setFixedWidth(170)
        
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
        toolButton.toggle()
        toolButton.clicked.connect(self.outputCompleteformula)
        toolBar.addWidget(toolButton)
        self.complete_button = toolButton

        solution = QWidget()
        sol_layout = QHBoxLayout()
        solution.setLayout(sol_layout)

        toolButton = QToolButton()
        toolButton.setText("Solve (max)")
        toolButton.setCheckable(False)
        toolButton.setAutoExclusive(True)
        toolButton.clicked.connect(self.outputSolution)
        toolButton.setFixedWidth(110)
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

        random_tree = QWidget()
        rnd_layout = QHBoxLayout()
        random_tree.setLayout(rnd_layout)

        toolSpin = QSpinBox()
        toolSpin.setValue(3)
        rnd_layout.addWidget(toolSpin)
        self.rnd_spin_1 = toolSpin
        toolSpin = QSpinBox()
        toolSpin.setValue(3)
        rnd_layout.addWidget(toolSpin)
        self.rnd_spin_2 = toolSpin
        toolSpin = QSpinBox()
        toolSpin.setValue(2)
        rnd_layout.addWidget(toolSpin)
        self.rnd_spin_3 = toolSpin

        toolBar.addWidget(random_tree)

        toolBar.addSeparator()
        toolButton = QToolButton()
        toolButton.setText("Fix Input")
        toolButton.clicked.connect(self.outputUsingAssumptions)
        toolBar.addWidget(toolButton)
        self.ouputAssumption_button = toolButton

        toolBar.addSeparator()
        toolButton = QToolButton()
        toolButton.setText("nx nodes")
        toolButton.clicked.connect(self.show_nx_nodes)
        toolBar.addWidget(toolButton)
        toolButton = QToolButton()
        toolButton.setText("nx edges")
        toolButton.clicked.connect(self.show_nx_edges)
        toolBar.addWidget(toolButton)
        toolButton = QToolButton()
        toolButton.setText("solutions list")
        toolButton.clicked.connect(self.show_sol)
        toolBar.addWidget(toolButton)

        toolBar.addSeparator()
        section_output = QLabel("CNF Transform")
        section_output.setAlignment(Qt.AlignHCenter)
        section_output.setStyleSheet("font-weight: bold")
        toolBar.addWidget(section_output)

        # Add buttons to toolbar
        cnf_form = QWidget()
        cnf_layout = QVBoxLayout()
        cnf_form.setLayout(cnf_layout)

        toolButton = QToolButton()
        toolButton.setText("Tseitin")
        toolButton.setCheckable(True)
        toolButton.setAutoExclusive(True)
        toolButton.clicked.connect(lambda: self.setCNFTransform(True))
        cnf_layout.addWidget(toolButton)

        toolButton = QToolButton()
        toolButton.setText("Quine-McCluskey")
        toolButton.setCheckable(True)
        toolButton.setAutoExclusive(True)
        toolButton.toggle()
        toolButton.clicked.connect(lambda: self.setCNFTransform(False))
        cnf_layout.addWidget(toolButton)

        toolBar.addWidget(cnf_form)

        toolBar.addSeparator()
        toolButton = QToolButton()
        toolButton.setText("Comparison")
        toolButton.clicked.connect(lambda: self.compareTrees())
        toolBar.addWidget(toolButton)

        Vlayout_toolbar.addWidget(toolBar)

        solver = QWidget()
        max_layout = QHBoxLayout()
        solver.setLayout(max_layout)

        toolButton = QLabel("Max SAT Sol")
        toolButton.setFixedWidth(110)
        max_layout.addWidget(toolButton)
        toolSpinMax = QSpinBox()
        toolSpinMax.setValue(20)
        toolSpinMax.setRange(-1, 99)
        max_layout.addWidget(toolSpinMax)
        self.max_spin = toolSpinMax

        toolBar.addWidget(solver)

        result_layout = QHBoxLayout()
        result_layout.addWidget(self.tracesFound)
        base_layout.addLayout(result_layout)

        self.grammarText = QtWidgets.QTextEdit(self)
        self.grammarText.setFixedWidth(400)
        Vlayout_right.addWidget(self.grammarText)
        Vlayout_right.addWidget(self.buttonImportGrammar)
        Vlayout_right.addWidget(self.buttonParse)

        self.setLayout(base_layout)

        self.curr_formula = None
        self.curr_cnf = None
        self.sol_array = None
        self.uniq_node_list = None
        self.uniq_node_list_cm = None   
        self.useTseitin = False

    ## Creation of the Digraph using Networkx and Pyvis :
    #   Create graph from given information by adding logic nodes,
    #   Get the layout from Networkx and send it to a Pyvis network,
    #   Use settings for Pyvis from a JSON file and save the graph
    #   to a HTML file
    #  @param self The object pointer.
    #  @param ln List of the Nodes of the JSON file
    #  @param le List of the Edges of the JSON file
    def get_canvas(self, ln, le):

        print("###########################################")

        g = nx.DiGraph()
        g.add_nodes_from(ln)
        #print(ln)
        #print(le)

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
                    node_nor = (name_nor, {'type': 'cmlogic', 'parent': u, 'CM': 0, 'inputNbr': -1})
                    logic_nodes.append(node_nor)

                    name = u + '_' + "LOGIC"
                    if d['type'] == 'OR' :
                        node = (name, {'type': 'logic', 'parent': u, 'CM': 0, 'inputNbr': -1})
                    else:
                        node = (name, {'type': 'logic', 'parent': u, 'CM': 0, 'inputNbr': 0})
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
                    if d['type'] == 'OR' :
                        node = (name, {'type': 'logic', 'parent': u, 'CM': 0, 'inputNbr': -1})
                    else:
                        node = (name, {'type': 'logic', 'parent': u, 'CM': 0, 'inputNbr': 0})
                    logic_nodes.append(node)
                    # if has no CM
                    edge = (u, name)
                    labels_logic[name] = d['type']
                    logic_edge.append(edge)

            elif d['CM'] == 1:
                name_nor = u + '_' + "CMLOGIC"
                node_nor = (name_nor, {'type': 'cmlogic', 'parent': u, 'CM': 0, 'inputNbr': -1})
                logic_nodes.append(node_nor)

                logic_leaf.append(name_nor)

                edge = (u, name_nor)
                labels_logic[name_nor] = "CM"
                logic_edge.append(edge)

        # attention aux CM !!

        for (u, v) in le:
            if v in counter_list:
                edge = (u + '_' + "CMLOGIC", v)
            else:
                edge = (u + '_' + "LOGIC", v)
            for (u, d) in logic_nodes:
                if u == edge[0]:
                    if d['inputNbr'] >= 0 :
                        d['inputNbr'] = d['inputNbr'] + 1
                    break
            new_le.append(edge)

        g.add_nodes_from(logic_nodes)
        g.add_edges_from(logic_edge)
        g.add_edges_from(new_le)

        pos = nx.nx_agraph.graphviz_layout(g, prog='dot', args='-Gnodesep=0.2 -Gsize=10,6\! -Gdpi=100 -Gratio=fill')

        # RESIZE figure
        # TODO CA AVANCE
        # CM entre noeud et noeud logic

        nt = Network(height="100%", width="100%")
        
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
  
        settings_file = os.path.join(dirname, 'settings/pyvis_param.json')
        with open(settings_file, 'r') as file:
            data_options = json.load(file)

        vis_str = "var options = " + json.dumps(data_options)
        nt.set_options(vis_str)
        nt.save_graph('res/nx.html')

        self.current_network = nt
        self.current_digraph = g
        
        print("@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@")

    ## Action called at the end of the import process :
    #   Clear the figure of the GUI, launch the html graph creation from
    #   the nodes and edges, retrieves the html and loads it on the canvas
    #  @param self The object pointer.
    #  @param node_list List of the Nodes of the JSON file
    #  @param node_list List of the Edges of the JSON file
    def plot(self, node_list, edge_list):
        # clearing old figure
        self.figure.clear()
        self.get_canvas(node_list, edge_list)    
        #self.canvas.setContextMenuPolicy(Qt.NoContextMenu)
        html_file = os.path.join(dirname, 'res/nx.html')
        local_url = QUrl.fromLocalFile(html_file)
        self.canvas.load(local_url)
        #self.canvas.draw()
        print("pressed")

    ## Action called by the import JSON button :
    #   Use a file explorer to choose the JSON file to import
    #   Create a new thread for the Worker class
    #  @param self The object pointer.
    def getfileJSON(self):
        fileName, _ = QtWidgets.QFileDialog.getOpenFileName(self, 'Single File', QtCore.QDir.currentPath() + '/res' , '*.json')
        if not fileName :
            return

        self.pathFile.setText(fileName)
        self.thread = QThread()
        self.worker = Worker()

        self.worker.pathFile = fileName
        self.worker.useTseitin = self.useTseitin
        self.worker.max_val = self.max_spin.value()
        self.worker.moveToThread(self.thread)

        self.thread.started.connect(self.worker.run)
        self.worker.finished.connect(self.thread.quit)
        self.worker.finished.connect(lambda: self.cleaning(0))
        self.thread.finished.connect(self.thread.deleteLater)

        self.thread.start()

        # Final resets
        self.buttonImportJson.setEnabled(False)
        self.thread.finished.connect(
            lambda: self.buttonImportJson.setEnabled(True)
        )

    ## Action called by the import Grammar button :
    #   Use a file explorer to choose the TXT file to import
    #   Set the text in the corresponding QTextEdit
    #  @param self The object pointer.
    def getfileGrammar(self):
        fileName, _ = QtWidgets.QFileDialog.getOpenFileName(self, 'Single File', QtCore.QDir.currentPath() + '/res' , '*.txt')
        if not fileName :
            return

        self.buttonImportGrammar.setEnabled(False)
        with open(fileName, 'r') as f: 
            self.grammarText.setText(f.read())
        self.buttonImportGrammar.setEnabled(True)

    ## Action called by the CNF Formula button :
    #   Set the output formula to its CNF form
    #  @param self The object pointer.
    def outputCNFformula(self):
        if self.curr_cnf is not None :
            self.tracesFound.setText(self.curr_cnf)
            self.tracesFound.repaint()

    ## Action called by the Complete Formula button :
    #   Set the output formula to its Complete form
    #  @param self The object pointer.
    def outputCompleteformula(self):
        if self.curr_formula is not None :
            self.tracesFound.setText(self.curr_formula)
            self.tracesFound.repaint()

    ## Action called by the Solve button :
    #   Get the index of the solution from the QSpinBox
    #   Create a new graph HTML with the nodes taken from
    #   the solution and put them in a specific group to highlight them
    #  @param self The object pointer.  
    def outputSolution(self):
        if self.curr_formula is not None :
            index = self.sol_spin.value()
            if index > -1 :
                self.tracesFound.setText("")
                cursor = self.tracesFound.textCursor()
                cursor.insertTable(2, len(self.var_array))
                for header in self.var_array:
                    cursor.insertText(header)
                    cursor.movePosition(QtGui.QTextCursor.NextCell)
                for row in self.sol_array[index]:
                    if row >= 0:
                        cursor.insertText("True")
                    else:
                        cursor.insertText("False")
                    cursor.movePosition(QtGui.QTextCursor.NextCell)

                #self.tracesFound.setText(' '.join(map(str, self.var_array)) + "\n" + ' '.join(map(str, self.sol_array[index])))
                self.tracesFound.repaint()
                list = []
                old_nodes = copy.deepcopy(self.current_network.nodes)
                for i, v in enumerate(self.sol_array[index]) :
                    if v >= 0 :
                        list.append(self.var_array[i])

                disabled_node = set()

                path_count_set = {}
                for n in self.current_network.nodes :
                    if 'group' in n and n['group'] == 'cm' and n['label'] in list:
                        n['group'] = 'model_leaf'
                        l = n['id'].split("_", 1)
                        disabled_node.add(l[1])
                        for e in self.current_network.edges :
                            if e['to'] == n['id']:
                                for n2 in self.current_network.nodes :
                                    if n2['id'] == e['from']:
                                        n2['group'] = 'model'

                for n in self.current_network.nodes :
                    if n['id'] in list or (n['id'][0] == '~' and n['id'][1:] not in list):
                        n['group'] = 'model_leaf'
                        for e in self.current_network.edges :
                            if e['to'] == n['id']:
                                self.recur_path(e, path_count_set, disabled_node)

                self.current_network.save_graph('res/nx_with_sol.html')
                self.current_network.nodes = old_nodes

                html_file = os.path.join(dirname, 'res/nx_with_sol.html')
                local_url = QUrl.fromLocalFile(html_file)
                self.canvas.load(local_url)
            else :
                self.tracesFound.setText("No Solution Found")
                self.tracesFound.repaint()

    ## Recursive iteration on the nodes :
    #   Recursively goes up in the tree by iterating on the edges
    #   Set node taken in a style group to color them
    #  @param self The object pointer.
    #  @param current_edge Current edge to evaluate.
    #  @param path_count_set Dictionary of nodes found with a counter 
    #           to enable them if needed or block the recursion.
    #  @param disabled_node Set of nodes which can be used.   
    def recur_path(self, current_edge, path_count_set, disabled_node):
        current = current_edge['from']
        for n in self.current_network.nodes :
            if n['id'] == current :

                for (u, d) in self.current_digraph.nodes(data=True) :
                    if u == current :
                        if d['type'] == 'logic' or d['type'] == 'cmlogic' :
                            if current in path_count_set :
                                path_count_set[current].add(current_edge['to'])
                            else:
                                path_count_set[current] = {current_edge['to']}

                            if d['inputNbr'] < 0 or d['inputNbr'] == len(path_count_set[current]) :
                                if 'group' not in n or n['group'] != 'model':
                                    n['group'] = 'model'
                                    for e in self.current_network.edges :
                                        if e['to'] == n['id']:
                                            self.recur_path(e, path_count_set, disabled_node)
                        else :
                            if n['id'] not in disabled_node and ('group' not in n or n['group'] != 'model'):
                                n['group'] = 'model'
                                for e in self.current_network.edges :
                                    if e['to'] == n['id']:
                                        self.recur_path(e, path_count_set, disabled_node)
                        break
                break

    ## Action called by the Clear button :
    #   Clear the output and reload the graph from the HTML file
    #  @param self The object pointer.
    def outputClear(self):
        self.tracesFound.setText("")
        self.tracesFound.repaint()
        html_file = os.path.join(dirname, 'res/nx.html')
        local_url = QUrl.fromLocalFile(html_file)
        self.canvas.load(local_url)

    ## Action called by the Random Tree button :
    #   Get the values from the three QSpinBox below the button
    #   Set the grammar text with the generated strings
    #   Parse the grammar
    #  @param self The object pointer.
    def getRandomTree(self):
        str,str1,str2 = TreeGen(self.rnd_spin_1.value(), self.rnd_spin_2.value(), self.rnd_spin_3.value())
        self.rndtree_button.setEnabled(False)
        self.grammarText.setText(str + "\n" + str1 + "\n" + str2)
        self.grammarText.repaint()
        self.parser()

    ## Action called by the Fix Input button : \n
    #   Create QGridLayout pop-up to help the user toggle nodes and CMs \n
    #   Recompute the solutions for this graph with the new assumptions
    #  @param self The object pointer.
    def outputUsingAssumptions(self):
        widget = QDialog()
        self.popup_assumpt = widget
        self.mandatory_cm_counter = 0
        layout = QGridLayout()
        layout_cm = QGridLayout()
        Vlayout = QVBoxLayout()
        buttonConfirm = QPushButton('Confirm')
        buttonConfirm.clicked.connect(self.computeUsingAssumptions)

        buttons = {}
        i = 0
        j = 0
        if self.uniq_node_list is None :
            return

        for val in self.uniq_node_list:
            buttons[(i, j)] = [QPushButton(val), 0]
            buttons[(i, j)][0].setCheckable(True)
            buttons[(i, j)][0].setAutoExclusive(False)
            buttons[(i, j)][0].clicked.connect(
                partial(self.changeState, (i, j), 0)
            )
            layout.addWidget(buttons[(i, j)][0], i, j)
            j += 1
            if j >= 10 :
                j = 0
                i += 1

        buttons_cm = {}
        i = 0
        j = 0
        if self.uniq_node_list_cm is None :
            return

        for val in self.uniq_node_list_cm:
            buttons_cm[(i, j)] = [QPushButton(val), 0]
            buttons_cm[(i, j)][0].setCheckable(True)
            buttons_cm[(i, j)][0].setAutoExclusive(False)
            buttons_cm[(i, j)][0].clicked.connect(
                partial(self.changeState, (i, j), 1)
            )
            layout_cm.addWidget(buttons_cm[(i, j)][0], i, j)
            j += 1
            if j >= 10 :
                j = 0
                i += 1

        Vlayout.addLayout(layout)
        Vlayout.addLayout(layout_cm)
        self.grid_fix_input = buttons
        self.grid_fix_input_cm = buttons_cm
        Vlayout.addWidget(buttonConfirm)
        widget.setLayout(Vlayout)
        widget.exec_()

    ## Change State of QGridLayout Elements \n
    #   States possible are : undefined, true, false
    #  @param self The object pointer.
    #  @param coord The coordinates of the element in the grid.
    #  @param type Type of the element : CM or leaf.
    def changeState(self, coord, type):
        if type == 0:
            button = self.grid_fix_input[coord][0]
            self.grid_fix_input[coord][1] = (self.grid_fix_input[coord][1] + 1) % 3
            state = self.grid_fix_input[coord][1]
        else:
            button = self.grid_fix_input_cm[coord][0]
            self.grid_fix_input_cm[coord][1] = (self.grid_fix_input_cm[coord][1] + 1) % 3
            state = self.grid_fix_input_cm[coord][1]

        if state == 0:
            button.setStyleSheet("")
            button.setChecked(False)
        elif state == 1:
            button.setStyleSheet("QPushButton { background-color: lightgreen }")
            button.setChecked(False)
        else:
            button.setStyleSheet("QPushButton { background-color: red }")
            button.setChecked(False)

        if type == 1:
            self.changeStateCounter(state, coord)

    ## Change State of CM element and changes the depending leaf nodes of the grid accordingly \n
    #   Keep counter of the number of nodes affected to see if a recomputation is needed
    #  @param self The object pointer.
    #  @param state State of the current CM node.
    #  @param coord The coordinates of the element in the grid.
    def changeStateCounter(self, state, coord):
        cm_name = self.grid_fix_input_cm[coord][0].text()
        list_to_toggle = []

        for (u, v, _) in self.current_digraph.edges(data=True):
            l = v.split("_", 1)
            if l[0] == cm_name:
                list_to_toggle.append(u.rsplit('_', 1)[0])

        print(list_to_toggle)

        for n in list_to_toggle:
            # TODO Voir quoi faire pour
            # les noeuds qui ne sont pas des leafs !!
            if n in self.uniq_node_list:
                index = self.uniq_node_list.index(n)
                j = index % 10
                i = (index - j) // 10
                current = self.grid_fix_input[(i, j)]

                if state == 0:
                    current[1] = 0
                    current[0].setStyleSheet("")
                    current[0].setChecked(False)
                elif state == 2:
                    current[1] = 1
                    current[0].setStyleSheet("QPushButton { background-color: lightgreen }")
                    current[0].setChecked(False)
                else:
                    current[1] = 2
                    current[0].setStyleSheet("QPushButton { background-color: red }")
                    current[0].setChecked(False)
            else:
                print("parent node is not a leaf")
                
            if state == 0:
                self.mandatory_cm_counter -= 1
            elif state == 2:
                pass
            else:
                self.mandatory_cm_counter += 1

    ## Recompute the tree solutions using the assumptions if needed : \n
    #  Launch a new Worker with the assumptions list
    #  @param self The object pointer.
    def computeUsingAssumptions(self):
        print(self.mandatory_cm_counter)

        self.thread = QThread()
        self.worker = Worker()
        self.worker.max_val = self.max_spin.value()

        if self.mandatory_cm_counter > 0:
            self.worker.str_formula = self.curr_formula_cm
            self.worker.uniq_node_list = self.uniq_node_list + self.uniq_node_list_cm
        else:
            self.worker.str_formula = self.curr_formula
            self.worker.uniq_node_list = self.uniq_node_list
        print("Compute With Assumptions")

        self.worker.assumptions = []

        for (i, j), [button, state] in self.grid_fix_input.items():
            if state != 0 :
                if state == 2:
                    self.worker.assumptions.append(-(i * 10 + j + 1))
                else:
                    self.worker.assumptions.append(i * 10 + j + 1)

        if self.mandatory_cm_counter > 0:
            last = i * 10 + j + 1
            for (i, j), [button, state] in self.grid_fix_input_cm.items():
                if state == 1 :
                    self.worker.assumptions.append(i * 10 + j + 1 + last)
                else:
                    self.worker.assumptions.append(-(i * 10 + j + 1 + last))

        self.worker.moveToThread(self.thread)
        self.thread.started.connect(self.worker.start_with_assumptions)
        self.worker.finished.connect(self.thread.quit)
        self.worker.finished.connect(lambda: self.cleaning(1))
        self.thread.finished.connect(self.thread.deleteLater)
        self.thread.start()

        self.ouputAssumption_button.setEnabled(False)
        self.thread.finished.connect(
            lambda: self.ouputAssumption_button.setEnabled(True)
        )
        self.popup_assumpt.close()

    ## Action called by the nx nodes button :
    #   Print the nodes in a pop-up QListWidget
    #  @param self The object pointer.
    def show_nx_nodes(self):
        if hasattr(self, 'current_digraph'):
            self.msg = QDialog()
            layout = QVBoxLayout(self.msg)
            list = QListWidget()
            self.msg.setWindowTitle("Networkx Nodes")
            for (u, d) in self.current_digraph.nodes(data=True):
                i = QListWidgetItem(str((u, d)))
                i.setFlags(Qt.ItemIsSelectable|Qt.ItemIsEnabled|Qt.ItemIsEditable)
                list.addItem(i)
            layout.addWidget(list)
            self.msg.setLayout(layout)
            self.msg.resize(700,500)
            self.msg.show()

    ## Action called by the nx edges button :
    #   Print the edges in a pop-up QListWidget
    #  @param self The object pointer.
    def show_nx_edges(self):
        if hasattr(self, 'current_digraph'):
            self.msg = QDialog()
            layout = QVBoxLayout(self.msg)
            list = QListWidget()
            self.msg.setWindowTitle("Networkx Edges")
            for (u, v, d) in self.current_digraph.edges(data=True):
                i = QListWidgetItem(str((u, v, d)))
                i.setFlags(Qt.ItemIsSelectable|Qt.ItemIsEnabled|Qt.ItemIsEditable)
                list.addItem(i)
            layout.addWidget(list)
            self.msg.setLayout(layout)
            self.msg.resize(500,500)
            self.msg.show()

    def show_sol(self):
        if hasattr(self, 'var_array'):
            self.msg = QDialog()
            layout = QVBoxLayout(self.msg)
            list = QListWidget()
            self.msg.setWindowTitle("Solutions")
            i = QListWidgetItem(str(self.var_array))
            i.setFlags(Qt.ItemIsSelectable|Qt.ItemIsEnabled|Qt.ItemIsEditable)
            list.addItem(i)
            for i in self.boolean_sol_arr:
                item = QListWidgetItem(str(i))
                item.setFlags(Qt.ItemIsSelectable|Qt.ItemIsEnabled|Qt.ItemIsEditable)
                list.addItem(item)
            layout.addWidget(list)
            self.msg.setLayout(layout)
            self.msg.resize(500,500)
            self.msg.show()

    ## Action called by two CNF transform buttons :
    #   Set the type of CNF transformation used by the Worker
    #  @param self The object pointer.
    #  @param bool The boolean value of Tseitin encoding usage.
    def setCNFTransform(self, bool):
        self.useTseitin = bool

    def compareTrees(self):
        self.comp = QDialog()
        self.comp.setWindowTitle("Left Tree Implies Right Tree")

        layout = QHBoxLayout()

        Vlayout = QVBoxLayout()

        VlayoutFirst = QVBoxLayout()
        VlayoutSecond = QVBoxLayout()

        path1 = QtWidgets.QTextEdit()
        path1.setFixedHeight(30)
        path2 = QtWidgets.QTextEdit()
        path2.setFixedHeight(30)

        form1 = QtWidgets.QTextEdit()
        form1.setFixedHeight(30)
        form2 = QtWidgets.QTextEdit()
        form2.setFixedHeight(30)

        sol1 = QtWidgets.QTextEdit()
        sol1.setFixedHeight(30)
        sol2 = QtWidgets.QTextEdit()
        sol2.setFixedHeight(30)

        first = QWebEngineView()
        second = QWebEngineView()

        VlayoutFirst.addWidget(first)
        VlayoutFirst.addWidget(path1)
        VlayoutFirst.addWidget(form1)
        VlayoutFirst.addWidget(sol1)

        VlayoutSecond.addWidget(second)
        VlayoutSecond.addWidget(path2)
        VlayoutSecond.addWidget(form2)
        VlayoutSecond.addWidget(sol2)

        tree1 = QWidget()
        tree1.setLayout(VlayoutFirst)
        tree2 = QWidget()
        tree2.setLayout(VlayoutSecond)

        layout.addWidget(tree1)
        layout.addWidget(tree2)

        tot_compare = QWidget()
        tot_compare.setLayout(layout)

        Vlayout.addWidget(tot_compare)

        buttonResults = QPushButton('Print Results')
        buttonResults.clicked.connect(self.showResults)
        Vlayout.addWidget(buttonResults)
        full_sol = QtWidgets.QTextEdit()
        full_sol.setFixedHeight(60)
        Vlayout.addWidget(full_sol)
        full_form = QtWidgets.QTextEdit()
        full_form.setFixedHeight(40)
        Vlayout.addWidget(full_form)

        self.call_compare(form1, form2, full_form, first, second, path1, path2, full_sol, sol1, sol2, buttonResults)

        self.comp.setLayout(Vlayout)
        self.comp.resize(1400,800)
        self.comp.show()

    
    def showResults(self):
        if hasattr(self.comparator, 'var_array3'):
            msg = QDialog()
            twocolumns = QHBoxLayout()
            
            layout = QVBoxLayout()
            twocolumns.addLayout(layout)
            layout2 = QVBoxLayout()
            twocolumns.addLayout(layout2)

            msg.setWindowTitle("Solutions")

            label = QLabel("Included")
            layout.addWidget(label)
            list = QListWidget()
            i = QListWidgetItem(str(self.comparator.var_array3))
            i.setFlags(Qt.ItemIsSelectable|Qt.ItemIsEnabled|Qt.ItemIsEditable)
            list.addItem(i)
            for i in self.comparator.boolean_sol_arr3:
                item = QListWidgetItem(str(i))
                item.setFlags(Qt.ItemIsSelectable|Qt.ItemIsEnabled|Qt.ItemIsEditable)
                list.addItem(item)
            layout.addWidget(list)

            if hasattr(self.comparator, 'var_array4'):

                label = QLabel("Not Included")
                layout2.addWidget(label)
                list = QListWidget()
                i = QListWidgetItem(str(self.comparator.var_array4))
                i.setFlags(Qt.ItemIsSelectable|Qt.ItemIsEnabled|Qt.ItemIsEditable)
                list.addItem(i)
                for i in self.comparator.boolean_sol_arr4:
                    item = QListWidgetItem(str(i))
                    item.setFlags(Qt.ItemIsSelectable|Qt.ItemIsEnabled|Qt.ItemIsEditable)
                    list.addItem(item)
                layout2.addWidget(list)

            msg.setLayout(twocolumns)
            msg.resize(500,500)
            self.comparator.msg = msg
            self.comparator.msg.show()

    def call_compare(self, form1, form2, form3, web1, web2, path1, path2, solutions, sol1, sol2, buttonResults):
        comparator = Comparison()
        comparator.concated_formula_text = form3
        comparator.webengine1 = web1
        comparator.webengine2 = web2
        comparator.solutions = solutions
        comparator.sol1 = sol1
        comparator.sol2 = sol2
        comparator.buttonResults = buttonResults
        comparator.max_sol = self.max_spin.value()
        file1, _ = QtWidgets.QFileDialog.getOpenFileName(self, 'File : Antecedent', QtCore.QDir.currentPath() + '/res' , '*.json')
        if not file1 :
            return
        path1.setText(file1)
        file2, _ = QtWidgets.QFileDialog.getOpenFileName(self, 'File : Consequent', QtCore.QDir.currentPath() + '/res' , '*.json')
        if not file2 :
            return
        path2.setText(file2)
        comparator.tree_comparison(file1, file2, form1, form2)
        comparator.window = self.comp
        self.comparator = comparator

    ## Get the Worker results and update them in the Window before deleting :
    #  @param self The object pointer.
    #  @param bool_plot Boolean value used to print formula and plot graph.
    def cleaning(self, bool_plot=0):
        self.sol_array = self.worker.sol_array
        self.var_array = self.worker.var_array

        boolean_array = []
        for l1 in self.sol_array:
            l = []
            for l2 in l1:
                if l2 >= 0:
                    l.append("True")
                else:
                    l.append("False")
            boolean_array.append(l)
        self.boolean_sol_arr = boolean_array

        # to csv file
        with open("res/solutions.csv", "wt") as fp:
            writer = csv.writer(fp, delimiter=",")
            writer.writerow(self.var_array)  # write header
            #print(boolean_array)
            writer.writerows(boolean_array)

        self.sol_spin.setMinimum(0)
        self.sol_spin.setMaximum(len(self.sol_array) - 1)
        self.sol_button.setText("Solve (" + str(len(self.sol_array)) + ")")

        if bool_plot == 0 :
            self.tracesFound.setText(self.worker.str_formula)
            self.curr_formula = self.worker.str_formula
            self.curr_cnf = self.worker.str_cnf
            self.curr_formula_cm = self.worker.str_formula_cm
            self.curr_cnf_cm = self.worker.str_cnf_cm
            self.uniq_node_list = self.worker.uniq_node_list
            self.uniq_node_list_cm = self.worker.uniq_node_list_cm

            self.plot(self.worker.node_list, self.worker.edge_list)

        self.worker.deleteLater

    ## Action called by the parser button :
    #   Create a ParserWorker thread to create a tree from the grammar given in the GUI
    #  @param self The object pointer.
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

    ## Enable buttons when processing is over
    #  @param self The object pointer.
    def enable_parser(self):
        self.buttonParse.setEnabled(True)
        self.rndtree_button.setEnabled(True)

    ## Show Error Pop-up QMessageBox :
    #   Message of a detected error and its type
    #  @param self The object pointer.
    #  @param error The id of the error.
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
        elif(error_id == 4):
            msg.setText("Multiple Roots !")
        else:
            msg.setText("This is the main text!")
        msg.setIcon(QMessageBox.Critical)
        msg.exec_()

## driver code
if __name__ == '__main__':
    app = QApplication(sys.argv)
    win = Window()
    win.show()
    sys.exit(app.exec())