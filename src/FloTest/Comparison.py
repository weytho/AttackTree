from PyQt5.QtCore import QThread, QUrl
from PyQt5 import QtGui
from sympy.parsing.sympy_parser import parse_expr
from threading import Semaphore
import networkx as nx
from pyvis.network import Network
import json

try:
    # From folder
    from Worker import *
    from SATsolver import sat_solver
except ImportError:
    # From package
    from FloTest.Worker import *
    from FloTest.SATsolver import sat_solver

dirname = os.path.dirname(__file__)
os.chdir(dirname)
with open('resources_directory.txt') as f:
    dirname = f.readline()
    dirname = dirname.rstrip("\n")
    os.chdir(dirname)

class Comparison(QObject):
    finished = pyqtSignal()

    def __init__(self, parent=None):
        super().__init__()
        print("[CMP] initialisation")
        self.formula1 = None
        self.cnf1 = None
        self.sol_array1 = None
        self.var_array1 = None
        self.formula2 = None
        self.cnf2 = None
        self.sol_array2 = None
        self.var_array2 = None
        self.formula3 = None
        self.cnf3 = None
        self.sol_array3 = None
        self.var_array3 = None
        self.sem = Semaphore()

    def tree_comparison(self,fileName1,fileName2,text1,text2):
        
        worker1 = Worker()
        worker1.max_val = self.max_sol
        worker1.pathFile = fileName1
        worker1.useTseitin = false
        worker2 = Worker()
        worker2.max_val = self.max_sol
        worker2.pathFile = fileName2
        worker2.useTseitin = false
        self.worker1 = worker1
        self.worker2 = worker2

        self.cnt = 0
        thread1 = QThread()
        thread2 = QThread()
        worker1.moveToThread(thread1)
        worker2.moveToThread(thread2)

        thread1.started.connect(worker1.run)
        worker1.finished.connect(thread1.quit)
        worker1.finished.connect(lambda: self.clean_Worker(1, text1))
        thread1.finished.connect(thread1.deleteLater)
        thread2.started.connect(worker2.run)
        worker2.finished.connect(thread2.quit)
        worker2.finished.connect(lambda: self.clean_Worker(2, text2))
        thread2.finished.connect(thread2.deleteLater)
        self.t1 = thread1
        self.t2 = thread2

        self.t1.start()
        self.t2.start()
        print("[CMP] 2 threads launched")

    def clean_Worker(self,nbr,text):
        print("[CMP] cleaning")
        if nbr==1:
            self.formula1 = self.worker1.str_formula
            self.cnf1 = self.worker1.str_cnf
            self.sol_array1 = self.worker1.sol_array
            self.var_array1 = self.worker1.var_array
            text.setText(self.formula1)
            self.sol1.setText("number of solutions found : " + str(len(self.sol_array1)))
            self.subplot(self.worker1.node_list, self.worker1.edge_list, self.webengine1, "first_comp")
            self.worker1.deleteLater
        if nbr==2:
            self.formula2 = self.worker2.str_formula
            self.cnf2 = self.worker2.str_cnf
            self.sol_array2 = self.worker2.sol_array
            self.var_array2 = self.worker2.var_array
            text.setText(self.formula2)
            self.sol2.setText("number of solutions found : " + str(len(self.sol_array2)))
            self.subplot(self.worker2.node_list, self.worker2.edge_list, self.webengine2, "second_comp")
            self.worker2.deleteLater
        ### UPDATE WINDOW WITH ARGUMENT TODO ###
        self.sem.acquire()
        self.cnt += 1
        if self.cnt == 2:
            self.sem.release()
            self.compare()
        else:
            self.sem.release()

    def compare(self):
        if self.formula1 == None or self.formula2 == None:
            print("[CMP] Some formulas are None .. aborting")
            return
        ### THREAD ###
        #self.formula3 = "( "+self.formula1+" & ( ~ "+self.formula1+" | "+self.formula2+" ) )"
        self.formula3 = "( "+self.formula1+" & "+self.formula2+" )"
        worker3 = cmpWorker()
        worker3.formula = self.formula3
        worker3.var_array1 = self.var_array1
        worker3.var_array2 = self.var_array2
        worker3.max_val = self.max_sol
        thread3 = QThread()
        thread3.started.connect(worker3.run)
        worker3.finished.connect(thread3.quit)
        worker3.finished.connect(lambda: self.clean_cmpWorker(1))
        thread3.finished.connect(thread3.deleteLater)
        self.worker3 = worker3
        self.t3 = thread3
        self.t3.start()

        self.formula4 = "( "+self.formula1+" & ( ~ ("+self.formula2+" ) ) )"
        worker4 = cmpWorker()
        worker4.formula = self.formula4
        worker4.var_array1 = self.var_array1
        worker4.var_array2 = self.var_array2
        worker4.max_val = self.max_sol
        thread4 = QThread()
        thread4.started.connect(worker4.run)
        worker4.finished.connect(thread4.quit)
        worker4.finished.connect(lambda: self.clean_cmpWorker(2))
        thread4.finished.connect(thread4.deleteLater)
        self.worker4 = worker4
        self.t4 = thread4
        self.t4.start()

    def clean_cmpWorker(self, nbr):
        ## TODO
        if nbr == 1:
            self.cnf3 = self.worker3.cnf
            self.var_array3 = self.worker3.var_array
            self.sol_array3 = self.worker3.sol_array
            self.boolean_sol_arr3 = []

            # Show on screen
            if len(self.sol_array3) > 0:
                boolean_array = []
                for l1 in self.sol_array3:
                    l = []
                    for l2 in l1:
                        if l2 >= 0:
                            l.append("True")
                        else:
                            l.append("False")
                    boolean_array.append(l)
                self.boolean_sol_arr3 = boolean_array
            self.worker3.deleteLater
        else:
            self.cnf4 = self.worker4.cnf
            self.var_array4 = self.worker4.var_array
            self.sol_array4 = self.worker4.sol_array
            self.boolean_sol_arr4 = []

            # Show on screen
            if len(self.sol_array4) > 0:
                boolean_array = []
                for l1 in self.sol_array4:
                    l = []
                    for l2 in l1:
                        if l2 >= 0:
                            l.append("True")
                        else:
                            l.append("False")
                    boolean_array.append(l)
                self.boolean_sol_arr4 = boolean_array
            self.worker4.deleteLater
        ### UPDATE WINDOW WITH ARGUMENT TODO ###
        self.sem.acquire()
        self.cnt += 1
        if self.cnt == 4:
            self.sem.release()

            self.concated_formula_text.setText(self.cnf3)

            self.finished.emit()
        else:
            self.sem.release()

    def subplot(self, node_list, edge_list, web, name):
        self.get_canvas(node_list, edge_list, name)    
        html_file = os.path.join(dirname, 'res/'+ name +'.html')
        local_url = QUrl.fromLocalFile(html_file)
        web.load(local_url)

    def get_canvas(self, ln, le, filename):

        g = nx.DiGraph()
        g.add_nodes_from(ln)

        types = [(u, d['type']) for (u, d) in g.nodes(data=True)]
        counter_list = [u for (u, d) in g.nodes(data=True) if d['type'] == 'CtMs']
       
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
                    if d['type'] == 'OR':
                        node = (name, {'type': 'logic', 'parent': u, 'CM': 0, 'inputNbr': -1})
                    elif d['type'] == 'NOT':
                        node = (name, {'type': 'logic', 'parent': u, 'CM': 0, 'inputNbr': -2})
                    elif d['type'] == 'XOR':
                        node = (name, {'type': 'logic', 'parent': u, 'CM': 0, 'inputNbr': -3})
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
                    if d['type'] == 'OR':
                        node = (name, {'type': 'logic', 'parent': u, 'CM': 0, 'inputNbr': -1})
                    elif d['type'] == 'NOT':
                        node = (name, {'type': 'logic', 'parent': u, 'CM': 0, 'inputNbr': -2})
                    elif d['type'] == 'XOR':
                        node = (name, {'type': 'logic', 'parent': u, 'CM': 0, 'inputNbr': -3})
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

        nt = Network(height="100%", width="100%")
        
        # Title can be html
        for (n, d) in ln:
            title_str = n + ": cost = " + str(d['cost']) + ", prob = " + str(d['prob'])

            if d['type'] == 'CtMs':
                nt.add_node(n_id=n, x=pos[n][0], y=-pos[n][1], label=d['variable'], shape='box', title=d['variable'] + ": cost = " + str(d['cost']) + ", prob = " + str(d['prob']), group="cm")
            elif (d['leaf'] == 1):
                nt.add_node(n_id=n, x=pos[n][0], y=-pos[n][1], label=n, shape='box', title=title_str, group="leaf")
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
        nt.save_graph('res/'+ filename +'.html')

class cmpWorker(QObject):
    finished = pyqtSignal()

    def run(self):
        glob = {}
        exec('from sympy.core import Symbol', glob) # ok for I, E, S, N, C, O, or Q
        parsed_formula = parse_expr(self.formula, global_dict=glob)
        #print("Parsed Formula : "+self.formula)
        cnf_formula = to_cnf(parsed_formula)
        self.cnf = str(cnf_formula)
        #print("Cnf Formula : "+self.cnf)
        # Create varlist from previous ones
        self.list_var = self.var_array1
        for var in self.var_array2:
            if var not in self.list_var:
                self.list_var.append(var)

        self.var_array, self.sol_array = sat_solver(cnf_formula, self.list_var, [], self.max_val)
        self.finished.emit()