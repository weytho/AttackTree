##
# @file
# Retrieve the ctype Structure representing the tree
# Retrieve the tree boolean formula
# Use a Sat-Solver to solve the formula
from json.encoder import INFINITY
import time
from PyQt5.QtCore import QObject, pyqtSignal
import ctypes
import os
from sympy.parsing.sympy_parser import parse_expr
# From folder 
from Struct import *
from collections import OrderedDict
from tseitin import *
from SATsolver import sat_solver

class Worker(QObject):
    finished = pyqtSignal()

    def run(self):
        print("WORKER")
        self.node_list= []
        self.edge_list = []
        self.formula = []
        self.formula_cm = []
        dirname = os.path.dirname(__file__)
        so_file = os.path.join(dirname, 'testlib.so')
        my_function = ctypes.CDLL(so_file)

        s = ctypes.create_string_buffer(self.pathFile.encode('utf-8'))
     
        my_function.mainfct.restype = ctypes.c_void_p
        my_function.mainfct.argtypes = [ctypes.c_char_p]
 
        fulllist = FullList.from_address(my_function.mainfct(s, 0))
        newlist = CustomList.from_address(fulllist.nl)

        node_list_uniq = []
        node_list_uniq_cm = []

        # .decode('utf-8') better way ?
        if newlist != None :
            tmp_node = CustomNode.from_address(newlist.data)
            newdict = {'type': tmp_node.type.decode('utf-8'),'leaf': tmp_node.leaf, 'root': tmp_node.root, 'cost': tmp_node.cost, 'prob': tmp_node.prob, 'CM': tmp_node.CM, 'variable': tmp_node.variable.decode('utf-8')}

            newtuple = (tmp_node.title.decode('utf-8'), newdict)
            self.node_list.append(newtuple)

            if( newdict['type'] == 'CntMs' ):
                if newdict['variable'] not in node_list_uniq_cm:
                    node_list_uniq_cm.append(newdict['variable'])
            elif( newdict['leaf'] == 1 ):
                if(newtuple[0][0] == '~'):
                    node_list_uniq.append(newtuple[0][1:])
                else:
                    node_list_uniq.append(newtuple[0])

            while newlist.next != None:
                newlist = CustomList.from_address(newlist.next)
                tmp_node = CustomNode.from_address(newlist.data)
                newdict = {'type': tmp_node.type.decode('utf-8'),'leaf': tmp_node.leaf, 'root': tmp_node.root, 'cost': tmp_node.cost, 'prob': tmp_node.prob, 'CM': tmp_node.CM, 'variable': tmp_node.variable.decode('utf-8')}

                newtuple = (tmp_node.title.decode('utf-8'), newdict)
                if newtuple not in self.node_list:
                    self.node_list.append(newtuple)

                if( newdict['type'] == 'CntMs' ):
                    if newdict['variable'] not in node_list_uniq_cm:
                        node_list_uniq_cm.append(newdict['variable'])
                elif( newdict['leaf'] == 1 ):
                    if(newtuple[0][0] == '~'):
                        node_list_uniq.append(newtuple[0][1:])
                    else:
                        node_list_uniq.append(newtuple[0])

        newEdgeList = CustomList.from_address(fulllist.el)

        if newEdgeList != None :
            tmp_node = EdgeNode.from_address(newEdgeList.data)
            newtuple = (tmp_node.parent.decode('utf-8'),tmp_node.child.decode('utf-8'))
            self.edge_list.append(newtuple)

            while newEdgeList.next != None:
                newEdgeList = CustomList.from_address(newEdgeList.next)
                tmp_node = EdgeNode.from_address(newEdgeList.data)
                newtuple = (tmp_node.parent.decode('utf-8'),tmp_node.child.decode('utf-8'))
                
                if newtuple not in self.edge_list:
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

        newFormula_cm = FormulaNode.from_address(fulllist.fo_cm)

        if newFormula_cm != None :
            newdata = newFormula_cm.data.decode('utf-8')
            self.formula_cm.append(newdata)

            while newFormula_cm.next != None:
                newFormula_cm = FormulaNode.from_address(newFormula_cm.next)
                newdata = newFormula_cm.data.decode('utf-8')
                self.formula_cm.append(newdata)

        str_formula_cm = ""
        for e in self.formula_cm:
            str_formula_cm = str_formula_cm + e

        # STR TO CNF SYMPY

        glob = {}
        exec('from sympy.core import Symbol', glob) # ok for I, E, S, N, C, O, or Q

        parsed_formula = parse_expr(str_formula, global_dict=glob)
        parsed_formula_cm = parse_expr(str_formula_cm, global_dict=glob)

        if self.useTseitin:
            tmp_formula, set_var, index_expr = tseitin(parsed_formula)
            node_list_uniq = list(set_var) + [str(l) for l in index_expr]
            tmp_formula_cm, set_var_cm, index_expr_cm = tseitin(parsed_formula)
            #node_list_uniq_cm = list(set_var_cm) + [str(l) for l in index_expr_cm]
        else:
            tmp_formula = to_cnf(parsed_formula)
            tmp_formula_cm = to_cnf(parsed_formula_cm)

        self.str_formula = str_formula
        self.str_formula_cm = str_formula_cm
        self.str_cnf = str(tmp_formula)
        self.str_cnf_cm = str(tmp_formula_cm)
        node_list_uniq = list(OrderedDict.fromkeys(node_list_uniq))
        self.uniq_node_list = node_list_uniq
        self.uniq_node_list_cm = node_list_uniq_cm

        print("DDDDDDDDDDDDDDDDDDDDDDDDDDDDDDDd")
        print(self.max_val)
        self.var_array, self.sol_array = sat_solver(tmp_formula, node_list_uniq, [], self.max_val)

        my_function.freeList(newlist)
        #my_function.freeEList(newEdgeList)
        #my_function.freeForm(newFormula)
        #time.sleep(2)
        #self.data.emit(node_list, edge_list)
        self.finished.emit()
        #self.plot

    def start_with_assumptions(self):
        glob = {}
        exec('from sympy.core import Symbol', glob) # ok for I, E, S, N, C, O, or Q
        tmp_formula = to_cnf(parse_expr(self.str_formula, global_dict=glob))

        self.var_array, self.sol_array = sat_solver(tmp_formula, self.uniq_node_list, self.assumptions, self.max_val)
        self.finished.emit()

if __name__ == "__main__":

    str_formula = "a & B & C_C | E | SN | C"
    glob = {}
    exec('from sympy.core import Symbol', glob) # ok for I, E, S, N, C, O, or Q
    print(str_formula)
    parsed_formula = parse_expr(str_formula, global_dict=glob)
    print(parsed_formula)