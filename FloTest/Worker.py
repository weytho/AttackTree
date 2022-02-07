##
# @file
# Retrieve the ctype Structure representing the tree
# Retrieve the tree boolean formula
# Use a Sat-Solver to solve the formula
import time
from PyQt5.QtCore import QObject, pyqtSignal
import ctypes
import os
from pysat.solvers import Glucose3
from sympy import *
from sympy.parsing.sympy_parser import parse_expr
# From folder 
from Struct import *
from collections import OrderedDict
from tseitin import *

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

        self.sat_solver(tmp_formula, node_list_uniq)

        my_function.freeList(newlist)
        #my_function.freeEList(newEdgeList)
        #my_function.freeForm(newFormula)
        time.sleep(2)
        #self.data.emit(node_list, edge_list)
        self.finished.emit()
        #self.plot

    def start_with_assumptions(self):
        glob = {}
        exec('from sympy.core import Symbol', glob) # ok for I, E, S, N, C, O, or Q
        tmp_formula = to_cnf(parse_expr(self.str_formula, global_dict=glob))

        self.sat_solver(tmp_formula, self.uniq_node_list, self.assumptions)
        self.finished.emit()

    def sat_solver(self, formula, list_var, assumptions=[]):
        print("####################### SAT SOLVER !!! #########################")
        print(formula)
        print(list_var)
        
        if formula == None:
            return

        dict_var = {}
        dict_index = {}
        i = 1
        for v in list_var:
            dict_var[v] = i
            dict_index[i] = v
            i = i + 1

        #print(dict_var)
        #print(dict_index)

        g = Glucose3()

        if(type(formula) is And):
            list_and = formula.args

            for x in list_and:
                l = []
                if(type(x) is Or):
                    list_or = x.args

                    for y in list_or:
                        if(type(y) is Not):
                            val = str(y.args[0])
                            l.append(-dict_var[val])
                        else:
                            val = str(y)
                            l.append(dict_var[val])

                elif(type(x) is Not):
                    val = str(x.args[0])
                    l.append(-dict_var[val])

                else:
                    val = str(x)
                    l.append(dict_var[val])

                #print(l)
                g.add_clause(l)

        elif(type(formula) is Or):
            l = []
            list_or = formula.args

            for x in list_or:
                if(type(x) is Not):
                    val = str(x.args[0])
                    l.append(-dict_var[val])
                else:
                    val = str(x)
                    l.append(dict_var[val])

            #print(l)
            g.add_clause(l)

        elif(type(formula) is Not):
            l = []
            val = str(formula.args[0])
            l.append(-dict_var[val])

            #print(l)
            g.add_clause(l)

        b = g.solve(assumptions=assumptions)
        print(b)
        self.var_array = list_var
        self.sol_array = []

        if(b):
            # TODO ATTENTION PAS ASSUMPTIONS SUR LE MODEL
            model = g.get_model()
            #print(model)

            result = []
            for n in model:
                if(n < 0):
                    result.append("Not("+dict_index[-n]+")")
                else:
                    result.append(dict_index[n])

            #print(result)

            # TODO LIMIT TO 20 FOR PERFORMANCE ISSUE
            cnt = 0
            for m in g.enum_models(assumptions=assumptions):
                if cnt >= 20 :
                    break
                self.sol_array.append(m)
                cnt += 1
    