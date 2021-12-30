import time
from PyQt5.QtCore import QObject, pyqtSignal
import ctypes
import os
from pysat.solvers import Glucose3
from sympy import *
from sympy.parsing.sympy_parser import parse_expr
# From folder 
from Struct import *

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

        s = ctypes.create_string_buffer(self.pathFile.encode('utf-8'))
     
        my_function.mainfct.restype = ctypes.c_void_p
        my_function.mainfct.argtypes = [ctypes.c_char_p]
 
        fulllist = FullList.from_address(my_function.mainfct(s))
        newlist = CustomList.from_address(fulllist.nl)

        node_list_uniq_cm = []

        # .decode('utf-8') better way ?
        if newlist != None :
            tmp_node = CustomNode.from_address(newlist.data)
            newdict = {'type': tmp_node.type.decode('utf-8'),'leaf': tmp_node.leaf, 'root': tmp_node.root, 'cost': tmp_node.cost, 'prob': tmp_node.prob, 'CM': tmp_node.CM, 'variable': tmp_node.variable.decode('utf-8')}

            newtuple = (tmp_node.title.decode('utf-8'), newdict)
            self.node_list.append(newtuple)

            if( newdict['type'] == 'CntMs' ):
                node_list_uniq_cm.append(newdict['variable'])
            elif( newdict['leaf'] == 1 ):
                node_list_uniq_cm.append(newtuple[0])


            while newlist.next != None:
                newlist = CustomList.from_address(newlist.next)
                tmp_node = CustomNode.from_address(newlist.data)
                newdict = {'type': tmp_node.type.decode('utf-8'),'leaf': tmp_node.leaf, 'root': tmp_node.root, 'cost': tmp_node.cost, 'prob': tmp_node.prob, 'CM': tmp_node.CM, 'variable': tmp_node.variable.decode('utf-8')}

                newtuple = (tmp_node.title.decode('utf-8'), newdict)
                self.node_list.append(newtuple)

                if( newdict['type'] == 'CntMs' ):
                    node_list_uniq_cm.append(newdict['variable'])
                elif( newdict['leaf'] == 1 ):
                    node_list_uniq_cm.append(newtuple[0])

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
        tmp_formula = to_cnf(parse_expr(str_formula, global_dict=glob))
        print(tmp_formula)
        self.str_formula = str_formula#str(tmp_formula)


        self.sat_solver(tmp_formula, node_list_uniq_cm)


        my_function.freeList(newlist)
        #my_function.freeEList(newEdgeList)
        #my_function.freeForm(newFormula)
        time.sleep(2)
        #self.data.emit(node_list, edge_list)
        self.finished.emit()
        #self.plot

    def sat_solver(self, formula, list_var):
        print("####################### SAT SOLVER !!! #########################")
        print(list_var)
        print(formula)

        if formula == None:
            return

        dict_var = {}
        dict_index = {}
        i = 1
        for v in list_var:
            dict_var[v] = i
            dict_index[i] = v
            i = i + 1

        print(dict_var)
        print(dict_index)

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

                print(l)
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

            print(l)
            g.add_clause(l)

        elif(type(formula) is Not):
            l = []
            val = str(formula.args[0])
            l.append(-dict_var[val])

            print(l)
            g.add_clause(l)

        b = g.solve()
        print(b)

        if(b):
            model = g.get_model()
            print(model)

            result = []
            for n in model:
                if(n < 0):
                    result.append("Not("+dict_index[-n]+")")
                else:
                    result.append(dict_index[n])

            print(result)

            #for m in g.enum_models():
                #print(m)
    