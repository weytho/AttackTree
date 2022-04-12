from json.encoder import INFINITY
from PyQt5.QtCore import QObject, pyqtSignal
import os
from sympy.parsing.sympy_parser import parse_expr
# From folder 
from Struct import *
from collections import OrderedDict
from tseitin import *
from SATsolver import sat_solver
from SMTsolver import SMTcost, SMTproba
from fractions import Fraction

class SMTWorker(QObject):
    finished = pyqtSignal()

    def run(self):
        print("SMT WORKER")

        list_cost = [Fraction(str(x)) for x in self.cost_list]
        list_proba = [Fraction(str(x)) for x in self.proba_list]

        formula = self.str_formula
        if not formula:
            return

        cost_max = Fraction(str(3.6))
        proba_min = Fraction(str(0.3))

        if self.type == 0:
            print("COST")
            #SMTcost(self.var_list, list_cost, formula, cost_max)
            self.var_array, self.sol_array, self.best_value = SMTcost(self.var_list, list_cost, formula)
        else:
            print("PROBA")
            #SMTproba(self.var_list, list_proba, formula, proba_min)
            self.var_array, self.sol_array, self.best_value = SMTproba(self.var_list, list_proba, formula)

        self.finished.emit()

    '''
    def start_with_assumptions(self):
        glob = {}
        exec('from sympy.core import Symbol', glob) # ok for I, E, S, N, C, O, or Q
        tmp_formula = to_cnf(parse_expr(self.str_formula, global_dict=glob))

        self.var_array, self.sol_array = sat_solver(tmp_formula, self.uniq_node_list, self.assumptions, self.max_val)
        self.finished.emit()
    '''
