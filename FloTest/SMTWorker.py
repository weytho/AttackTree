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

        if self.type == 0:
            print("COST")
            if self.limit:
                self.var_array, self.sol_array, self.best_value = SMTcost(self.var_list, list_cost, formula, Fraction(str(self.limit)))
            else:
                self.var_array, self.sol_array, self.best_value = SMTcost(self.var_list, list_cost, formula)
        else:
            print("PROBA")
            if self.limit:
                self.var_array, self.sol_array, self.best_value = SMTcost(self.var_list, list_cost, formula, Fraction(str(self.limit)))
            else:
                self.var_array, self.sol_array, self.best_value = SMTproba(self.var_list, list_proba, formula)

        self.finished.emit()
