from json.encoder import INFINITY
from PyQt5.QtCore import QObject, pyqtSignal
import os
from sympy.parsing.sympy_parser import parse_expr
from collections import OrderedDict
from fractions import Fraction

try:
    # From folder
    from Struct import *
    from tseitin import *
    from SATsolver import sat_solver
    from SMTsolver import SMTcost, SMTproba
except ImportError:
    # From package 
    from FloTest.Struct import *
    from FloTest.tseitin import *
    from FloTest.SATsolver import sat_solver
    from FloTest.SMTsolver import SMTcost, SMTproba

class SMTWorker(QObject):
    finished = pyqtSignal()

    def run(self):

        list_cost = [Fraction(str(x)) for x in self.cost_list]
        list_proba = [Fraction(str(x)) for x in self.proba_list]

        formula = self.str_formula
        if not formula:
            return

        list_without_not = []
        for s in self.var_list:
            if(s[0] == '~'):
                list_without_not.append(s[1:])
            else:
                list_without_not.append(s)

        if self.type == 0:
            print("SMT WORKER : COST")
            if self.limit:
                self.var_array, self.sol_array, self.best_value, self.values_array = SMTcost(list_without_not, list_cost, formula, Fraction(str(self.limit)))
            else:
                self.var_array, self.sol_array, self.best_value, self.values_array = SMTcost(list_without_not, list_cost, formula)
        else:
            print("SMT WORKER : PROBA")
            if self.limit:
                self.var_array, self.sol_array, self.best_value, self.values_array = SMTcost(list_without_not, list_cost, formula, Fraction(str(self.limit)))
            else:
                self.var_array, self.sol_array, self.best_value, self.values_array = SMTproba(list_without_not, list_proba, formula)

        self.finished.emit()
