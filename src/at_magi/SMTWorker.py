##
# @file
# Retrieve the tree boolean formula
# Use a SMT-Solver to solve the formula in term of costs or probabilities
#
from PyQt5.QtCore import QObject, pyqtSignal
from fractions import Fraction

try:
    # From folder
    from Struct import *
    from Tseitin import *
    from SMTsolver import SMTcost, SMTproba
except ImportError:
    # From package 
    from at_magi.Struct import *
    from at_magi.Tseitin import *
    from at_magi.SMTsolver import SMTcost, SMTproba

## SMTWorker Class
#
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
            list_without_not.append(s)

        if self.type == 0:
            if self.limit:
                self.var_array, self.sol_array, self.best_value, self.values_array = SMTcost(list_without_not, list_cost, formula, Fraction(str(self.limit)))
            else:
                self.var_array, self.sol_array, self.best_value, self.values_array = SMTcost(list_without_not, list_cost, formula)
        else:
            if self.limit:
                self.var_array, self.sol_array, self.best_value, self.values_array = SMTproba(list_without_not, list_proba, formula, Fraction(str(self.limit)))
            else:
                self.var_array, self.sol_array, self.best_value, self.values_array = SMTproba(list_without_not, list_proba, formula)

        self.finished.emit()
