from Worker import *
from PyQt5.QtCore import QThread, QUrl, Qt
from sympy import *

class Comparison():

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

    def tree_comparions(self,fileName1,fileName2):
        
        worker1 = Worker()
        worker1.pathFile = fileName1
        worker1.useTseitin = false
        worker2 = Worker()
        worker2.pathFile = fileName2
        worker2.useTseitin = false

        thread1 = QThread()
        thread2 = QThread()
        worker1.moveToThread(thread1)
        worker2.moveToThread(thread2)

        thread1.started.connect(worker1.run)
        worker1.finished.connect(thread1.quit)
        worker1.finished.connect(lambda: self.clean_Worker(worker1,1))
        thread1.finished.connect(thread1.deleteLater)
        thread2.started.connect(worker2.run)
        worker2.finished.connect(thread2.quit)
        worker2.finished.connect(lambda: self.clean_Worker(worker2,2))
        thread2.finished.connect(thread2.deleteLater)

        thread1.start()
        thread2.start()
        print("[CMP] 2 threads launched")

    def clean_Worker(self,worker,nbr):
        if nbr==1:
            self.formula1 = worker.str_formula
            self.cnf1 = worker.str_cnf
            self.sol_array1 = worker.sol_array
            self.var_array1 = worker.var_array
        if nbr==2:
            self.formula2 = worker.str_formula
            self.cnf2 = worker.str_cnf
            self.sol_array2 = worker.sol_array
            self.var_array2 = worker.var_array
        ### UPDATE WINDOW WITH ARGUMENT TODO ###

    def compare(self):
        if self.formula1 == None or self.formula2 == None:
            print("[CMP] Some formulas are None .. aborting")
            return
        ### THREAD ###
        self.formula3 = "( ~ "+self.formula1+" | "+self.formula2+" )"
        worker3 = cmpWorker()
        worker3.formula = self.formula3
        worker3.var_array1 = self.var_array1
        worker3.var_array2 = self.var_array2
        thread3 = QThread()
        thread3.started.connect(worker3.run)
        worker3.finished.connect(thread3.quit)
        worker3.finished.connect(lambda: self.clean_cmpWorker(worker3))
        thread3.finished.connect(thread3.deleteLater) 
        thread3.start()

    def clean_cmpWorker(self, worker):
        ## TODO
        self.cnf3 = worker.cnf
        self.var_array3 = worker.var_array
        self.sol_array3 = worker.sol_array
        # Show on screen
        worker.deleteLater
        return  


class cmpWorker(QObject):
    finished = pyqtSignal()

    def run(self):
        glob = {}
        exec('from sympy.core import Symbol', glob) # ok for I, E, S, N, C, O, or Q
        parsed_formula = parse_expr(self.formula, global_dict=glob)
        self.cnf = str(to_cnf(parsed_formula))
        # Create varlist from previous ones
        self.list_var = self.var_array1
        for var in self.var_array2:
            if var not in self.list_var:
                self.list_var.append(var)

        self.sat_solver(self.formula, self.list_var)
        self.finished.emit()

    def sat_solver(self, formula, list_var, assumptions=[]):
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





    
            
        

