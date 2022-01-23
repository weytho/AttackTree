##
# @file
# Class ParserWorker
# used to send the text representation of an attack tree to the C parser
#
import time
from PyQt5.QtCore import QObject, pyqtSignal
import ctypes
import os
from pysat.solvers import Glucose3
from sympy import *
from sympy.parsing.sympy_parser import parse_expr
# From folder 
#from Struct import *

class ParserWorker(QObject):
    finished = pyqtSignal(int)

    def run(self):

        self.node_list= []

        dirname = os.path.dirname(__file__)
        so_file = os.path.join(dirname, 'testlib.so')
        my_function = ctypes.CDLL(so_file)

        strTest = self.fullText
        new_s = strTest.split("RELATIONS")
        #print(new_s)
        new_s2 = new_s[1].split("COUNTERMEASURES")
        #print(new_s2)
        new_s3 = new_s2[1].split("PROPERTIES")
        #print(new_s3)

        if(len(new_s3) <= 1):
            print("Boolean mode")
            s = ctypes.create_string_buffer(new_s2[0].encode('utf-8'))
            s2 = ctypes.create_string_buffer(new_s3[0].encode('utf-8'))

            my_function.parser.restype = ctypes.c_int
            my_function.parser.argtypes = [ctypes.c_char_p]
            ret = my_function.parser(s, "", s2)
        else:
            #print(new_s2[0])
            #print(new_s3[0])
            #print(new_s3[1])

            # sanitize and check input
            s = ctypes.create_string_buffer(new_s2[0].encode('utf-8'))
            s2 = ctypes.create_string_buffer(new_s3[0].encode('utf-8'))
            s3 = ctypes.create_string_buffer(new_s3[1].encode('utf-8'))

            my_function.parser.restype = ctypes.c_int
            my_function.parser.argtypes = [ctypes.c_char_p]
            ret = my_function.parser(s, s3, s2)

        time.sleep(2)
        self.finished.emit(ret)

        if ret == 0 :
            print("NICE WE GOT HERE")
            pass
        else:
            print("ERROR IN PARSER")
            print("Code : " + str(ret))
            pass