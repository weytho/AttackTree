##
# @file
# Class ParserWorker
# used to send the text representation of an attack tree to the C parser
#
from PyQt5.QtCore import QObject, pyqtSignal
import ctypes
import os

## ParserWorker Class
#
#  Create and manage the parsing
#  of an attack tree from GUI given text
class ParserWorker(QObject):
    finished = pyqtSignal(int)

    def get_file_so(self):
        dirname = os.path.dirname(__file__)
        for file in os.listdir(dirname):
            if file.startswith("testlib") and file.endswith(".so"):
                self.file_so = file
                break

    def run(self):
        self.get_file_so()

        self.node_list= []

        dirname = os.path.dirname(__file__)
        so_file = os.path.join(dirname, self.file_so)
        my_function = ctypes.CDLL(so_file)

        strTest = self.fullText

        if not strTest:
            print("Error empty string to parse")
            self.finished.emit(1)
            return
        new_s = strTest.split("RELATIONS")
        #print(new_s)
        new_s2 = new_s[1].split("COUNTERMEASURES")
        #print(new_s2)
        new_s3 = new_s2[1].split("PROPERTIES")
        #print(new_s3)
        file = ctypes.create_string_buffer(self.filename.encode('utf-8'))

        if(len(new_s3) <= 1):
            print("Boolean mode")
            s = ctypes.create_string_buffer(new_s2[0].encode('utf-8'))
            s2 = ctypes.create_string_buffer(new_s3[0].encode('utf-8'))

            my_function.parser.restype = ctypes.c_int
            my_function.parser.argtypes = [ctypes.c_char_p]
            ret = my_function.parser(s, "", s2, file)
        else:
            # sanitize and check input
            s = ctypes.create_string_buffer(new_s2[0].encode('utf-8'))
            s2 = ctypes.create_string_buffer(new_s3[0].encode('utf-8'))
            s3 = ctypes.create_string_buffer(new_s3[1].encode('utf-8'))

            my_function.parser.restype = ctypes.c_int
            my_function.parser.argtypes = [ctypes.c_char_p]
            ret = my_function.parser(s, s3, s2, file)

        self.finished.emit(ret)

        if ret == 0 :
            print("Success")
        else:
            print("Error in Parser")
            print("Code : " + str(ret))