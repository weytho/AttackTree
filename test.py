from ctypes import *
import ctypes

so_file = "/home/thomas/UCL/AttackTree/ftest.so"

my_function = CDLL(so_file)

p = "thomaslebg"

print(type(my_function))
my_function.main(1,1,"thomaslebg")


