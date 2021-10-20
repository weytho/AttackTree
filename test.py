from ctypes import *

so_file = "/home/thomas/UCL/AttackTree/C_computation/my_test.so"

my_function = CDLL(so_file)

print(type(my_function))
my_function.main()