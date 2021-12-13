import ctypes

class CustomNode(ctypes.Structure):
    _fields_ = [('title', ctypes.c_char * 50),
        ('variable', ctypes.c_char * 50),
        ('type', ctypes.c_char * 5),
        ('root', ctypes.c_int),
        ('leaf', ctypes.c_int),
        ('cost', ctypes.c_int),
        ('prob', ctypes.c_double),
        ('CM', ctypes.c_int),]

class EdgeNode(ctypes.Structure):
    _fields_ = [('parent', ctypes.c_char * 50),
        ('child', ctypes.c_char * 50)]

class FormulaNode(ctypes.Structure):
    _fields_ = [('data', ctypes.c_char_p),
        ('next', ctypes.c_void_p)]

class CustomList(ctypes.Structure):
    _fields_ = [('next', ctypes.c_void_p),
        ('data', ctypes.c_void_p)]

class FullList(ctypes.Structure):
    _fields_ = [('nl', ctypes.c_void_p),
        ('el', ctypes.c_void_p),
        ('fo', ctypes.c_void_p)]