##
# @file
# Methods use to compute the Tseitin transformation
# used to convert a boolan formula to its CNF-form
#
from matplotlib import pyplot as plt
from sympy import *
import time
import signal
from sympy.logic.boolalg import *

try:
    # From folder
    from SATsolver import sat_solver
    from at_magi.Tseitin import tseitin
except ImportError:
    # From package
    from at_magi.SATsolver import sat_solver
    from at_magi.Tseitin import tseitin

class timeout:
    def __init__(self, seconds=1, error_message='Timeout'):
        self.seconds = seconds
        self.error_message = error_message
    def handle_timeout(self, signum, frame):
        raise TimeoutError(self.error_message)
    def __enter__(self):
        signal.signal(signal.SIGALRM, self.handle_timeout)
        signal.alarm(self.seconds)
    def __exit__(self, type, value, traceback):
        signal.alarm(0)

def _find_predicates(expr):
    if not isinstance(expr, BooleanFunction):
        return {expr}
    return set().union(*(map(_find_predicates, expr.args)))

def compute_truthtable(expr, find_all):
    expr = sympify(expr)
    if not isinstance(expr, BooleanFunction):
        return expr, []

    variables = _find_predicates(expr)
    from sympy.simplify.simplify import simplify
    s = tuple(map(simplify, variables))
    expr = expr.xreplace(dict(zip(variables, s)))
    variables = _find_predicates(expr)

    c, v = sift(ordered(variables), lambda x: x in (True, False), binary=True)
    variables = c + v
    truthtable = []

    c = [1 if i == True else 0 for i in c]
    for t in product((0, 1), repeat=len(v)):
        if expr.xreplace(dict(zip(v, t))) == True:
            truthtable.append(c + list(t))
            if not find_all:
                break
            else:
                if len(truthtable) >= 10000: # Limit
                    break
                
    return v, truthtable

def benchmark():

    str_formula = []
    # nbr vars <= 4 && nbr operators <= 6 (short formula)
    # few variables and short formula
    form_1 = []
    form_1.append("~(a & b & c) & (a ^ b ^ c ^ d)")
    form_1.append("(a | b | c)")
    form_1.append("(a ^ b ^ c)")
    form_1.append("(~(a & b) | (c & ~d))")
    form_1.append("(~(a & b) ^ (~c | ~d))")
    form_1.append("(~(a | b) ^ (c | d) ^ (a & d))")
    form_1.append(" ~( a ^ b ) | ( c ^ d ) ")
    form_1.append("(a & b) | (~(a & c) & (a | c | d))")
    form_1.append("(~((a | b) & c)) | (~d) ")
    form_1.append("(~(a | c) & b) ^ (~d)")
    form_1.append("( a & ~a )")
    
    str_formula.append(form_1)
    
    # few variables and long formulas
    form_2 = []
    form_2.append("( ( ( a & b ) | ( ( ~a & c & b ) & ( ~c | a | b ) & d & a ) ) | ( ( ( d ^ c ^ b ) ^ ( a ^ ~c ^ b ^ ( ( a & b ) | ( ( c & a & b ) & ( d | a | ~a ) & c & a ) ) ) ^ b ) & a & ( c ^ ~c ^ a ^ ( d | ~d | b ) ) & a ) | ( b | ( a ^ d ^ c ) ) )")
    form_2.append("( a | ( ( b & c & d & ~a ) & c & ( a | ( b ^ ~a ^ ~c ) | d ) & b ) | ( ( b | a | ( a & b & c & d ) | ~c ) & ( ( a ^ ~b ^ c ^ ( c & a & b & ~d ) ) ^ a ^ b ^ ( c ^ d ^ ~d ) ) & ( a & b & c & d ) & ( ( a & b & c & d ) & a & ( b | ( ~a ^ ~b ^ ~c ) | a ) & d ) ) )")
    form_2.append("( ( a & ~b ) & ( ( b | c ) | ( c & d & ~a ) | a | b ) & ( c | ( d | ( a & b & c ) | ~c ) & c ) )")
    form_2.append("( ( a & b ) & ( ( c | d ) | ( a & ~b & c ) | d | ~a ) & ( d & ( a & ( b | c | ~d ) & c ) & d ) )")
    form_2.append("( ( ( a & b & ( ( c | a | b ) & c ) ) | d ) & ( d | c | b | ( a ^ b ^ ( a ^ b ^ c ) ^ d ) | d ) & ( ( ( a | ( b & (  ~ a ) & (  ~ c ) & d ) | a ) & b ) ^ c ) & ( b & ( c ^ ( a | b | d ) ^ a ^ (  ~ a ) ^ b ) & c & ( ( d | a | c ) ^ a ^ ( d ^ a ^ ( b | c | d | ( (  ~ b ) | (  ~ a ) | b ) ) ^ c ^ b ) ^ (  ~ a ) ^ c ) ) )")
    form_2.append("((a & b) | (c | d) | (c & a) | (~b & ~c) | (a & c & d) | ~d)")
    form_2.append("((a ^ b) | (c & b | (~(b & c)) | (~b ^ ~c)) | a | (c & d) | ~d)")
    form_2.append("((a ^ b) & (c | b | ~a | (~b ^ ~c)) & a & (c | d) & d & (c & b & (~(b & c)) | (~b ^ ~c)) & a & (c & d) & ~d)")

    str_formula.append(form_2)

    # many variables and short formula
    form_3 = []
    form_3.append("( ( node00 & node01 & node02 ) | ( ( node100 & node101 ) | ( node110 & node111 & (  ~ node112 ) ) | ( node120 ^ node121 ^ node122 ^ node100 ) ) | ( node20 ^ node21 ^ ( node100 & node101 ) ) )")
    form_3.append("( ( node00 ^ ( (  ~ node010 ) ^ node011 ^ node00 ) ^ node02 ) & ( node10 & node11 & node12 ) )")
    form_3.append("( node0 | ( ( node100 ^ node101 ^ (  ~ node102 ) ) & node11 & node12 ) | ( node20 ^ ( node210 ^ node211 ^ node212 ) ^ ( node220 ^ node221 ^ node210 ) ) )")
    form_3.append("( node0 ^ ( ( node100 & node101 ) | ( node110 ^ node111 ^ node112 ^ node100 ) ) )")
    form_3.append("( ( ( (  ~ node000 ) & node001 & node002 ) & ( node010 ^ node011 ^ node012 ) ) | ( ( node100 ^ node101 ^ node002 ) & node11 ) )")
    form_3.append("( (  ~ node0 ) & ( ( (  ~ node100 ) & ( node1010 | node1011 | node1012 ) & node0 ) ^ ( node110 ^ node111 ^ node112 ^ node0 ) ^ node12 ) )")
    form_3.append("( ( node00 | ( ( node0100 & node0101 ) | (  ~ node011 ) | node012 ) ) & ( node10 & node11 & ( (  ~ node120 ) ^ node00 ) ) )")

    str_formula.append(form_3)
    
    # many variables and long formula
    form_4 = []
    form_4.append("( ( ( (  ~ node000 ) & (  ~ node001 ) & ( ( (  ~ node00200 ) | (  ~ node00201 ) | node00202 ) & node0021 ) ) | node01 ) & ( node10 | node11 | node12 | ( node130 ^ node131 ^ ( ( node13200 & node13201 & node000 ) ^ node1321 ^ node1322 ^ node1323 ) ^ node001 ) | node0021 ) & ( ( ( node2000 | ( node20010 & (  ~ node20011 ) & (  ~ node20012 ) & node20013 ) | node2002 ) & node201 ) ^ node21 ) & ( node30 & ( node310 ^ ( node3110 | node3111 | node3112 ) ^ node312 ^ (  ~ node313 ) ^ node001 ) & node32 & ( ( node3300 | node3301 | node3302 ) ^ node331 ^ ( node3320 ^ node3321 ^ ( node33220 | node33221 | node33222 | ( (  ~ node00200 ) | (  ~ node00201 ) | node00202 ) ) ^ node3323 ^ node3302 ) ^ (  ~ node333 ) ^ node3111 ) ) )")
    form_4.append("( ( node00 & node01 & ( ( node0200 & node0201 & node0202 ) | node021 | node022 | node01 ) & node03 ) | node1 | ( node20 & ( node210 & node211 & (  ~ node212 ) & ( node2130 | node2131 | node2132 | node2133 ) & node1 ) & ( ( node2200 | node2201 | node2202 | node2203 ) ^ ( node2210 | node2211 | node2212 | node2213 ) ) & ( node230 & node231 & ( node2320 & node2321 & node2322 & node2323 ) & ( node2210 | node2211 | node2212 | node2213 ) ) ) )")
    form_4.append("( node0 & ( node10 & node11 & node0 ) & node2 & ( ( node300 ^ node301 ^ node11 ) & ( node310 ^ node311 ) & ( ( ( node32000 & node32001 & node311 ) & ( (  ~ node32010 ) & node32011 & node10 ) & node3202 & node3203 ) ^ ( node3210 | node3211 ) ^ node322 ^ ( node3230 & node3231 & node3232 ) ^ node310 ) ) )")
    form_4.append("( ( ( node000 & node001 & node002 ) | ( node010 & ( node0110 | node0111 | node0112 ) & node012 & node000 ) ) & ( ( node100 ^ ( node1010 & node1011 & ( node010 & ( node0110 | node0111 | node0112 ) & node012 & node000 ) ) ^ node102 ) | node11 ) & ( node20 & ( node210 | node211 | ( node2120 & node2121 & node102 ) ) & node22 & node0111 ) )")
    form_4.append("( ( ( node000 & ( ( node00100 ^ node00101 ^ node00102 ^ node000 ) ^ node0011 ^ node0012 ^ node0013 ) & node002 & node003 ) | node01 | ( ( node0200 | node0201 | node003 ) | node021 | ( node0220 | node0221 | ( node00100 ^ node00101 ^ node00102 ^ node000 ) ) | node0011 ) | ( node030 & node031 ) ) | node1 | ( ( ( node2000 & node2001 & node2002 ) | ( node2010 ^ node2011 ^ node2012 ) | node202 | node203 | node1 ) ^ node21 ^ node22 ^ ( ( node2300 ^ ( node23010 | node23011 ) ^ node22 ) & node231 & node232 & ( node2330 | ( node23310 & node23311 ) | node2332 | node2333 | ( node23010 | node23011 ) ) & node21 ) ) )")
    form_4.append("( ( node00 | ( node010 ^ node011 ^ node012 ^ node013 ^ node00 ) | node02 ) | ( node10 & ( ( node1100 & node1101 ) | node111 | node112 | node113 ) & node12 & ( ( node1300 & ( node13010 | node13011 ) & node1302 & node12 ) | ( ( node13100 ^ node13101 ^ node13102 ^ node13103 ^ node1300 ) | node1311 | node1312 | node1313 | node011 ) | ( node1320 & node1321 & node1322 & node1323 ) | ( ( node13300 | node13301 | node13302 | ( node13010 | node13011 ) ) | node1331 | node1332 | ( node13330 ^ node13331 ^ node13332 ^ node13333 ) | node1313 ) ) ) )")
    form_4.append("( ( ( ( node0000 ^ node0001 ) & node001 & node002 & ( node0030 | node0033 ) ) & node01 ) | ( ( ( ( node10000 & node10001 & node0030 ) & node1001 & ( node0000 & node0001 ) ) ^ ( node1010 & node001 ) ^ ( node1030 & node1031 ) ^ node0031 ) & node11 & ( node120 & node121 & node10000 ) & ( ( node1300 ^ node0000 ) & node131 & ( node1320 & ( node13210 ^ node13211 ) & node1322 & node11 ) & node133 ) ) | ( ( ( node2001 ^ ( node10000 & node0030 ) ) & ( node2010 ^ node13213 ) & node120 ) & ( ( node2100 & node2101 ) | node211 ) & ( node220 & ( node2210 ^ ( ( node1300 ^ node0000 ) & ( node1320 & node1322 & node11 ) & node133 ) ) & node222 ) ) )")

    str_formula.append(form_4)

    glob = {}
    exec('from sympy.core import Symbol', glob) # ok for I, E, S, N, C, O, or Q

    basic = [0, 0, 0, 0]
    solve_basic = [0, 0, 0, 0]
    tt = [0, 0, 0, 0]
    solve_tt = [0, 0, 0, 0]
    tse = [0, 0, 0, 0]
    solve_tse = [0, 0, 0, 0]

    timer = 300 #150
    etimer = [0, 0, 0]

    for i in [0, 1, 2, 3]:
        for s in str_formula[i]:
            formula = parse_expr(s, global_dict=glob)
            print(formula)

            try:
                with timeout(seconds=timer):
                    print("1")
                    start = time.time()
                    cnf_formula = to_cnf(formula)
                    end = time.time()
                    #print(cnf_formula)
                    etimer[0] = end - start
                    basic[i] += etimer[0]
            except:
                print("encoding timeout 1")
                basic[i] += timer
                cnf_formula = False

            try:
                with timeout(seconds=timer):
                    print("2")
                    start = time.time()
                    list_and_cnf, set_var, index_expr = tseitin(formula)
                    end = time.time()
                    #print(list_and_cnf)
                    etimer[2] = end - start
                    tse[i] += etimer[2]
            except:
                print("encoding timeout 2")
                tse[i] += timer
                list_and_cnf = False

            list_var = list(set_var) + [str(l) for l in index_expr]

            if cnf_formula != True and cnf_formula != False:
                try:
                    with timeout(seconds=round(timer-etimer[0])):
                        print("solve 1")
                        start = time.time()
                        sat_solver(cnf_formula, list(set_var), [], 10000, False)
                        end = time.time()
                        solve_basic[i] += end - start
                except:
                    print("solving timeout")
                    solve_basic[i] += timer-etimer[0]

            try:
                with timeout(seconds=round(timer-etimer[1])):
                    print("solve 2")
                    start = time.time()
                    compute_truthtable(formula, True)
                    end = time.time()
                    solve_tt[i] += end - start
            except Exception as e:
                print("solving timeout")
                solve_tt[i] += timer-etimer[1]
            

            if list_and_cnf != True and list_and_cnf != False:
                try:
                    with timeout(seconds=round(timer-etimer[2])):
                        print("solve 3")
                        start = time.time()
                        sat_solver(list_and_cnf, list_var, [], 10000, False)
                        end = time.time()
                        solve_tse[i] += end - start
                except Exception as e:
                    print("solving timeout")
                    solve_tse[i] += timer-etimer[2]


    ind = ['TruthTable', 'Basic', 'Tseitin'] 
    width = 0.75

    fig, axs = plt.subplots(1, 4, figsize=(14,5))

    encoding = []
    solving = []

    for i in [0, 1, 2, 3]:
        print(i)
        cnt = len(str_formula[i])

        print("")
        print("TIME CNF TRUTHTABLE = " + str(tt[i]/cnt))
        print("TIME CNF BASIC = " + str(basic[i]/cnt))
        print("TIME CNF TSEITIN = " + str(tse[i]/cnt))
        print("")
        print("TIME SOLVE TRUTHTABLE = " + str(solve_tt[i]/cnt))
        print("TIME SOLVE BASIC = " + str(solve_basic[i]/cnt))
        print("TIME SOLVE TSEITIN = " + str(solve_tse[i]/cnt))

        encoding.append([tt[i]/cnt, basic[i]/cnt, tse[i]/cnt])
        solving.append([solve_tt[i]/cnt, solve_basic[i]/cnt, solve_tse[i]/cnt])

    fig.suptitle('Encoding and solving comparison')

    p1 = axs[0].bar(ind, encoding[0], width, color=['blue'], edgecolor='black')
    p1_both = axs[0].bar(ind, solving[0], width, bottom = encoding[0], color=['orange'], edgecolor='black')
    axs[0].set_title('Few vars and few operators', size='medium')

    p2 = axs[1].bar(ind, encoding[1], width, color=['blue'], edgecolor='black')
    p2_both = axs[1].bar(ind, solving[1], width, bottom = encoding[1], color=['orange'], edgecolor='black')
    axs[1].set_title('Few vars and many operators', size='medium')

    p3 = axs[2].bar(ind, encoding[2], width, color=['blue'], edgecolor='black')
    p3_both = axs[2].bar(ind, solving[2], width, bottom = encoding[2], color=['orange'], edgecolor='black')
    axs[2].set_title('Many vars and few operators', size='medium')

    p4 = axs[3].bar(ind, encoding[3], width, color=['blue'], edgecolor='black', label='encoding')
    p4_both = axs[3].bar(ind, solving[3], width, bottom = encoding[3], color=['orange'], edgecolor='black', label='solving')
    axs[3].set_title('Many vars and many operators', size='medium')

    handles, labels = axs[3].get_legend_handles_labels()
    fig.legend(handles, labels, loc='center right')

    fig.supxlabel('Method used')
    fig.supylabel('Time (s)')
    
    plt.show()

if __name__ == "__main__":
    benchmark()
