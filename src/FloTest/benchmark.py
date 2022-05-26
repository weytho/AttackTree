##
# @file
# Methods use to compute the Tseitin transformation
# used to convert a boolan formula to its CNF-form
#
from matplotlib import pyplot as plt
import numpy as np
from sympy import *
import time
from itertools import product
import math

try:
    # From folder
    from SATsolver import sat_solver
    from tseitin import tseitin
except ImportError:
    # From package
    from FloTest.SATsolver import sat_solver
    from FloTest.tseitin import tseitin

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
    #form_4.append("")
    #form_4.append("")
    #form_4.append("")
    #form_4.append("")

    str_formula.append(form_4)

    glob = {}
    exec('from sympy.core import Symbol', glob) # ok for I, E, S, N, C, O, or Q

    basic = [0, 0, 0, 0]
    solve_basic = [0, 0, 0, 0]
    qmc = [0, 0, 0, 0]
    solve_qmc = [0, 0, 0, 0]
    tse = [0, 0, 0, 0]
    solve_tse = [0, 0, 0, 0]

    for i in [0, 1, 2, 3]:
        for s in str_formula[i]:
            formula = parse_expr(s, global_dict=glob)
            print(formula)
            
            start = time.time()
            cnf_formula = to_cnf(formula)
            print("1")
            #print(cnf_formula)
            end = time.time()
            basic[i] += end - start

            start = time.time()
            cnf_formula_qmc = to_cnf(formula, True, True)
            print("2")
            #print(cnf_formula_qmc)
            end = time.time()
            qmc[i] += end - start

            start = time.time()
            list_and_cnf, set_var, index_expr = tseitin(formula)
            print("3")
            #print(list_and_cnf)
            end = time.time()
            tse[i] = end - start

            list_var = list(set_var) + [str(l) for l in index_expr]

            if cnf_formula != True and cnf_formula != False:
                start = time.time()
                sat_solver(cnf_formula, list(set_var), [], -1, False)
                end = time.time()
                solve_basic[i] += end - start

            if cnf_formula_qmc != True and cnf_formula_qmc != False:
                start = time.time()
                sat_solver(cnf_formula_qmc, list(set_var), [], -1, False)
                end = time.time()
                solve_qmc[i] += end - start

            if list_and_cnf != True and list_and_cnf != False:
                start = time.time()
                sat_solver(list_and_cnf, list_var, [], -1, False)
                end = time.time()
                solve_tse[i] += end - start

            #break # to remove
        #break

    ind = np.arange(3)  
    width = 0.4

    fig, ((ax1, ax2, ax3, ax4), (ax5, ax6, ax7, ax8)) = plt.subplots(2, 4)
    axs = [ax1, ax2, ax3, ax4, ax5, ax6, ax7, ax8]

    encoding = []
    solving = []

    for i in [0, 1, 2, 3]:
        print(i)
        print("")

        print("TIME CNF BASIC = " + str(basic[i]))
        print("TIME CNF QMC = " + str(qmc[i]))
        print("TIME CNF TSEITIN = " + str(tse[i]))

        print("")

        print("TIME SOLVE BASIC = " + str(solve_basic[i]))
        print("TIME SOLVE QMC = " + str(solve_qmc[i]))
        print("TIME SOLVE TSEITIN = " + str(solve_tse[i]))

        encoding.append([basic[i], qmc[i], tse[i]])
        solving.append([solve_basic[i], solve_qmc[i], solve_tse[i]])


    #plt.yscale('log')

    p1 = axs[0].bar(ind - width, encoding[0], width, color=['blue'], edgecolor='black')
    p1_both = axs[0].bar(ind - width, solving[0], width, bottom = encoding[0], color=['orange'], edgecolor='black')

    p2 = axs[1].bar(ind, encoding[1], width, color=['blue'], edgecolor='black')
    p2_both = axs[1].bar(ind, solving[1], width, bottom = encoding[1], color=['orange'], edgecolor='black')

    p3 = axs[2].bar(ind + width, encoding[2], width, color=['blue'], edgecolor='black')
    p3_both = axs[2].bar(ind + width, solving[2], width, bottom = encoding[2], color=['orange'], edgecolor='black')

    p4 = axs[3].bar(ind + width, encoding[3], width, color=['blue'], edgecolor='black')
    p4_both = axs[3].bar(ind + width, solving[3], width, bottom = encoding[2], color=['orange'], edgecolor='black')

    axs[4].set_yscale('log')
    axs[5].set_yscale('log')
    axs[6].set_yscale('log')
    axs[7].set_yscale('log')

    print([sum(x) for x in zip(encoding[0], solving[0])])

    p1_tot = axs[4].bar(ind, [sum(x) for x in zip(encoding[0], solving[0])], width, color=['blue'], edgecolor='black')

    p2_tot = axs[5].bar(ind, [sum(x) for x in zip(encoding[1], solving[1])], width, color=['blue'], edgecolor='black')

    p3_tot = axs[6].bar(ind, [sum(x) for x in zip(encoding[2], solving[2])], width, color=['blue'], edgecolor='black')

    p4_tot = axs[7].bar(ind, [sum(x) for x in zip(encoding[3], solving[3])], width, color=['blue'], edgecolor='black')

    #plt.autoscale(tight=True)

    #plt.ylabel('Time')
    #plt.title('Encoding and solving Test')
    #plt.xticks(ind, ('T1', 'T2', 'T3', 'T4'))



    #plt.yticks(np.arange(0, 81, 10))
    #plt.legend((p1_basic[0], p2_basic[0], p1_qmc[0], p2_qmc[0], p1_tse[0], p2_tse[0]), ('CNF converter', 'SAT solver'))
    
    plt.show()

if __name__ == "__main__":
    benchmark()