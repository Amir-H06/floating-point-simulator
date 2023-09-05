from ..arithmetic import ieee754
from itertools import product
import math
import logging
import sys
import time
from rich import print

# File imports

logging.basicConfig(filename=r'errors.log', level=logging.DEBUG)

"""Introducing some sort of documentation - it's 10pm on a sunday night so apologies for any errors"""

# self-explanatory

same, different, total, totals, checked = [[0] * 9 for _ in range(5)], [[0] * 9 for _ in range(5)], [[0] * 9 for _ in range(5)], [0] * 4, 0

tracker = [[0] * 15 for _ in range(5)]

evaly, evaln = [[0] * 9 for _ in range(5)], [[0] * 9 for _ in range(5)]


# bill's magic that I can't explain at this current moment
def normalize_sig(c, nbits):
    if c.bit_length() < nbits:
        return c << (nbits - c.bit_length())
    else:
        return c


def get_bit_range(x, start, end):
    masklen = end - start
    mask = (1 << masklen) - 1
    return (x >> start) & mask


# bill's magic which I can explain


def splitsignif(a, b, c):
    # p, k, h are variables / constraints defined in the original proof (Emi)
    # p represents the signifand length of floating point c
    p = c.ctx.p
    k = c.e - b.e
    h = c.e - a.e
    assert p == a.ctx.p == b.ctx.p  # checks whether all of the fp significand's length is the same

    # c1 is basically the same as floating point c, but we added 0s to the left to make the bit_length the same as p
    csig = normalize_sig(c.c, p)
    # c0 returns the last bit of the signifand of fp c
    c0 = get_bit_range(csig, 0, 1)

    # refer to the diagram shown in the original proof
    bsig = normalize_sig(b.c, p)
    b2 = get_bit_range(bsig, 0, k)
    b1 = get_bit_range(bsig, k, p)
    bk = get_bit_range(bsig, k, k + 1)

    asig = normalize_sig(a.c, p)
    a3 = get_bit_range(asig, 0, h - k)
    a2 = get_bit_range(asig, h - k, h)
    a1 = get_bit_range(asig, h, p)
    ah = get_bit_range(asig, h, h + 1)
    a32 = get_bit_range(asig, 0, h)

    # stores each of the split bitvectors in an array (there's obviously a nicer way to store this)
    fpa = [asig, a1, a2, a3, ah, a32]
    fpb = [bsig, b1, b2, bk]
    fpc = [csig, c0]

    return fpa, fpb, fpc


def checkcarry(x, y, n, generated=False):
    # x and y must be greater than 0, and the bit length of the two numbers should be less than the length of the significand (depends)#
    # returns whether the bit length of x+y is greater than the length of the significand (generate has occurred)
    if x > 0 and y > 0:
        if generated:
            if (x < 2**n and (y > 2**n or y == 2**n)):
                return (x + y) >= 2**n
        else:
            if (x < 2**n and y < 2**n):
                return (x + y) >= 2**n


def checklessthan(x, y):
    return x < y


def realpos(fp):
    # checks whether the fp is positive and whether it contains any sub-normals
    return fp.isnormal() and not fp.negative


def realneg(fp):
    return fp.isnormal() and fp.negative


def check(fp, ctx, case, cases):
    a, b, c = fp
    total[case][cases] += 1
    if a.add(b, ctx).add(c, ctx) != a.add(b.add(c, ctx), ctx):
        different[case][cases] += 1
        return 1
    else:
        same[case][cases] += 1
        return 0


def eval(checks, condition, case, cases):
    # checks whether the condition from the paper matches with the condition
    if checks == condition:
        evaly[case][cases] += 1
    else:
        evaln[case][cases] += 1

    return checks == condition


def assoc(fp, ctx, case, cases):
    if a.add(b, ctx).add(c, ctx) != a.add(b.add(c, ctx), ctx):
        different[case][cases] += 1
    else:
        same[case][cases] += 1


def render_element(e):
    return str(e)


def subtractcarry(x, y, n, h):
    return (((x) << h) - y) >= 2**(n + h)


def case1(fp, f8_rtz, p, k, h):
    totals[1] += 1
    if checkcarry(fpb[1], fpc[0], p):
        if checkcarry(fpa[1], fpb[1] + fpc[0], p, True):
            if checkcarry(fpa[2], fpb[2], k):
                eval(check(fp, f8_rtz, 1, 8), fpa[4] or (fpb[3] ^ fpc[1]), 1, 8)   # Case 1.8
            else:
                eval(check(fp, f8_rtz, 1, 7), fpa[4] and (fpb[3] ^ fpc[1]), 1, 7)  # Case 1.7
        else:
            if checkcarry(fpa[2], fpb[2], k):
                eval(check(fp, f8_rtz, 1, 6), 0, 1, 6)  # Case 1.6
            else:
                eval(check(fp, f8_rtz, 1, 5), 0, 1, 5)  # Case 1.5
    else:
        if checkcarry(fpa[1], fpb[1] + fpc[0], p):
            if checkcarry(fpa[2], fpb[2], k):
                eval(check(fp, f8_rtz, 1, 4), fpa[4] ^ fpb[3] ^ fpc[1], 1, 4)  # Case 1.4
            else:
                eval(check(fp, f8_rtz, 1, 3), 0, 1, 3)  # Case 1.3
        else:
            if checkcarry(fpa[2], fpb[2], k):
                eval(check(fp, f8_rtz, 1, 2), 1, 1, 2)  # Case 1.2
            else:
                eval(check(fp, f8_rtz, 1, 1), 0, 1, 1)  # Case 1.1


def case2(fp, f8_rtz, p, k, h, i, j, l):
    totals[2] += 1
    if checkcarry(fpb[1], fpc[0], p):
        if subtractcarry(fpb[1] + fpc[0], fpa[0], p, h):
            if (fpa[2] > fpb[2] or (fpb[2] == fpa[2] and fpa[3] > 0)):
                # eval(check(fp, f8_rtz, 2, 8), ((not fpa[4])) or ((fpb[3] ^ fpc[1])), 2, 8))
                eval(check(fp, f8_rtz, 2, 8), (fpb[3] ^ fpc[1]) and (fpa[4] ^ fpb[3] ^ fpc[1]), 2, 8)
            else:
                eval(check(fp, f8_rtz, 2, 7), (((fpa[5] == 0) and fpa[4] and (fpb[3] ^ fpc[1])) or ((fpa[5] > 0) and (fpa[4] or (fpb[3] ^ fpc[1])))), 2, 7)
                ctx = f8_rtz # Case 2.8
                print(a.add(b, ctx).add(c, ctx) != a.add(b.add(c, ctx), ctx), fpa[4], fpb[3], fpc[1])
                #print(i, j, l, check(fp, f8_rtz, 2, 8), (fpa[4] ^ fpb[3] ^ fpc[1]) & ((not fpa[4])) or ((fpb[3] ^ fpc[1])), fpa[4])
                logging.debug('%s %s %s', i, j, l)  # Case 2.7
        else:
            if (fpa[2] > fpb[2] or (fpb[2] == fpa[2] and fpa[3] > 0)):
                eval(check(fp, f8_rtz, 2, 6), fpb[3] ^ fpc[1], 2, 6)  # Case 2.6
            else:
                eval(check(fp, f8_rtz, 2, 5), fpa[5] > 0 or fpb[3] ^ fpc[1], 2, 5)  # Case 2.5
    else:
        if subtractcarry(fpb[1] + fpc[0], fpa[0], p, h):
            if (fpa[2] > fpb[2] or (fpb[2] == fpa[2] and fpa[3] > 0)):
                eval(check(fp, f8_rtz, 2, 4), 1, 2, 4)  # Case 2.4
            else:
                eval(check(fp, f8_rtz, 2, 3), 1, 2, 3)  # Case 2.3
        else:
            if (fpa[2] > fpb[2] or (fpb[2] == fpa[2] and fpa[3] > 0)):
                eval(check(fp, f8_rtz, 2, 2), 0, 2, 2)
            else:
                eval(check(fp, f8_rtz, 2, 1), fpa[5] > 0, 2, 1)


def percentage(x, y):
    if y == 0:
        return '0%'
    else:
        return f'{round((x/y), 2) * 100}%'


nbits = 7
es = 3
f8_rtz = ieee754.ieee_ctx(es=es, nbits=nbits, rm=ieee754.RM.ROUND_TO_ZERO)

start = time.time()

"""
Quick explanation on what my dodgy code does for anyone who needs to work on the problem

TLDR: The program loops through 



"""


for l in range(2**nbits):
    for j in range(2**nbits):
        for i in range(2**nbits):
            a = ieee754.bits_to_digital(i, f8_rtz) 
            b = ieee754.bits_to_digital(j, f8_rtz)
            c = ieee754.bits_to_digital(l, f8_rtz)
            p = c.ctx.p
            k = c.e - b.e  # Saadhana's K var 
            h = c.e - a.e  # Saadhana's L var (A1)
            q = p - k  # Saadhana's Q var (B1)
            fp = (a, b, c)

            if (c.e > b.e > a.e) and (c.e - a.e < p - 1):   # Constraints implemented
                fpa, fpb, fpc = splitsignif(a, b, c)                             
                if realpos(a.add(b, f8_rtz).add(c, f8_rtz)) and realpos(a.add(b.add(c, f8_rtz), f8_rtz)):   # Checks for whether (A+B)+C and A + (B+C) doesnt lead to inf result
                    if realpos(c):
                        if realpos(b) & realpos(a):
                            case1(fp, f8_rtz, p, k, h)
                        elif realpos(b) & realneg(a):
                            case2(fp, f8_rtz, p, k, h, i, j, l)

end = time.time()

for i in range(1, 3):
    for j in range(1, len(same[i])):
        print(f'''[bold blue]Case {i}.{j}[/bold blue]: [green]Associative:[/green] [green]{same[i][j]}[/green], [red]Non-Associative:[/red] [red]{different[i][j]}[/red], [gray]Total[/gray]: [gray]{same[i][j] + different[i][j]}[/gray], [blue]Cond Evalulated:[/blue] [green]T:[green] [green]{evaly[i][j]}[/green], [red]F:[/red] [red]{evaln[i][j]}[/red]''')


print(f'Probability of non-associativity is {(sum(different[1])+sum(different[2]))/(sum(totals))}')

print(f'Total: {sum(totals)}, Time: {round(end-start,2)}s')

exit()
