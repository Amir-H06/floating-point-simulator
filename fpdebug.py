from ..arithmetic import ieee754
from itertools import product
import math
import sys


old_stdout = sys.stdout

log_file = open("checked.log","w")

sys.stdout = log_file

def normalize_sig(c, nbits):
  if c.bit_length() < nbits:
    return c << (nbits - c.bit_length())
  else:
    return c

def get_bit_range(x, start, end):
  masklen = end - start
  mask = (1 << masklen) - 1
  return (x >> start) & mask

def splitsignif(a,b,c):
  p = c.ctx.p
  k = c.e - b.e
  h = c.e - a.e
  assert p == a.ctx.p == b.ctx.p
  c1 = normalize_sig(c.c, p)
  c0 = get_bit_range(c1, 0, 1)

  b0 = normalize_sig(b.c, p)
  b2 = get_bit_range(b0, 0, k)
  b1 = get_bit_range(b0, k, p)
  bk = get_bit_range(b0, k, k+1)

  a0 = normalize_sig(a.c, p)
  a3 = get_bit_range(a0, 0, h-k)
  a2 = get_bit_range(a0, h-k, h)
  a1 = get_bit_range(a0, h, p)
  ak = get_bit_range(a0, h, h+1)
  a32 = get_bit_range(a0, 0, h)

  #stores each of the split bitvectors in an array (there's obviously a nicer way to store this)
  fpa = [a0,a1,a2,a3,ak,a32]
  fpb = [b0,b1,b2, bk]
  fpc = [c1, c0]
  """  print(bin(a0), bin(a1), bin(a2), bin(a3))
  print(bin(b0), bin(b1), bin(b2))
  print(bin(c1))"""
  return fpa, fpb, fpc

same, different, total = [0]*50, [0]*50, [0]*50
evaly, evaln = [0]*50, [0]*50

test =[[0] * 9 for _ in range(5)]

def realpos(fp):
  return fp.isnormal() and not fp.negative

def realneg(fp):
  return fp.isnormal() and fp.negative

def check(a,b,c, case, ctx): 
  # simple function that checks for non-associativity and saves it as an array of the case number 💀
  total[case] += 1
  if a.add(b, ctx).add(c, ctx) != a.add(b.add(c, ctx), ctx):
      different[case] += 1
      return 1
  else:
      same[case] += 1
      return 0

def eval(checks, condition, case):
  #checks whether the condition from the paper matches with the condition
  if checks == condition:
    evaly[case] += 1
  else:
    evaln[case] += 1
  
  return checks == condition


def render_element(e):
    return str(e)

def checkcarry(x,y,n, generated=False):
  """  assert (x > 0 and y > 0)
    assert x.bit_length() <= n and y.bit_length() <= n"""
  # x and y must be greater than 0, and the bit length of the two numbers should be less than the length of the significand (depends)#
  # returns whether the bit length of x+y is greater than the length of the significand (generate has occurred)
  if x > 0 and y > 0: 
    if generated == True:
      if (x < 2**n and (y > 2**n or y == 2**n)):
        return (x+y) >= 2**n
    else:
      if (x < 2**n and y < 2**n):
        return (x+y) >= 2**n

def checklessthan(x,y):
  return x < y

def renderfp(a):
  return f'{render_element(a)!s:<20}{ieee754.show_bitpattern(a)}'


"""def checker(a,b,c, ctx):
  fpa, fpb, fpc = splitsignif(a,b,c)
  
  print('DEBUG: ')
  print('Bit length of C, ', c.ctx.p)
  print('Bit length of k (exp(c) - exp(b)), ', c.e - a.e)

  print('a:', bin(fpa[0]), bin(fpa[1]), bin(fpa[2]), bin(fpa[3]))
  print(f'{render_element(a)!s:<10}{ieee754.show_bitpattern(a)}')
  print('b:', bin(fpb[0]), bin(fpb[1]), bin(fpb[2]))
  print(f'{render_element(b)!s:<10}{ieee754.show_bitpattern(b)}')
  print('c:', bin(fpc[0]))
  print(f'{render_element(c)!s:<10}{ieee754.show_bitpattern(c)}')

  print('Case 1 Checks:')
  print('Does B1 + C generate?:', (fpb[1]+fpc[0]) >= 2**c.ctx.p,', bit value:', (fpb[1]+fpc[0]), 2**c.ctx.p)
  print('Does A1 + B1 + C generate?:', ((fpa[1])+(fpb[1]+fpc[0])) >= 2**c.ctx.p,', bit value:', ((fpa[1])+(fpb[1]+fpc[0])), 2**c.ctx.p) #c.e - b.e
  print('Does A2 + B2 generate?:', (fpa[2]+fpb[2]) >= 2**(c.e - b.e),', bit value:', (fpa[2]+fpb[2]), 2**(c.e - b.e), '\n')

  print('Case 2 Checks: ')
  print('Does B1 + C generate?:', (fpb[1]+fpc[0]) >= 2**c.ctx.p,', bit value:', (fpb[1]+fpc[0]), 2**c.ctx.p)
  print('Does B1 + C - A1 generate?:', ((fpb[1] - fpa[1]) + fpc[1]) >= 2**c.ctx.p,', bit value:', ((fpb[1] - fpa[1]) + fpc[1]), 2**c.ctx.p)
  print('Is B2 > A2:', fpb[2] > fpa[2])
  print('Is A2+A3 > 0: ', fpa[5] > 0)
  print('Is A2 + A3 = 0: ', fpa[5] == 0, '\n')

  print('Associative?:', check(a,b,c,1, ctx)) #0 = False, 1 = True
  print('LHS: (a+b) + c: ', float(a.add(b, ctx).add(c, ctx)))
  print(f'(a+b) + c {render_element(a.add(b, ctx).add(c, ctx))!s:<20}{ieee754.show_bitpattern(a.add(b, ctx).add(c, ctx))}')
  print(f'a + b: {render_element(a.add(b, ctx))!s:<20}{ieee754.show_bitpattern(a.add(b, ctx))}\n')

  print('RHS: a + (b+c): ', float(a.add(b.add(c, ctx), ctx)))
  print(f'a + (b+c) {render_element(a.add(b.add(c, ctx), ctx))!s:<20}{ieee754.show_bitpattern(a.add(b.add(c, ctx), ctx))}')
  print(f'b + c: {render_element(b.add(c, ctx))!s:<20}{ieee754.show_bitpattern(b.add(c, ctx))}\n')

  print(f'bk ^ c0: {fpb[3] ^ fpc[1]}')
  print(f'Az > 0 || bk ^ c0 {fpa[4] > 0 or fpb[3] ^ fpc[1]}')

  print(f'{eval(check(a,b,c,1, ctx), 0, 1)}')
  print(f'{evaly, evaln}')"""

def checker2file(a,b,c, ctx):
  fpa, fpb, fpc = splitsignif(a,b,c)

  print(f'{i}, {j}, {k}')
  print(f'a: {bin(fpa[0]), bin(fpa[1]), bin(fpa[2]), bin(fpa[3]), bin(fpa[4]), bin(fpa[5])} - {render_element(a)} - {ieee754.show_bitpattern(a)}')
  print(f'b: {bin(fpb[0]), bin(fpb[1]), bin(fpb[2]), bin(fpb[3])} - {render_element(b)} - {ieee754.show_bitpattern(b)}')
  print(f'c: {bin(fpc[0]), bin(fpc[1])} - {render_element(c)} - {ieee754.show_bitpattern(c)}')
  print(f'Case 2 Checks: {(fpb[1]+fpc[0]) >= 2**c.ctx.p}, {((fpb[1] - fpa[1]) + fpc[1]) >= 2**c.ctx.p}, {fpb[2] > fpa[2]} ')
  print(f'{fpa[5] > 0}, {fpa[5] == 0}')
  print(f'Associative?:, {check(a,b,c,1, ctx)}')
  print(f'LHS (a+b): {float(a.add(b, ctx))}, {render_element(a.add(b, ctx))!s:<20}{ieee754.show_bitpattern(a.add(b, ctx))}')
  print(f'LHS: (a+b) + c {float(a.add(b, ctx).add(c, ctx))}, {render_element(a.add(b.add(c, ctx), ctx))!s:<20}{ieee754.show_bitpattern(a.add(b.add(c, ctx), ctx))}')
  print(f'RHS: (b+c): , {float(b.add(c, ctx))}, {render_element(b.add(c, ctx))!s:<20}{ieee754.show_bitpattern(b.add(c, ctx))}')
  print(f'RHS: a + (b + c): {float(a.add(b.add(c, ctx), ctx))}, {render_element(a.add(b.add(c, ctx), ctx))!s:<20}{ieee754.show_bitpattern(a.add(b.add(c, ctx), ctx))}\n')

#a.add(b, ctx).add(c, ctx)

nbits = 8
f8_rtz = ieee754.ieee_ctx(es=3, nbits=nbits, rm=ieee754.RM.ROUND_TO_ZERO)

end = False

with open("errors.log", "r") as file:
    for line in file:
        i, j, k = line.strip().split()

        if i.lower() == 'end' or j.lower() == 'end' or k.lower() == 'end':
            end = True
            break
        else:
            a = ieee754.bits_to_digital(int(i), f8_rtz)
            b = ieee754.bits_to_digital(int(j), f8_rtz)
            c = ieee754.bits_to_digital(int(k), f8_rtz)
            checker2file(a, b, c, f8_rtz)


sys.stdout = old_stdout
log_file.close()

fpa, fpb, fpc = splitsignif(a,b,c)
p = c.ctx.p
k = c.e - b.e
h = c.e - a.e

#27 49 68

        
exit()