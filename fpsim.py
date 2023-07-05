from ..arithmetic import ieee754
from itertools import product
import math
import logging
import sys
import time

logging.basicConfig(filename=r'error.log',level=logging.DEBUG)




"""Introducing some sort of documentation - it's 10pm on a sunday night so apologies for any errors"""

#self-explanatory
same, different, total, totals, checked = [[0] * 9 for _ in range(5)], [[0] * 9 for _ in range(5)], [[0] * 9 for _ in range(5)], [0]*4, 0
evaly, evaln = [[0] * 9 for _ in range(5)], [[0] * 9 for _ in range(5)]
#[[0]*8]*4, [[0]*8]*4,
#bill's magic that I can't explain at this current moment
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
def splitsignif(a,b,c):
  # p, k, h are variables / constraints defined in the original proof (Emi), 
  # p represents the signifand length of floating point c
  p = c.ctx.p
  k = c.e - b.e
  h = c.e - a.e
  assert p == a.ctx.p == b.ctx.p #checks whether all of the fp significand's length is the same

  #c1 is basically the same as floating point c, but we added 0s to the left to make the bit_length the same as p
  csig = normalize_sig(c.c, p)
  #c0 returns the last bit of the signifand of fp c
  c0 = get_bit_range(csig, 0, 1)

  #refer to the diagram shown in the original proof
  bsig = normalize_sig(b.c, p)
  b2 = get_bit_range(bsig, 0, k)
  b1 = get_bit_range(bsig, k, p)
  bk = get_bit_range(bsig, k, k+1)


  asig = normalize_sig(a.c, p)
  a3 = get_bit_range(asig, 0, h-k)
  a2 = get_bit_range(asig, h-k, h)
  a1 = get_bit_range(asig, h, p)
  ak = get_bit_range(asig, h, h+1)
  a32 = get_bit_range(asig, 0, h)

  #stores each of the split bitvectors in an array (there's obviously a nicer way to store this)
  fpa = [asig,a1,a2,a3,ak,a32]
  fpb = [bsig,b1,b2, bk]
  fpc = [csig, c0]

  return fpa, fpb, fpc

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

def checkshrink(x,y,n, generated=False):
  """  assert (x > 0 and y > 0)
    assert x.bit_length() <= n and y.bit_length() <= n"""
  # x and y must be greater than 0, and the bit length of the two numbers should be less than the length of the significand (depends)#
  # returns whether the bit length of x+y is greater than the length of the significand (generate has occurred)
  if x > 0 and y > 0: 
      if (x < 2**n and y < 2**n):
        return (x+y) <= 2**n

def checklessthan(x,y):
  return x < y

def realpos(fp):
    # checks whether the fp is positive and whether it contains any sub-normals
    return fp.isnormal() and not fp.negative

def realneg(fp):
    return fp.isnormal() and fp.negative

def check(a,b,c, ctx, case, cases): 
  # simple function that checks for non-associativity and saves it as an array of the case number 💀
  total[case][cases] += 1
  if a.add(b, ctx).add(c, ctx) != a.add(b.add(c, ctx), ctx):
      different[case][cases] += 1
      return 1
  else:
      same[case][cases] += 1
      return 0

def eval(checks, condition, case, cases):
  #checks whether the condition from the paper matches with the condition
  if checks == condition:
    evaly[case][cases] += 1
  else:
    evaln[case][cases] += 1
  
  return checks == condition

def assoc(a,b,c,ctx):
  if a.add(b, ctx).add(c, ctx) != a.add(b.add(c, ctx), ctx):
    return 1
  else:
    return 0


def render_element(e):
    return str(e)

def case1(a,b,c, f8_rtz, p, k, h):
  totals[1] += 1
  if checkcarry(fpb[1], fpc[0], p): #generate
    if checkcarry(fpa[1], fpb[1]+fpc[0], p, True): #generate
      if checkcarry(fpa[2], fpb[2], k): #generate
        eval(check(a,b,c,f8_rtz,1,8), fpa[4] or (fpb[3] ^ fpc[1]), 1, 8)   #Case 1.8
      else: #not generate
        eval(check(a,b,c,f8_rtz,1,7), fpa[4] and (fpb[3] ^ fpc[1]), 1, 7)
    else:
      if checkcarry(fpa[2], fpb[2], k): 
        eval(check(a,b,c,f8_rtz,1,6), 0, 1, 6) #Case 1.6
      else: #not generate
        eval(check(a,b,c,f8_rtz,1,5), 0, 1, 5) #Case 1.5
  else: 
    if checkcarry(fpa[1], fpb[1]+fpc[0], p):
      if checkcarry(fpa[2], fpb[2], k):
        eval(check(a,b,c,f8_rtz,1,4), fpa[4] ^ fpb[3] ^ fpc[1], 1, 4) #Case 1.4
      else:
        eval(check(a,b,c,f8_rtz,1,3), 0, 1, 3) #Case 1.3
    else:
      if checkcarry(fpa[2], fpb[2], k):
        eval(check(a,b,c,f8_rtz,1,2), 1, 1, 2) #Case 1.2
      else:
        eval(check(a,b,c,f8_rtz,1,1), 0, 1, 1) #Case 1.1
    
def case2(a,b,c, f8_rtz, p, k, h, i, j, l):
  global checks

  totals[2] += 1
  if checkcarry(fpb[1], fpc[0], p): #generate
    if checkcarry(fpb[1] - fpa[1], fpc[0], p): #generate
      if (fpa[2] > fpb[2] or (fpb[2] == fpa[2] and fpa[3] > 0)): #case 2.8
        eval(check(a,b,c,f8_rtz,2,8), (not fpa[4]) or (fpb[3] ^ fpc[1]), 2, 8)
      else:
        if not eval(check(a,b,c,f8_rtz,2,7), (((fpa[5] == 0) and fpa[4] and (fpb[3] ^ fpc[1])) or (fpa[5] > 0 and (fpa[4] or (fpb[3] ^ fpc[1])))), 2, 7):
          print(i,j,l, (fpb[1]-fpa[1]).bit_length(), (fpc[1]).bit_length(), (fpc[1] + fpb[1] - fpa[1]).bit_length(), (fpb[1] + fpc[1]).bit_length(), check(a,b,c,f8_rtz,2,5))
          logging.debug('%s %s %s', i, j, l)
    else:
      if (fpa[2] > fpb[2] or (fpb[2] == fpa[2] and fpa[3] > 0)):
        eval(check(a,b,c,f8_rtz,2,6), fpb[3] ^ fpc[1], 2, 6)
      else:
        eval(check(a,b,c,f8_rtz,2,5), fpa[5] > 0 or fpb[3] ^ fpc[1], 2, 5)


  else:
    if checkcarry(fpb[1] - fpa[1], fpc[0], p):
      if (fpa[2] > fpb[2] or (fpb[2] == fpa[2] and fpa[3] > 0)):
        eval(check(a,b,c,f8_rtz,2,4), 1, 2, 4)

      else: 
        eval(check(a,b,c,f8_rtz,2,3), 1, 2, 3)
    else:
      if (fpa[2] > fpb[2] or (fpb[2] == fpa[2] and fpa[3] > 0)):
        eval(check(a,b,c,f8_rtz,2,2), 0, 2, 2)
      else:
        eval(check(a,b,c,f8_rtz,2,1), fpa[5] > 0, 2, 1)


    """
          if not (eval(check(a,b,c,f8_rtz,2,1), fpa[5] > 0, 2, 1)):
            logging.debug('%s %s %s', i, j, l)
            print(i,j,l, check(a,b,c,f8_rtz,2,1), fpa[5] > 0, fpa[5] == 0)"""
        



        
nbits = 8
f8_rtz = ieee754.ieee_ctx(es=3, nbits=nbits, rm=ieee754.RM.ROUND_TO_ZERO)

start = time.time()

for l in range(2**nbits): #range(2**nbits):
  for j in range(2**nbits):
    for i in range(2**nbits):
      a = ieee754.bits_to_digital(i, f8_rtz)
      b = ieee754.bits_to_digital(j, f8_rtz)
      c = ieee754.bits_to_digital(l, f8_rtz) 
      p = c.ctx.p
      k = c.e - b.e
      h = c.e - a.e
      
      if (c.e > b.e > a.e) and (c.e - a.e < p-1):
        fpa, fpb, fpc = splitsignif(a,b,c)
        if realpos(a.add(b, f8_rtz).add(c, f8_rtz)) and realpos(a.add(b.add(c, f8_rtz), f8_rtz)):
          if realpos(c):
            if realpos(b) & realpos(a):
              case1(a,b,c,f8_rtz, p, k, h)
            elif realpos(b) & realneg(a):
              case2(a,b,c, f8_rtz, p, k, h, i, j, l)
          

                    
end = time.time()

mincase = 4
maxcase = 28


"""
22 58 64
-2 0 1
0.344 1.62 2.0"""

for i in range(1,3):
  for j in range(1,len(same[i])):
    print(f'Case {i}.{j}: Assoc is true: {same[i][j]}, Assoc is false: {different[i][j]}, Total: {same[i][j]+different[i][j]}, Cond Evalulated: T: {evaly[i][j]}, F: {evaln[i][j]}')

print(f'Total: {totals}, Time: {end-start}s')
exit()
                  

"""X = 0 | A | B

   Y = C | D | 0"""
"""print(same, different)
print(total)"""
exit()