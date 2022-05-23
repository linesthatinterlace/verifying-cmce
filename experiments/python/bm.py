from sage.all import *
from itertools import islice

F = GF(4)
R = PolynomialRing(F, 'D')
D = R.gen(0)

def bm (s : list(F)) :
  C = R(1)
  B = R(1)
  x = 1
  L = 0
  b = F(1)
  n = len(s)
  for N in range(n) :
    d = sum(C[i]*s[N - i] for i in range(L + 1))
    if d == 0 :
      x += 1
    elif 2*L > N :
      C -= (d/b)*(D**x)*B
      x += 1
    else :
      T = C
      C -= (d/b)*(D**x)*B
      L = N + 1 - L
      B = T
      b = d 
      x = 1

  return L, C

def lfsr (L, C, seed) :
  C = R(C)
  s = seed[:L]
  for v in s :
    yield v
  while True:
    v = -sum(C[i]*s[L - i] for i in range(1, L + 1))
    s.pop(0)
    s.append(v)
    yield v

def seed_check (seed):
  L, C = bm(seed)
  seed2 = lfsr(L, C, seed)
  n = len(seed)
  seed2 = list(islice(seed2, n))
  return seed == seed2
