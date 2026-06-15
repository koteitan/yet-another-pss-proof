#!/usr/bin/env python3
"""Which of K1/K2/K3 are PURE olt-algebra consequences of R1 (head facts)?
Test on RANDOM term pairs (not class) with the hypotheses:
  hyp: olt B F, B nonempty, F nonempty, B head-viol (not olt (harg B) B).
Then check K1 lead eq, K2 olt harg, K3 F head-viol.  Count fails on RANDOM
(non-class) pairs satisfying the hypotheses. If a K holds 0-fail on RANDOM,
it's pure algebra (provable). If it FAILS, it needs the class.
"""
import sys, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(11)
from valnorm import lt_term, fmtb
def leadof(x): return -1 if x==() else x[0][1]
def harg(x): return None if x==() else x[0][2]
def randterm(depth):
    if depth<=0 or random.random()<0.35: return ()
    n=random.randint(1,3)
    return tuple(('D',random.randint(0,3),randterm(depth-1)) for _ in range(n))
N=3000000
hyp=0; k1f=k2f=k3f=0; ex1=[];ex2=[];ex3=[]
for _ in range(N):
    B=randterm(4); F=randterm(4)
    if B==() or F==(): continue
    if not lt_term(B,F): continue
    aB=harg(B)
    if lt_term(aB,B): continue   # require B head-viol
    hyp+=1
    aF=harg(F)
    if leadof(B)!=leadof(F):
        k1f+=1
        if len(ex1)<3: ex1.append((fmtb(B),fmtb(F)))
    if not lt_term(aB,aF):
        k2f+=1
        if len(ex2)<3: ex2.append((fmtb(B),fmtb(F)))
    if lt_term(aF,F):
        k3f+=1
        if len(ex3)<3: ex3.append((fmtb(B),fmtb(F)))
print(f'random pairs with hyp (olt B F & B head-viol)={hyp}')
print(f'K1 lead B!=lead F   fail = {k1f}')
print(f'K2 not olt aB aF    fail = {k2f}')
print(f'K3 F NOT head-viol  fail = {k3f}')
for e in ex1[:2]: print(' K1ex:',e)
for e in ex2[:2]: print(' K2ex:',e)
for e in ex3[:2]: print(' K3ex:',e)
print('DONE')
