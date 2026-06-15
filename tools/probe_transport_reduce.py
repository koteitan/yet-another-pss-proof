#!/usr/bin/env python3
"""Does transport reduce to head-shape facts class-free?
Given B=P aB hbB hcB, F=P aF hbF hcF, both wf3, both fire (proj0 != ),
 with head-shape: lead hbB>aB, hbB maximal violator, proj0 B=hbB; same for F.
 olt B F.  Claims:
  T-fire: F fires  (we ASSUME both fire here, so test the OTHER content)
  T-ord:  olt hbB hbF.
 Test T-ord as class-free implication:
   for random wf3 B,F with [lead hbB>aB, lead hbF>aF, hbB max viol, hbF max viol,
    proj0 B=hbB, proj0 F=hbF], olt B F  =>  olt hbB hbF ?
 Also test the simpler: olt B F + both head-shape => olt hbB hbF, restricting to
   pairs where proj0B=hbB and proj0F=hbF (the firing identity).
"""
import sys, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(101)
from valnorm import lt_term
def Glist(u,x):
    if x==(): return []
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    head = ([b]+Glist(u,b)) if u<=a else []
    return head+Glist(u,c)
def leadof(x): return 0 if x==() else x[0][1]
def harg(x): return () if x==() else x[0][2]
def maxo(x,ys):
    m=x
    for y in ys:
        if lt_term(m,y): m=y
    return m
def proj(a,x):
    bb=x
    while True:
        gs=[g for g in Glist(a,bb) if not lt_term(g,bb)]
        if not gs: break
        bb=maxo(gs[0],gs[1:])
    return bb
def wf3(x):
    if x==(): return True
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    if not wf3(b) or not wf3(c): return False
    for g in Glist(a,b):
        if not lt_term(g,b): return False
    if c!=():
        e=c[0][1]; f=c[0][2]
        if not (a<e or (a==e and (lt_term(b,f) or b==f))): return False
    return True
def rand_term(depth):
    if depth<=0 or random.random()<0.35: return ()
    a=random.randint(0,3); b=rand_term(depth-1)
    n=random.randint(0,2); tail=[]
    for _ in range(n):
        tail.append((0,random.randint(0,3),rand_term(depth-1)))
    return ((0,a,b),)+tuple(tail)
def headshape(t):
    if t==(): return False
    a=leadof(t); hb=harg(t)
    if not (leadof(hb)>a): return False
    if proj(0,t)!=hb: return False
    V=[g for g in Glist(0,t) if not lt_term(g,t)]
    if not V: return False
    for g in V:
        if lt_term(hb,g): return False  # hb not maximal
    return True
pool=[]
for _ in range(400000):
    t=rand_term(4)
    if t!=() and wf3(t) and headshape(t): pool.append(t)
print('headshape pool =',len(pool))
n=0; Tord_fail=0; ex=[]
import itertools
random.shuffle(pool)
for B in pool[:4000]:
    for F in pool[:4000]:
        if not lt_term(B,F): continue   # need olt B F
        n+=1
        if not lt_term(harg(B),harg(F)):   # olt hbB hbF should hold
            Tord_fail+=1
            if len(ex)<3: ex.append((B,F))
        if n>3000000: break
    if n>3000000: break
print(f'olt B F pairs (both headshape) = {n}')
print(f'T-ord olt hbB hbF fails = {Tord_fail} (0 => class-free)')
for e in ex: print('  ex',e)
print('DONE')
