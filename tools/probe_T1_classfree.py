#!/usr/bin/env python3
"""Is maxsub-monotonicity T1 (olt B F => maxsub B<=maxsub F) class-free on wf3?"""
import sys, random
sys.path.insert(0,'.'); sys.setrecursionlimit(1000000); random.seed(9)
from valnorm import lt_term
def Glist(u,x):
    if x==(): return []
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    return (([b]+Glist(u,b)) if u<=a else [])+Glist(u,c)
def maxsub(x):
    if x==(): return 0
    return max(x[0][1],max(maxsub(x[0][2]),maxsub(tuple(x[1:]))))
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
def rt(d):
    if d<=0 or random.random()<0.35: return ()
    a=random.randint(0,4); b=rt(d-1); n=random.randint(0,2)
    return ((0,a,b),)+tuple((0,random.randint(0,4),rt(d-1)) for _ in range(n))
pool=[]
for _ in range(300000):
    t=rt(4)
    if t!=() and wf3(t): pool.append(t)
random.shuffle(pool); S=pool[:3000]
n=0;f=0;ex=[]
for B in S:
    for F in S:
        if not lt_term(B,F): continue
        n+=1
        if maxsub(B)>maxsub(F):
            f+=1
            if len(ex)<3: ex.append((maxsub(B),maxsub(F)))
print(f'wf3 olt pairs={n}, T1 maxsub B<=maxsub F fails={f} (0=>class-free)')
for e in ex: print('  ms',e)
print('DONE')
