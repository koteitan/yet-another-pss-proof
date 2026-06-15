#!/usr/bin/env python3
"""Is tied_crit_lt_hb CLASS-FREE? Conjecture:
  For wf3 t = P L tb tc, every g in Gterm 0 t with lead g == lead t (=L) has olt g t.
Equivalently (the lemma): hb wf3, every g in Gterm 0 hb with lead g==lead hb has olt g hb.
Test on RANDOM wf3 terms (no arg-zone class). If 0 failures -> class-free, only wf3 needed.
"""
import random
random.seed(12345)
from valnorm import lt_term
def Glist(u,x):
    if x==(): return []
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    head=([b]+Glist(u,b)) if u<=a else []
    return head+Glist(u,c)
def leadof(x): return 0 if x==() else x[0][1]
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
    a=random.randint(0,4); b=rand_term(depth-1)
    n=random.randint(0,2); tail=[]
    for _ in range(n):
        tail.append((0,random.randint(0,4),rand_term(depth-1)))
    return ((0,a,b),)+tuple(tail)
n=0; fail=0; checked=0; fex=[]
for _ in range(4000000):
    t=rand_term(4)
    if t==() or not wf3(t): continue
    n+=1
    L=leadof(t)
    for g in set(Glist(0,t)):
        if leadof(g)!=L: continue
        checked+=1
        if not lt_term(g,t):
            fail+=1
            if len(fex)<10: fex.append((t,g))
print(f'random wf3 terms = {n}')
print(f'tied criticals (lead g == lead t) checked = {checked}')
print(f'CLASS-FREE FAIL: NOT olt g t = {fail}  (0 => class-free, only wf3 needed)')
for (t,g) in fex:
    print(' t=',t)
    print(' g=',g,' lead t=',leadof(t),' lead g=',leadof(g))
print('DONE')
