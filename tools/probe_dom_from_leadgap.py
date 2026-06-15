#!/usr/bin/env python3
"""Does argzone_head_dominates follow from leadgap(a<lead hb)+wf3+firing?
X=P a hb hc wf3. lead hb>a. For ANY violator g in Gterm 0 X (not olt g X), is not olt hb g?
i.e. hb is the maximal violator. Test using ONLY: wf3 X, lead hb>a, g viol.
We test the IMPLICATION on firing images directly (already know it holds 0/...).
But ALSO test the PURELY ALGEBRAIC claim:
  forall wf3 t = P a hb hc with lead hb>a, forall g in Gterm 0 t with not olt g t: not olt hb g.
Search RANDOM wf3 terms (not arg-zone!) with lead hb>a to see if algebraic claim holds class-free.
If class-free TRUE -> dominance reduces to leadgap algebraically (great).
If class-free FALSE -> need class.
"""
import sys, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(7)
from valnorm import lt_term
def Glist(u,x):
    if x==(): return []
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    head = ([b]+Glist(u,b)) if u<=a else []
    return head+Glist(u,c)
def Gterm(u,x): return Glist(u,x)
def leadof(x): return 0 if x==() else x[0][1]
def harg(x): return () if x==() else x[0][2]
def wf3(x):
    if x==(): return True
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    if not wf3(b): return False
    if not wf3(c): return False
    for g in Glist(a,b):
        if not lt_term(g,b): return False
    # hdle c (P a b Z)
    if c!=():
        e=c[0][1]; f=c[0][2]
        if not (a<e or (a==e and (lt_term(b,f) or b==f))): return False
    return True
# random three terms
def rand_term(depth):
    if depth<=0 or random.random()<0.35: return ()
    a=random.randint(0,4)
    b=rand_term(depth-1)
    # build tail as list
    n=random.randint(0,2)
    tail=[]
    for _ in range(n):
        tail.append((0,random.randint(0,4),rand_term(depth-1)))
    # represent as tuple of principals: (dummy, sub, arg)
    return ((0,a,b),)+tuple(tail)
def fmt(x):
    return x
cnt=0; tested=0; dom_fail=0; exs=[]
for _ in range(2000000):
    t=rand_term(4)
    if t==() : continue
    if not wf3(t): continue
    a=leadof(t); hb=harg(t)
    if not (leadof(hb)>a): continue   # need lead hb>a
    # is t firing? need some violator
    V=[g for g in Glist(0,t) if not lt_term(g,t)]
    if not V: continue
    cnt+=1
    for g in V:
        tested+=1
        if lt_term(hb,g):   # olt hb g => dominance fails
            dom_fail+=1
            if len(exs)<3: exs.append((t,g,hb))
            break
print(f'wf3 terms with lead hb>a and firing = {cnt}')
print(f'dominance failures (exists viol g with olt hb g) = {dom_fail} (0 => class-free)')
for e in exs: print('  EX', e)
print('DONE')
