#!/usr/bin/env python3
"""Class-free reductions for clause-2 facts (1) S_Gviol and (2) T_allGhb.
Test on RANDOM wf3 terms (NOT the arg-zone class) to see if either holds class-free,
and under what extra hypothesis.

We test, for random wf3 X = P a b c that FIRES at 0 (some violator in Gterm 0 X):
 (2a) T_allGhb : all g in Gterm 0 b : olt g b   (b=harg, b is 0-stable)
 (1a) S_Gviol  : every violator g in Gterm 0 X is in {b} U Gterm 0 b
 (HV) head b is itself a violator: not olt b X
We expect these to FAIL on random wf3 (class-essential). Count failures.

Then test the SAME facts but only when X is itself 0-STABLE-headed via:
 cond proj0 b == b  (b non-firing at 0): does S_Gviol then follow? i.e. is
   "b non-firing at 0" + wf3 X  =>  S_Gviol ?  (the tail produces no 0-violator)
"""
import sys, random, itertools
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(7)
from valnorm import lt_term

# three terms as nested tuples: () = Z ; ((D,a,b), <tail principals...>) where each principal is (D,a,argtuple)
# Represent like valnorm: tuple of principals, principal = ('D', a, argtuple)
def Z(): return ()
def mkP(a,b,c):
    # P a b c  = principal ('D',a,b) prepended to tail c (c is a term-tuple)
    return (('D',a,b),)+c
def Glist(u,x):
    if x==(): return []
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    head = ([b]+Glist(u,b)) if u<=a else []
    return head+Glist(u,c)
def Gset(u,x): return set(Glist(u,x))
def harg(x): return () if x==() else x[0][2]
def leadof(x): return 0 if x==() else x[0][1]
def fires(a,x): return any(not lt_term(g,x) for g in Glist(a,x))
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
def hdle(x,y):
    # hdle on principals
    if x==(): return True
    if y==(): return False
    ax,bx=x[0][1],x[0][2]; ay,by=y[0][1],y[0][2]
    return ax<ay or (ax==ay and (lt_term(bx,by) or bx==by))
def wf3(t):
    if t==(): return True
    a=t[0][1]; b=t[0][2]; c=tuple(t[1:])
    if not wf3(b): return False
    if not wf3(c): return False
    # all x in Gterm a b : olt x b
    for x in Gset(a,b):
        if not lt_term(x,b): return False
    # hdle c (P a b Z)
    if not hdle(c, ((('D',a,b),))): return False
    return True

def rand_term(maxa, depth):
    if depth<=0 or random.random()<0.3:
        return ()
    n=random.randint(1,3)
    out=()
    # build tail in non-increasing head order is hard; just build then filter via wf3
    parts=[]
    for _ in range(n):
        a=random.randint(0,maxa)
        b=rand_term(maxa, depth-1)
        parts.append((a,b))
    t=()
    for (a,b) in reversed(parts):
        t=mkP(a,b,t)
    return t

# generate random wf3 firing-at-0 terms
N=400000
seen=0; fire0=0
n2a=0; n1a=0; nHV=0
# stable-tail conditional test
cond_seen=0; cond_S_fail=0
for _ in range(N):
    t=rand_term(3,4)
    if not wf3(t): continue
    if t==(): continue
    seen+=1
    if not fires(0,t): continue
    fire0+=1
    b=harg(t)
    Gb=Gset(0,b)
    if any(not lt_term(g,b) for g in Gb): n2a+=1   # T_allGhb fails
    inserthbG=Gb|{b}
    viol_bad=False
    for g in Gset(0,t):
        if lt_term(g,t): continue
        if g not in inserthbG: viol_bad=True; break
    if viol_bad: n1a+=1
    if not (not lt_term(b,t)): nHV+=1   # head not a violator
    # conditional: if b is 0-stable, does S_Gviol hold?
    if proj(0,b)==b:
        cond_seen+=1
        bad=False
        for g in Gset(0,t):
            if lt_term(g,t): continue
            if g not in inserthbG: bad=True; break
        if bad: cond_S_fail+=1
print(f'random wf3 seen={seen}, firing@0={fire0}')
print(f'(2a) T_allGhb fails on random wf3 = {n2a}  (>0 => class-essential)')
print(f'(1a) S_Gviol  fails on random wf3 = {n1a}  (>0 => class-essential)')
print(f'(HV) head NOT a violator on random firing = {nHV} (>0 => HV class-essential)')
print(f'conditional: b 0-stable cases={cond_seen}, S_Gviol still fails = {cond_S_fail}')
print('DONE')
