#!/usr/bin/env python3
"""Is 'fires(0,X) <=> not olt (headarg X) X' a general wf3 fact, or class-bound?
Also: when X fires, is proj 0 X == headarg X a general wf3 fact?
Test on RANDOM wf3 terms (in_OT) of the binary form, not just arg-zone images.
"""
import sys, itertools, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(7)
from valnorm import lt_term, fmtb, G, in_OT, nrm
def projlist(a,x): return [g for g in G(a,x) if not lt_term(g,x)]
def fires(a,x): return len(projlist(a,x))>0
def proj(a,x):
    bb=x
    while True:
        bad=projlist(a,bb)
        if not bad: break
        g=bad[0]
        for h in bad[1:]:
            if lt_term(g,h): g=h
        bb=g
    return bb
def leadof(x): return -1 if x==() else x[0][1]
def headarg(x): return None if x==() else x[0][2]
def randterm(depth):
    if depth<=0 or random.random()<0.3: return ()
    n=random.randint(1,3)
    ps=[]
    for _ in range(n):
        v=random.randint(0,3); ps.append(('D',v,randterm(depth-1)))
    # weakly decreasing for in_OT-ish; sort
    return tuple(ps)
N=400000
wf=0; t1f=0; t2f=0; ex1=[]; ex2=[]
fired=0
for _ in range(N):
    X=randterm(4)
    if not in_OT(X): continue
    if X==(): continue
    wf+=1
    f=fires(0,X)
    ha=headarg(X)
    head_viol=(ha is not None) and (not lt_term(ha,X))
    if f!=head_viol:
        t1f+=1
        if len(ex1)<3: ex1.append((fmtb(X),f,head_viol))
    if f:
        fired+=1
        m=proj(0,X)
        if head_viol and m!=ha:
            t2f+=1
            if len(ex2)<3: ex2.append((fmtb(X),fmtb(m),fmtb(ha)))
print(f'wf3 terms tested={wf}, fired={fired}')
print(f'T1 fires != head-arg-viol (general wf3) = {t1f}')
for e in ex1: print('   ex1:',e)
print(f'T2 head-viol but proj != headarg (general wf3) = {t2f}')
for e in ex2: print('   ex2:',e)
print('DONE')
