#!/usr/bin/env python3
"""Does a NATURAL hypothesis make proj0(proj1 t)=proj1 t class-free-ISH?
Test candidate conditions H on random wf3 t (with a=1):
 H1: every principal subscript of t is >= 1 (no subscript-0 principal in t)
 H2: t = nrm(t0) for some t0 (t is an nrm-image)  [approx: t == nrm(t)]
 H3: lead t >= 1
 H4: maxsub(proj 1 t) achieved at lead (proj 1 t) i.e. lead = maxsub  (the F2 fact)
For each H, among t satisfying H, count proj0(proj1 t) != proj1 t.
If some H gives 0 AND H is implied by the arg-zone structure, that's the lever.
"""
import sys, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(3)
from valnorm import lt_term, nrm
def mkP(a,b,c): return (('D',a,b),)+c
def Glist(u,x):
    if x==(): return []
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    head = ([b]+Glist(u,b)) if u<=a else []
    return head+Glist(u,c)
def Gset(u,x): return set(Glist(u,x))
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
    if x==(): return True
    if y==(): return False
    ax,bx=x[0][1],x[0][2]; ay,by=y[0][1],y[0][2]
    return ax<ay or (ax==ay and (lt_term(bx,by) or bx==by))
def wf3(t):
    if t==(): return True
    a=t[0][1]; b=t[0][2]; c=tuple(t[1:])
    if not wf3(b) or not wf3(c): return False
    for x in Gset(a,b):
        if not lt_term(x,b): return False
    if not hdle(c, ((('D',a,b),))): return False
    return True
def all_subs_ge1(t):
    if t==(): return True
    a=t[0][1]; b=t[0][2]; c=tuple(t[1:])
    if a<1: return False
    return all_subs_ge1(b) and all_subs_ge1(c)
def leadof(x): return 0 if x==() else x[0][1]
def maxsub(x):
    if x==(): return 0
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    return max(a, max(maxsub(b), maxsub(c)))
def rand_term(maxa, depth):
    if depth<=0 or random.random()<0.3: return ()
    n=random.randint(1,3); parts=[]
    for _ in range(n):
        parts.append((random.randint(0,maxa), rand_term(maxa, depth-1)))
    t=()
    for (a,b) in reversed(parts): t=mkP(a,b,t)
    return t
N=300000
H1n=0;H1f=0; H2n=0;H2f=0; H3n=0;H3f=0; H4n=0;H4f=0
for _ in range(N):
    t=rand_term(3,4)
    if not wf3(t): continue
    p1=proj(1,t); bad = (proj(0,p1)!=p1)
    if all_subs_ge1(t):
        H1n+=1
        if bad: H1f+=1
    if nrm(t)==t:
        H2n+=1
        if bad: H2f+=1
    if leadof(t)>=1:
        H3n+=1
        if bad: H3f+=1
    if leadof(p1)==maxsub(p1):
        H4n+=1
        if bad: H4f+=1
print(f'H1 all subs>=1: n={H1n} proj0(proj1 t)!=proj1 t fails={H1f}')
print(f'H2 t is nrm-image: n={H2n} fails={H2f}')
print(f'H3 lead t>=1: n={H3n} fails={H3f}')
print(f'H4 lead(proj1 t)=maxsub: n={H4n} fails={H4f}')
print('DONE')
