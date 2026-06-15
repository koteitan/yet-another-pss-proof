#!/usr/bin/env python3
"""Is proj 0 (proj a t) == proj a t for all wf3 t and all a? (class-free)
i.e. is a proj-a image automatically proj-0-stable / 0-non-firing?
Equivalently: all g in Gterm 0 (proj a t) : olt g (proj a t).
proj_G gives this for Gterm a, not Gterm 0. Test whether subscript 0 also holds.

Also test the more basic monotone-in-subscript claim:
 P1: proj 0 (proj a t) == proj a t      (random wf3 t, random a)
 P2: not pfire 0 (proj a t)              (same)
 P3 (counter-direction sanity): Gterm 0 (proj a t) vs Gterm a (proj a t):
     are they EQUAL as sets? (Gsub_eq) -- if so subscript irrelevant on proj-images
Run on RANDOM wf3 (class-free).
"""
import sys, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(11)
from valnorm import lt_term
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
def rand_term(maxa, depth):
    if depth<=0 or random.random()<0.3: return ()
    n=random.randint(1,3); parts=[]
    for _ in range(n):
        parts.append((random.randint(0,maxa), rand_term(maxa, depth-1)))
    t=()
    for (a,b) in reversed(parts): t=mkP(a,b,t)
    return t
N=300000
seen=0; p1=0; p2=0; p3=0; ntest=0
for _ in range(N):
    t=rand_term(3,4)
    if not wf3(t): continue
    seen+=1
    a=random.randint(0,3)
    pa=proj(a,t)
    ntest+=1
    if proj(0,pa)!=pa: p1+=1
    if fires(0,pa): p2+=1
    if Gset(0,pa)!=Gset(a,pa): p3+=1
print(f'wf3 seen={seen}, tested={ntest}')
print(f'P1 proj 0 (proj a t) != proj a t = {p1} (0 => proj-images are 0-stable, CLASS-FREE!)')
print(f'P2 pfire 0 (proj a t)            = {p2} (0 => same)')
print(f'P3 Gterm 0 (proj a t) != Gterm a (proj a t) = {p3} (info: subscript matters?)')
print('DONE')
