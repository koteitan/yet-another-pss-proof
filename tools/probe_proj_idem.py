#!/usr/bin/env python3
"""Is proj idempotent? proj a (proj a t) == proj a t for wf3 t?
If yes (class-free), then proj 0 hb = proj 0 (proj 0 X) = proj 0 X = hb, giving the
class fact for FREE, and tied_crit_lt_hb follows from proj_G. Test random wf3."""
import random
random.seed(7)
from valnorm import lt_term
def Glist(u,x):
    if x==(): return []
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    head=([b]+Glist(u,b)) if u<=a else []
    return head+Glist(u,c)
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
    a=random.randint(0,4); b=rand_term(depth-1)
    n=random.randint(0,2); tail=[]
    for _ in range(n):
        tail.append((0,random.randint(0,4),rand_term(depth-1)))
    return ((0,a,b),)+tuple(tail)
n=0; idem_fail=0; ex=[]
for _ in range(3000000):
    t=rand_term(4)
    if t==() or not wf3(t): continue
    n+=1
    for a in (0,1):
        p=proj(a,t); pp=proj(a,p)
        if pp!=p:
            idem_fail+=1
            if len(ex)<8: ex.append((a,t,p,pp))
            break
print(f'random wf3 terms = {n}')
print(f'proj idempotence FAIL (proj a (proj a t) != proj a t) = {idem_fail}  (0 => idempotent)')
for (a,t,p,pp) in ex:
    print(' a=',a,' t=',t)
    print('   proj=',p,' projproj=',pp)
print('DONE')
