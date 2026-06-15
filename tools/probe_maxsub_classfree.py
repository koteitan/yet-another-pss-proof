#!/usr/bin/env python3
"""Which maxsub facts are CLASS-FREE (hold on all wf3 terms) vs class-essential?
Test on random wf3 terms (NOT arg-zone):
 G1: g in Gterm u t (g!=Z) => maxsub g <= maxsub t      (subterm maxsub bound) [expect class-free]
 G2: lead t <= maxsub t                                 [trivial class-free]
 G3: lead(proj 0 t) = maxsub t   for firing t           [F2 - class-free?]
 G4: pfire 0 t <=> lead t < maxsub t                    [F1 - class-free?]
 G5: maxsub t == cmax(spine t)                          [SP - class-free? likely NOT]
 G6: olt(maxo of level-0 violators, ...) lead = maxsub
 G7: maximal violator m=proj0 t has not olt m g for all viol g, and lead m=maxsub t
"""
import sys, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(31)
from valnorm import lt_term
def Glist(u,x):
    if x==(): return []
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    head = ([b]+Glist(u,b)) if u<=a else []
    return head+Glist(u,c)
def leadof(x): return 0 if x==() else x[0][1]
def harg(x): return () if x==() else x[0][2]
def spine(x):
    if x==(): return []
    return [x[0][1]]+spine(x[0][2])
def maxsub(x):
    if x==(): return 0
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    return max(a,max(maxsub(b),maxsub(c)))
def cmax(s): return max(s) if s else 0
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
g1=0;g3=0;g4=0;g5=0; n=0; nfire=0
g3ex=[];g5ex=[]
for _ in range(3000000):
    t=rand_term(4)
    if t==() or not wf3(t): continue
    n+=1
    ms=maxsub(t); s=spine(t); cm=cmax(s); lt=leadof(t)
    # G1
    for g in Glist(0,t):
        if g!=() and maxsub(g)>ms: g1+=1; break
    # G5
    if ms!=cm:
        g5+=1
        if len(g5ex)<3: g5ex.append(t)
    fr = any(not lt_term(gg,t) for gg in Glist(0,t))
    # G4
    if fr != (lt<ms): g4+=1
    if fr:
        nfire+=1
        px=proj(0,t)
        if leadof(px)!=ms:
            g3+=1
            if len(g3ex)<3: g3ex.append(t)
print(f'wf3 terms = {n}, firing = {nfire}')
print(f'G1 maxsub g<=maxsub t (g in Gterm0): fails={g1} (0=>class-free)')
print(f'G4 pfire0 <=> lead<maxsub          : fails={g4} (0=>class-free)')
print(f'G3 lead(proj0 t)=maxsub t (firing) : fails={g3} (0=>class-free)')
print(f'G5 maxsub==cmax(spine)             : fails={g5} (0=>class-free)')
for e in g3ex: print('  g3ex',e)
for e in g5ex: print('  g5ex',e)
print('DONE')
