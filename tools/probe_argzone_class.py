#!/usr/bin/env python3
"""Find the EXACT invariant I distinguishing arg-zone nrm-images (proj y mono OK)
from arbitrary wf3 (proj y mono FALSE).

For each arg-zone image nB (grouped by y), record:
  - lead(nB) (top principal subscript)  vs y
  - does proj y fire on nB?  what does it do?
  - min top subscript, all top subscripts
Hypotheses:
  H1: y < lead(nB)  for all arg-zone images  (head sub strictly below arg lead)
  H2: y <= every TOP subscript of nB  (no top principal below y)
  H3: proj y does NOT fire (proj y nB == nB) for arg-zone images
Then RE-TEST proj-mono on the wf3 pool RESTRICTED to the discovered invariant,
to confirm it kills the 84960 reversals.
"""
import sys, itertools, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(7)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term, fmtb, G
from fast_pss import oper

def proj(a,x):
    bb=x
    while True:
        bad=[g for g in G(a,bb) if not lt_term(g,bb)]
        if not bad: break
        g=bad[0]
        for h in bad[1:]:
            if lt_term(g,h): g=h
        bb=g
    return bb

def lead(t): return t[0][1] if t else -1   # top principal subscript, -1 if Z
def topsubs(t): return [p[1] for p in t]
def takeW(r):
    out=[]
    for p in r:
        if p[0]>0: out.append(p)
        else: break
    return out

base=enum_ST(seed_max_v=5,oper_ns=(1,2,3,4,5),max_len=16,rounds=8)
extra=set(base); cur=list(extra)
for _ in range(5):
    new=[]
    for M in cur:
        M=list(M)
        if len(M)<2: continue
        for n in (1,2,3,4,5):
            tt=tuple(oper(M,n))
            if len(tt)<=22 and tt not in extra:
                extra.add(tt); new.append(tt)
    cur=new
    if not cur: break
print('deep ST closure =',len(extra),flush=True)

from collections import defaultdict
byY=defaultdict(set)
for M in extra:
    M=list(M)
    if not M or M[0][0]!=0: continue
    y=M[0][1]; aM=tuple(takeW(M[1:]))
    if aM:
        byY[y].add(nrm(conv(translate(list(aM)))))

# measure invariants on arg-zone images
h1=h2=h3=0; tot=0
h1bad=[]; h2bad=[]; h3bad=[]
for y,S in byY.items():
    for nB in S:
        tot+=1
        if y < lead(nB): h1+=1
        else: h1bad.append((y,nB)) if len(h1bad)<6 else None
        if nB and y <= min(topsubs(nB)): h2+=1
        else: h2bad.append((y,nB)) if len(h2bad)<6 else None
        if proj(y,nB)==nB: h3+=1
        else: h3bad.append((y,nB)) if len(h3bad)<6 else None
print(f'arg-zone images total={tot}')
print(f'H1 y<lead(nB)         : holds {h1}/{tot}')
for y,nB in h1bad[:5]: print(f'    FAIL y={y} lead={lead(nB)}: {fmtb(nB)}')
print(f'H2 y<=min topsub(nB)  : holds {h2}/{tot}')
for y,nB in h2bad[:5]: print(f'    FAIL y={y} mintop={min(topsubs(nB)) if nB else None}: {fmtb(nB)}')
print(f'H3 proj y nB == nB    : holds {h3}/{tot}')
for y,nB in h3bad[:5]: print(f'    FAIL y={y}: {fmtb(nB)} -> {fmtb(proj(y,nB))}')
print('DONE')
