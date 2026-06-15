#!/usr/bin/env python3
"""Confirm maxo monotonicity needs wf3 (in_OT) and holds with it.
Pool = subterms of nrm-images, BUT keep only in_OT ones.
Test at y=0,1,2:
  R1: olt B F & in_OT B & in_OT F ==> le_term (M G(y,B)) (M G(y,F))  [Z sentinel]
  R3: + firing: vB!=[] ==> vF!=[] & le_term(maxo vB)(maxo vF)
"""
import sys, itertools, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(11)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term, fmtb, G, in_OT
from fast_pss import oper
Z=()
def le_term(a,b): return a==b or lt_term(a,b)
def maxo_or_Z(lst):
    if not lst: return Z
    g=lst[0]
    for h in lst[1:]:
        if lt_term(g,h): g=h
    return g
def projlist(a,x): return [g for g in G(a,x) if not lt_term(g,x)]
def maxo_of(lst):
    g=lst[0]
    for h in lst[1:]:
        if lt_term(g,h): g=h
    return g
base=enum_ST(seed_max_v=4,oper_ns=(1,2,3,4),max_len=13,rounds=6)
extra=set(base); cur=list(extra)
for _ in range(3):
    new=[]
    for M in cur:
        M=list(M)
        if len(M)<2: continue
        for n in (1,2,3,4):
            tt=tuple(oper(M,n))
            if len(tt)<=18 and tt not in extra: extra.add(tt); new.append(tt)
    cur=new
    if not cur: break
print('ST closure =',len(extra),flush=True)
pool=set()
def subterms(t):
    yield t
    for i in range(len(t)):
        yield t[i:]
        yield from subterms(t[i][2])
for M in extra:
    t=nrm(conv(translate(list(M))))
    for s in subterms(t):
        pool.add(s)
pool=[t for t in pool if in_OT(t)]
random.shuffle(pool); pool=pool[:1500]
print('in_OT term pool =',len(pool),flush=True)
for y in (0,1,2):
    Mc={}; Vc={}
    for t in pool:
        Mc[t]=maxo_or_Z(G(y,t)); Vc[t]=projlist(y,t)
    tot=0; r1f=0; r3f=0; exR3=[]
    for B,F in itertools.combinations(pool,2):
        if lt_term(B,F): pass
        elif lt_term(F,B): B,F=F,B
        else: continue
        tot+=1
        if not le_term(Mc[B],Mc[F]): r1f+=1
        vB=Vc[B]; vF=Vc[F]
        if vB:
            if not (vF and le_term(maxo_of(vB),maxo_of(vF))):
                r3f+=1
                if len(exR3)<3: exR3.append((B,F))
    print(f'y={y}: pairs={tot}  R1 FAIL={r1f}  R3(viol maxo mono) FAIL={r3f}')
    for B,F in exR3[:2]:
        print('   R3FAIL B=%s'%fmtb(B)); print('          F=%s'%fmtb(F))
print('DONE')
