#!/usr/bin/env python3
"""Probe pure structural monotonicity of maxo(Glist y t) in t under olt.
Goal lemma candidate (UNCONDITIONAL, no firing, no wf3, no arg-zone):
   GLMONO:  olt B F  ==>  Glist y B = []  OR  Glist y F != [] and
            le_term (maxo Glist y B) (maxo Glist y F)
Equivalently with a sentinel Z for empty:
   define M(t) = maxo over (Glist y t) or Z if empty.
   olt B F ==> le_term (M B) (M F)?   <-- test this with Z sentinel (Z is bottom)

Also test refinements that might be needed for the induction to go through:
   R1: olt B F ==> le_term (M y B) (M y F)            [Z sentinel]
   R2: same but also need: lead-subscript control. test if FALSE to know.
   R3: the firing-restricted le_term(maxo vB)(maxo vF)  [viol filter] under olt B F & vB!=[]
"""
import sys, itertools, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(11)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term, fmtb, G
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
# Use a broad pool of arbitrary wf3-ish terms = nrm images, plus their subterms,
# to stress GLMONO on as wide a class as possible.
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
    # t is conv-term: tuple of ('D',a,b). collect t and all sub args/tails
    yield t
    for i in range(len(t)):
        yield t[i:]            # tails
        yield from subterms(t[i][2])  # args
for M in extra:
    t=nrm(conv(translate(list(M))))
    for s in subterms(t):
        pool.add(s)
pool=list(pool); random.shuffle(pool); pool=pool[:1500]
print('term pool (with subterms) =',len(pool),flush=True)
for y in (0,1,2):
    Mc={}; Vc={}
    for t in pool:
        Mc[t]=maxo_or_Z(G(y,t)); Vc[t]=projlist(y,t)
    tot=0; r1f=0; r3f=0; exR1=[]
    for B,F in itertools.combinations(pool,2):
        if lt_term(B,F): pass
        elif lt_term(F,B): B,F=F,B
        else: continue
        tot+=1
        if not le_term(Mc[B],Mc[F]):
            r1f+=1
            if len(exR1)<3: exR1.append((B,F,Mc[B],Mc[F]))
        vB=Vc[B]; vF=Vc[F]
        if vB:
            if not (vF and le_term(maxo_of(vB),maxo_of(vF))): r3f+=1
    print(f'y={y}: pairs={tot}  R1(maxo G mono,Z-sentinel) FAIL={r1f}  R3(viol maxo mono) FAIL={r3f}')
    for B,F,mb,mf in exR1[:2]:
        print('   R1FAIL B=%s F=%s'%(fmtb(B),fmtb(F)))
        print('          MB=%s MF=%s'%(fmtb(mb),fmtb(mf)))
print('DONE')
