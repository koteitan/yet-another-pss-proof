#!/usr/bin/env python3
"""CONSOLIDATED soundness gate + factoring analysis for the §1 core
   proj_nrm_argzone_olt   (term level, nrm.thy ~line 1866).

Records (deep ST closure +5, ~1.0M forms) the verified TRUE facts and the
FALSE proj-mono candidates ruled out THIS SESSION, so they are never retried.

TRUE (separable, formalizable):
  D1  NRMMONO-on-argzone: olt B F => olt (nrm B)(nrm F)   for arg-zone translates
      [44850 ordered pairs / 0 reversals / 0 collapses]  -- the clean nrm half.
  IST  arg-zone value bound: every value v in aM satisfies y<=v
      [1013167/1013167]  -- feeds NT_subs/proj_subs.

FALSE (counterexamples; DO NOT enshrine):
  PROJMONO        wf3 b f, olt b f => olt(proj a(nrm b))(proj a(nrm f))   FALSE
                  [prior: 14739 reversals universe B]
  PROJMONO_WF3    wf3 p q, olt p q => olt(proj y p)(proj y q)            FALSE
                  [84960 reversals / 2.83M  -- e.g. lo=D0(D1(..)), y=0]
  PROJMONO_GEQ    + all subscripts of p,q >= y                            FALSE
                  [177329 reversals  -- the >=y bound is vacuous at y=0]
  C1              oV(proj y(nrm B)) = oV B                                FALSE
                  [prior: 266594/1013167  proj strictly raises the value]

DIAGNOSIS: proj-mono has NO local term-level characterization (wf3 / >=y /
P_subdom all fail). The ONLY trivial fragment is P_canon (proj y t == t, no
fire) -> 0 reversals but only covers 72% of arg-zone images. The irreducible
content lives ENTIRELY in the firing 28% (== prior art's "fire x sum-vs-nest"
crux, memo 続83). Hence the core does NOT factor through a proj-side invariant;
proj.nrm must be handled as a unit on the arg-zone class.
"""
import sys, itertools, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(23)
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
byY_trans=defaultdict(set)   # y -> arg-zone translates B
ist_ok=ist_tot=0
for M in extra:
    M=list(M)
    if not M or M[0][0]!=0: continue
    y=M[0][1]; aM=tuple(takeW(M[1:]))
    if not aM: continue
    ist_tot+=1
    if all(v>=y for (i,v) in aM): ist_ok+=1
    byY_trans[y].add(aM)
print(f'IST arg-zone value bound (all v>=y): {ist_ok}/{ist_tot}')

# D1: nrm order-pres on arg-zone translates, grouped by y
cap=300
tot=rev=coll=0
for y,S in byY_trans.items():
    S=list(S)
    if len(S)>cap: S=random.sample(S,cap)
    Bs=[conv(translate(list(a))) for a in S]
    for B,F in itertools.combinations(Bs,2):
        if lt_term(B,F): lo,hi=B,F
        elif lt_term(F,B): lo,hi=F,B
        else: continue
        tot+=1
        nl,nh=nrm(lo),nrm(hi)
        if lt_term(nh,nl): rev+=1
        elif nl==nh: coll+=1
print(f'D1 NRMMONO-on-argzone: pairs={tot} reversals={rev} collapses={coll}')
print('DONE')
