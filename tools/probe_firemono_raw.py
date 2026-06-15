#!/usr/bin/env python3
"""Is firing monotone UNCONDITIONALLY (any wf3? any term?)?
 pfire y B (exists viol crit of B) and olt B F  => pfire y F ?
Test on:
  (a) arbitrary terms (subterms pool)
  (b) in_OT pool
to find the most general TRUE form for an Isabelle structural-induction lemma.
Also test the candidate MECHANISM lemma that would PROVE it by induction:
  FM: B has a viol crit gB (not olt gB B). olt B F. Then F has a viol crit.
      Concretely is there gF in G(y,F) with not olt gF F?
  And the sharper transported witness: is gB itself (B's max viol crit) <= some
  crit of F, giving F a viol crit >= B > ... ?
"""
import sys, itertools, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(5)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term, fmtb, G, in_OT
from fast_pss import oper
def projlist(a,x): return [g for g in G(a,x) if not lt_term(g,x)]
def fires(a,x): return len(projlist(a,x))>0
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
pool=list(pool); random.shuffle(pool); pool=pool[:2000]
poolOT=[t for t in pool if in_OT(t)]
print('pool=',len(pool),' in_OT=',len(poolOT),flush=True)
for name,P in (('ALL',pool),('in_OT',poolOT)):
    for y in (0,1,2):
        FR={t:fires(y,t) for t in P}
        tot=0; fn=0; ex=[]
        for B,F in itertools.combinations(P,2):
            if lt_term(B,F): pass
            elif lt_term(F,B): B,F=F,B
            else: continue
            tot+=1
            if FR[B] and not FR[F]:
                fn+=1
                if len(ex)<2: ex.append((B,F))
        print(f'{name} y={y}: pairs={tot} FN(B fires,F no)={fn}')
        for B,F in ex[:1]:
            print('   B=%s'%fmtb(B)); print('   F=%s'%fmtb(F))
print('DONE')
