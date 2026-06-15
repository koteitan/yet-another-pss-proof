#!/usr/bin/env python3
"""Pin down the two factors and their required invariants.

F1 (nrm mono on NF): for ANY two NF terms v,u (translates of ST forms, not just
   arg zones) with olt v u, is olt (nrm v) (nrm u)?  [= nrm_order_pres; circular
   if used, but check it's the SAME content]
F2-arb (proj mono on arbitrary wf3): olt p q (both wf3) => olt (proj y p)(proj y q)?
   EXPECT FALSE (PROJMONO false). Confirm with counterexample.
F2-nrm (proj mono on nrm-images of arg trans): the actual D2. confirm true.
F2-class: characterize the class of nrm-images of arg-zone translates. Is it
   exactly "wf3 + every top principal subscript >= 1"? or "wf3 hereditarily-...".
   Test proj-mono on:  (a) all wf3 pairs, (b) wf3 with all top-subs>=1.
"""
import sys, itertools, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(23)
from wfe_explore import translate, enum_ST, fmt
from valnorm import conv, nrm, lt_term, fmtb, G, in_OT
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

def topsubs(t): return [p[1] for p in t]

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

# Collect the nrm-images of arg-zone translates, grouped by y (the actual D2 class)
from collections import defaultdict
byY_nrm=defaultdict(set)   # y -> set of nrm-images
for M in extra:
    M=list(M)
    if not M or M[0][0]!=0: continue
    y=M[0][1]; aM=tuple(takeW(M[1:]))
    if aM:
        nB=nrm(conv(translate(list(aM))))
        byY_nrm[y].add(nB)

# F2-nrm: proj y mono on these images
cap=350
tot=rev=coll=0; exR=[]
for y,S in byY_nrm.items():
    S=list(S)
    if len(S)>cap: S=random.sample(S,cap)
    for p,q in itertools.combinations(S,2):
        if lt_term(p,q): lo,hi=p,q
        elif lt_term(q,p): lo,hi=q,p
        else: continue
        tot+=1
        pl,ph=proj(y,lo),proj(y,hi)
        if lt_term(ph,pl): rev+=1; exR.append((y,lo,hi)) if len(exR)<5 else None
        elif pl==ph: coll+=1
print(f'F2-nrm proj y mono on nrm-images-of-argtrans: pairs={tot} rev={rev} coll={coll}')
for y,lo,hi in exR[:4]: print(f'   REV y={y}: {fmtb(lo)} <o {fmtb(hi)} -> {fmtb(proj(y,lo))} vs {fmtb(proj(y,hi))}')

# F2-arb: proj y mono on ARBITRARY wf3 pairs (collect wf3 terms = nrm of random terms)
# build a pool of wf3 terms from nrm of all subterm translates (broader class)
wf3pool=set()
for M in list(extra)[:40000]:
    M=list(M)
    if not M: continue
    nB=nrm(conv(translate(M)))
    wf3pool.add(nB)
    # also subterms
wf3pool=list(wf3pool)
random.shuffle(wf3pool)
wf3pool=wf3pool[:1500]
# test proj y for y in 0,1,2 on arbitrary wf3 pairs
tot2=rev2=0; exR2=[]
for y in (0,1,2):
    sub=random.sample(wf3pool, min(700,len(wf3pool)))
    for p,q in itertools.combinations(sub,2):
        if lt_term(p,q): lo,hi=p,q
        elif lt_term(q,p): lo,hi=q,p
        else: continue
        tot2+=1
        pl,ph=proj(y,lo),proj(y,hi)
        if lt_term(ph,pl):
            rev2+=1
            if len(exR2)<6: exR2.append((y,lo,hi))
    if rev2: break
print(f'F2-arb proj y mono on ARBITRARY wf3 (y in 0,1,2): pairs={tot2} rev={rev2}')
for y,lo,hi in exR2[:6]:
    print(f'   REV y={y}: {fmtb(lo)} <o {fmtb(hi)} -> {fmtb(proj(y,lo))} vs {fmtb(proj(y,hi))}')

# Characterize: for the D2 class, what is special about (lo,hi) vs y?
# hypothesis: every TOP subscript of the nrm-image >= 1 (since arg zone starts at row1, head sub = v>=1?)
# actually after proj y the leading princ can drop. but BEFORE proj: nrm-image top subs?
badtop=0; tt=0
for y,S in byY_nrm.items():
    for nB in S:
        tt+=1
        ts=topsubs(nB)
        if ts and min(ts)<1:  # any top subscript 0
            badtop+=1
print(f'class-check: nrm-images with a TOP subscript ==0 : {badtop}/{tt}  (if 0 => all top subs>=1)')
print('DONE')
