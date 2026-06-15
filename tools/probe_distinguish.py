#!/usr/bin/env python3
"""Distinguish arg-zone nrm-images (proj y mono OK) from the GEQ counterexamples.
The reversal mechanism: lo has a G_y-critical subterm g with g >o lo, so
proj y lo jumps UP to g. Test predicates that the arg-zone class satisfies
but the counterexample lo=D0(D1(...)) violates:

  P_canon(y,t): every g in G_y(t) has olt g t   (== proj y t = t, t already y-canonical / no fire)
  P_leadfire:   if proj y t fires, lead(proj y t) == lead(t)? (proj preserves leading sub)
  P_subdom:     for every g in G_y(t), lead(g) <= lead(t)  (no arg has higher leading sub than host)
We measure each on arg-zone images AND on the wf3 GEQ pool, and check whether
ANY predicate is (i) 100% on arg-zone images and (ii) makes proj-mono hold when
imposed on the wf3 pool.
"""
import sys, itertools, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(9)
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
def lead(t): return t[0][1] if t else -1
def takeW(r):
    out=[]
    for p in r:
        if p[0]>0: out.append(p)
        else: break
    return out
def subterms(t):
    out=set()
    def rec(s):
        out.add(s)
        for p in s: rec(p[2])
        for i in range(1,len(s)+1): out.add(s[i:])
    rec(t); return out

def P_canon(y,t): return all(lt_term(g,t) for g in G(y,t))     # proj y t == t
def P_subdom(y,t): return all(lead(g)<=lead(t) for g in G(y,t)) # no critical has higher lead

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

# arg-zone images grouped by y
from collections import defaultdict
byY=defaultdict(set)
for M in extra:
    M=list(M)
    if not M or M[0][0]!=0: continue
    y=M[0][1]; aM=tuple(takeW(M[1:]))
    if aM: byY[y].add(nrm(conv(translate(list(aM)))))

# measure predicates on arg-zone images
canon=subdom=tot=0
for y,S in byY.items():
    for nB in S:
        tot+=1
        if P_canon(y,nB): canon+=1
        if P_subdom(y,nB): subdom+=1
print(f'arg-zone images total={tot}')
print(f'  P_canon (proj y nB==nB / y-canonical): {canon}/{tot}')
print(f'  P_subdom(no G_y-critical has higher lead): {subdom}/{tot}',flush=True)

# Now: impose P_subdom on a wf3 pool and re-test proj-mono
exl=list(extra); random.shuffle(exl)
wf3=set()
for M in exl[:45000]:
    c=conv(translate(list(M)))
    for s in subterms(c):
        wf3.add(nrm(s))
        if len(wf3)>200000: break
    if len(wf3)>200000: break
wf3=list(wf3); random.shuffle(wf3); wf3=wf3[:1200]
for predname,pred in [('P_subdom',P_subdom),('P_canon',P_canon)]:
    tot2=rev=coll=0; ex=[]
    for y in range(0,6):
        frag=[t for t in wf3 if pred(y,t)]
        for p,q in itertools.combinations(frag,2):
            if lt_term(p,q): lo,hi=p,q
            elif lt_term(q,p): lo,hi=q,p
            else: continue
            tot2+=1
            pl,ph=proj(y,lo),proj(y,hi)
            if lt_term(ph,pl): rev+=1; ex.append((y,lo,hi)) if len(ex)<4 else None
            elif pl==ph: coll+=1
    print(f'[impose {predname}] pairs={tot2} rev={rev} coll={coll}',flush=True)
    for y,lo,hi in ex[:3]:
        print(f'   REV y={y}: {fmtb(lo)} <o {fmtb(hi)} -> {fmtb(proj(y,lo))} vs {fmtb(proj(y,hi))}')
print('DONE')
