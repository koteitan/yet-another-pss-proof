#!/usr/bin/env python3
"""SHARP test of the clean factor:

  PROJMONO_WF3:  wf3 p, wf3 q, olt p q  ==>  olt (proj y p) (proj y q)
                 for ALL y (0..maxsub+1).   [proj y is olt-monotone on wf3]

If TRUE, the arg-zone core factors as:
   nrm-mono-on-NF (the hard half)  THEN  proj-mono-on-wf3 (this clean half).
We build a LARGE wf3 pool from many sources and inject hard families
(y-tower, p0p1 wrappers, nrm of everything). Deep +5.
Also separately test the SECOND factor:
  NRMMONO_ARG: arg-zone translates  olt B F  ==> olt (nrm B)(nrm F)  (already D1=0)
"""
import sys, itertools, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(101)
from wfe_explore import translate, enum_ST
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

def subterms(t):
    out=set()
    def rec(s):
        out.add(s)
        for p in s:
            rec(p[2])
        for i in range(1,len(s)+1):
            out.add(s[i:])
    rec(t); return out

def maxsub_c(t):
    m=0
    for p in t:
        m=max(m,p[1],maxsub_c(p[2]))
    return m

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

# Build a big WF3 pool: nrm of subterms of a SAMPLE of translates,
# plus nrm of hard injected families.
wf3=set()
exl=list(extra)
random.shuffle(exl)
terms=[conv(translate(list(M))) for M in exl[:60000]]
for c in terms:
    for s in subterms(c):
        wf3.add(nrm(s))
        if len(wf3)>400000: break
    if len(wf3)>400000: break
# inject hard families then normalize
D=lambda v,x:('D',v,x); T=lambda *ps:tuple(ps)
y0=T(D(1,())); yk=y0; fam=[y0]
for _ in range(6):
    yk=T(D(0,T(D(1,yk)))); fam.append(yk)
for f in list(fam):
    fam.append(T(D(0,T(D(1,f)))))
    fam.append(T(D(2,f)))
for f in fam: wf3.add(nrm(f))
# sanity: all wf3?
nonwf=[t for t in list(wf3)[:5000] if not in_OT(t)]
print('wf3 pool size=',len(wf3),' non-OT in sample:',len(nonwf))

wf3=list(wf3)
random.shuffle(wf3)
# group: test proj y for y in 0..6 on the whole pool (sampled), all y
cap=900
sub=wf3[:cap]
tot=rev=coll=0; exR=[]
ymax=6
for y in range(0,ymax+1):
    for p,q in itertools.combinations(sub,2):
        if lt_term(p,q): lo,hi=p,q
        elif lt_term(q,p): lo,hi=q,p
        else: continue
        tot+=1
        pl,ph=proj(y,lo),proj(y,hi)
        if lt_term(ph,pl):
            rev+=1
            if len(exR)<8: exR.append((y,lo,hi))
        elif pl==ph:
            coll+=1
print(f'PROJMONO_WF3 (y=0..{ymax}): pairs={tot} reversals={rev} collapses={coll}')
for y,lo,hi in exR[:8]:
    print(f'   REV y={y}: {fmtb(lo)} <o {fmtb(hi)} -> {fmtb(proj(y,lo))} vs {fmtb(proj(y,hi))}')
print('DONE')
