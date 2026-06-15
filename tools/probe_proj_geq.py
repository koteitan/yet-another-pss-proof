#!/usr/bin/env python3
"""DEFINITIVE soundness gate for the PROJ factor:

  PROJMONO_GEQ:  wf3 p, wf3 q,  all subscripts of p and of q are >= y,
                 olt p q   ==>   olt (proj y p) (proj y q).

This is the clean half of proj_nrm_argzone_olt:
  arg-zone images nB satisfy subs(nB) <= {v : y<=v}  (NT_subs + IST: arg vals>=y),
  so they all live in this >=y fragment.
We build a LARGE wf3 pool (nrm of subterms) + inject hard families, then for
each y test proj-mono ONLY on the >=y fragment.  Deep +5.  0 reversals required.
"""
import sys, itertools, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(2024)
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

def allsubs(t):
    out=[]
    for p in t:
        out.append(p[1]); out+=allsubs(p[2])
    return out
def minsub(t):
    s=allsubs(t); return min(s) if s else 10**9
def subterms(t):
    out=set()
    def rec(s):
        out.add(s)
        for p in s: rec(p[2])
        for i in range(1,len(s)+1): out.add(s[i:])
    rec(t); return out

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

exl=list(extra); random.shuffle(exl)
wf3=set()
for M in exl[:55000]:
    c=conv(translate(list(M)))
    for s in subterms(c):
        wf3.add(nrm(s))
        if len(wf3)>320000: break
    if len(wf3)>320000: break
# inject hard families (all subs shifted so they live in various >=y fragments)
D=lambda v,x:('D',v,x); T=lambda *ps:tuple(ps)
y0=T(D(1,())); yk=y0; fam=[y0]
for _ in range(6):
    yk=T(D(0,T(D(1,yk)))); fam.append(yk)
# also shift-up copies: wrap so min-subscript is high
for f in list(fam):
    fam.append(T(D(2,f))); fam.append(T(D(3,f)))
for f in fam: wf3.add(nrm(f))
print('wf3 pool size=',len(wf3),flush=True)

# precompute minsub
wf3=list(wf3); random.shuffle(wf3)
pool=[(t, minsub(t)) for t in wf3[:1400]]

tot=rev=coll=0; ex=[]
for y in range(0,7):
    frag=[t for (t,ms) in pool if ms>=y]   # all subscripts >= y
    for p,q in itertools.combinations(frag,2):
        if lt_term(p,q): lo,hi=p,q
        elif lt_term(q,p): lo,hi=q,p
        else: continue
        tot+=1
        pl,ph=proj(y,lo),proj(y,hi)
        if lt_term(ph,pl):
            rev+=1
            if len(ex)<10: ex.append((y,lo,hi))
        elif pl==ph: coll+=1
    print(f'  y={y}: frag={len(frag)} cumulative pairs={tot} rev={rev} coll={coll}',flush=True)
print(f'PROJMONO_GEQ (y=0..6): pairs={tot} reversals={rev} collapses={coll}')
for y,lo,hi in ex[:10]:
    print(f'   REV y={y}: {fmtb(lo)} <o {fmtb(hi)} -> {fmtb(proj(y,lo))} vs {fmtb(proj(y,hi))}')
print('DONE')
