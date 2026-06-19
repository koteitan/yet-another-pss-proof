#!/usr/bin/env python3
"""DECISIVE probe 4: is 'no a-canonical witness < oV g' derivable from
g-canonical + maxo + B2, WITHOUT the value identity oV(proj a b')=oV g (psi_proj)?

The contradiction needs:  membership psi_a(oVb') in C_a(oVg)  =>  exists a-canonical
delta < oV g with psi_a(delta)=psi_a(oVb').  We must REFUTE the existence of such delta.

Two candidate refutations:
 (R-circ) the canonical rep of oV b' = oV g (value identity = psi_proj). Then any
   canonical realizer delta has psi_a(delta)=psi_a(oVb')=psi_a(oVg), and by
   psi_canonical_inj (delta, g both canonical) delta=oV g, NOT <oV g. Uses psi_proj.

 (R-band) WITHOUT value identity: g is a-canonical (maxo, proj a g=g) and g is the
   maxo violator. Claim: psi_a(oV g) is the LEAST value of psi_a on a-canonical args
   that is >= psi_a(oV b'). i.e. for every a-canonical delta < oV g, psi_a(delta) <
   psi_a(oV b') STRICTLY (so cannot equal). TEST THIS:
     for all a-canonical delta with delta < oV g:  psi_a(delta) < psi_a(oV b') ?
   If 0-viol, the refutation is a STRICT-MONOTONICITY / band fact:
     'psi_a is strictly below psi_a(oVb') on all canonical args below oV g',
   which would follow from psi_strict_mono (canonical args) + 'oV g is the least
   canonical arg with psi_a >= psi_a(oV b')'. The last clause is still rep-flavoured
   but as an INEQUALITY (psi_a(oVg) >= psi_a(oVb')) not an EQUALITY.

 THE real escape test (R-maxo): does
     psi_a(oV g) >= psi_a(oV b')   [INEQUALITY, from B1 oVb'<=oVg + psi_mono, FREE]
   COMBINED WITH  psi_a strict-mono-canonical below oV g
   suffice to refute a canonical realizer < oV g  WITHOUT equality?
   A canonical delta<oV g with psi_a(delta)=psi_a(oVb'): since delta<oV g and BOTH
   would need... we compare psi_a(delta) vs psi_a(oV b'). We know psi_a(delta) <
   psi_a(oV g) IF delta canonical & delta<oV g & oV g... no, oV g canonical so
   psi_strict_mono_arg(delta<oVg, delta canonical) => psi_a(delta)<psi_a(oV g).
   But we need psi_a(delta) vs psi_a(oV b') = the collapse value. Without knowing
   psi_a(oVb')=psi_a(oVg), we can't place psi_a(oV b') relative to psi_a(delta).

   SO test: is it ALWAYS true that  for a-canonical delta<oV g, psi_a(delta) != psi_a(oVb')?
   AND is the WEAKER  psi_a(delta) < psi_a(oV b')  also always true (giving a clean
   strict-mono refutation)?  If psi_a(delta)<psi_a(oVb') for ALL canonical delta<oVg,
   the refutation is: 'oV b' value exceeds every canonical-arg value below oV g',
   which is psi_a(oVb') >= sup{psi_a(delta): delta canonical <oV g}. Compare to
   psi_a(oV g): we'd get psi_a(oVb')<=psi_a(oVg) [B1] and psi_a(oVb')>psi_a(delta)
   for delta<oVg canonical. That PINS psi_a(oVb') into [psi_a(oVg^-), psi_a(oVg)]
   = the plateau, forcing =psi_a(oVg). That IS psi_proj again (the plateau identity).
"""
import sys
sys.path.insert(0,'.')
from valnorm import conv, nrm, lt_term, G, in_OT
from wfe_explore import translate, enum_ST
Z=()
def cn(x): return tuple(('D',vv,cn(bb)) for _,vv,bb in x)
def maxo(lst):
    m=lst[0]
    for h in lst[1:]:
        if lt_term(m,h): m=h
    return m
def proj(u,t):
    while True:
        bad=[x for x in G(u,t) if not lt_term(x,t)]
        if not bad: return t
        t=maxo(bad)
def acanon(u,t): return not any(not lt_term(x,t) for x in G(u,t))
def psi_a(a,arg): return cn(nrm((('D',a,arg),)))
def collect(rounds):
    terms=set()
    for M in enum_ST(rounds=rounds):
        t=conv(translate(M)); st=[t]
        while st:
            x=st.pop()
            if not x: continue
            for (_,_,arg) in x: st.append(arg)
            terms.add(x)
    return terms

def audit(rounds):
    terms=collect(rounds)
    pool=sorted({cn(t) for t in terms if in_OT(t)}, key=lambda z: (len(str(z)),str(z)))
    seen=set(); inst=0
    # for canonical delta<oVg: psi_a(delta) vs psi_a(oVb')
    all_strict_below=0   # ALL canonical delta<oVg have psi_a(delta)<psi_a(oVb')  (R-band)
    any_eq=0             # SOME canonical delta<oVg has psi_a(delta)=psi_a(oVb')   (escape blocked)
    any_above=0          # SOME canonical delta<oVg has psi_a(delta)>psi_a(oVb')   (R-band fails)
    g_canonical=0
    psig_ge_psib=0       # psi_a(oVg) >= psi_a(oVb')  (free from B1)
    # the maxo-specific: is psi_a(oVb')=psi_a(oVg) EXACTLY (the plateau top)?
    plateau_eq=0
    for b in terms:
        if not in_OT(b): continue
        bc=cn(b)
        for a in range(0,4):
            bad=[x for x in G(a,b) if not lt_term(x,b)]
            if not bad: continue
            g=maxo(bad); gc=cn(g)
            key=(a,str(bc),str(gc))
            if key in seen: continue
            seen.add(key); inst+=1
            pb=psi_a(a,bc); pg=psi_a(a,gc)
            if acanon(a,gc): g_canonical+=1
            if pg==pb or lt_term(pb,pg): psig_ge_psib+=1
            if pb==pg: plateau_eq+=1
            below=[d for d in pool if acanon(a,d) and lt_term(d,gc)]
            sb=True; eq=False; ab=False
            for d in below:
                pd=psi_a(a,d)
                if pd==pb: eq=True; sb=False
                elif lt_term(pb,pd): ab=True; sb=False
            if sb: all_strict_below+=1
            if eq: any_eq+=1
            if ab: any_above+=1
    print(f"rounds={rounds}: instances={inst}")
    print(f"  g a-canonical                                  = {g_canonical}/{inst}")
    print(f"  psi_a(oVg) >= psi_a(oVb') (free B1)            = {psig_ge_psib}/{inst}")
    print(f"  PLATEAU psi_a(oVb')==psi_a(oVg) (= CRM=psiproj)= {plateau_eq}/{inst}")
    print(f"  R-band: ALL canon delta<oVg have psi<psi(oVb')= {all_strict_below}/{inst}")
    print(f"  some canon delta<oVg has psi==psi(oVb') (BLOCK)= {any_eq}/{inst}")
    print(f"  some canon delta<oVg has psi>psi(oVb')         = {any_above}/{inst}")

if __name__=="__main__":
    for r in (5,6,7):
        audit(r); print()
