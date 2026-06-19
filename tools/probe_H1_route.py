# H1 via IHn(eta) [psiSelf delta u = psiSelf eta u, delta=proj_u eta u-canonical] +
#   need psiSelf(psiSelf eta w) u = psiSelf delta u.
# Route for psiSelf c u = psiSelf delta u (c=psiSelf eta w): 
#   gap (delta, c] all u-non-canon (884/884) + delta u-canonical + delta<=c.
#   => psiSelf c u = psiSelf delta u via collapseSelf_le-on-(delta,c].
# The Lean lemma: "delta u-canonical, delta<=x, every g in (delta,x] u-non-canon => 
#    psiSelf x u = psiSelf delta u".  Proof: collapseSelf_le gives psiSelf (delta+1?) ...
# Actually collapseSelf_le alpha beta needs [alpha,beta) non-canon. Take alpha=delta: 
#   [delta, c) — delta canonical, FAILS. 
# BUT: we don't need to start at delta. psiSelf delta u: delta u-canonical means
#   psiSelf delta u FIRES, is in CsetSelf(delta+1). Hmm.
# CLEANER: psiSelf x u = psiSelf delta u for x with (delta,x] non-canon: 
#   = collapseSelf_le x (delta) needs [delta,x) non-canon (delta IS canon - fails by 1 point).
#   Workaround: collapseSelf_le x (delta+1)? psiSelf(delta+1)u vs psiSelf delta u: 
#     delta u-canonical so delta IN CsetSelf(delta) u, collapseSelf_succ needs delta NOT in
#     => psiSelf delta u != psiSelf(delta+1) u possibly. Hmm.
# Let me test the EXACT identity we can get: is psiSelf c u = psiSelf delta u, AND separately
#   is psiSelf c u = psiSelf eta u DIRECTLY via collapseSelf_le on a gap that IS clean from
#   a NON-canonical bottom? The bottom should be a u-NON-canonical point. Both eta, c are
#   u-non-canon. min(eta,c) is u-non-canon. The gap [min,max) had canonical interior (511/884).
#   So NOT directly. 
# The rep route: psiSelf eta u = psiSelf delta u (IHn) and psiSelf c u = psiSelf delta u (need).
# For psiSelf c u = psiSelf delta u: c u-non-canon, proj_u c = delta. This is psi_proj at c.
# Is psi_proj at c = IHn at c? c at rank? Test if c reachable at rank<=n is NOT needed:
#   instead, c = psiSelf eta w. Maybe psi_proj at c follows from IHn(eta) via w-subscript.
# DECISIVE simpler test: does H1 follow from JUST "psiSelf c u = psiSelf eta u" provable by
#   collapseSelf_le on the gap (delta, max(eta,c)] with BOTH endpoints reached from delta?
#   i.e. psiSelf eta u = psiSelf delta u (IHn) and we PROVE psiSelf c u = psiSelf delta u by
#   collapseSelf_le c delta_plus... 
# Just confirm the rep identity for c is the clean target and move to Lean with a
#   "gap-above-rep collapse" lemma. Verify: delta u-canonical, delta < c, (delta,c] u-non-canon
#   => psiSelf c u = psiSelf delta u. (the lemma to build). Count holds:
import sys
sys.path.insert(0,'.')
from valnorm import conv, nrm, lt_term, G, in_OT
from wfe_explore import translate, enum_ST
Z=()
def cn(x): return tuple(('D',vv,cn(bb)) for _,vv,bb in x)
def le_t(a,b): return a==b or lt_term(a,b)
def acanon(u,t): return not any(not lt_term(x,t) for x in G(u,t))
def princ_in(alpha,v,p):
    _,uu,xi=p
    if uu<v: return True
    if not lt_term(xi,alpha): return False
    if not acanon(uu,xi): return False
    return term_in(alpha,v,xi)
def term_in(alpha,v,delta):
    if delta==Z: return True
    return all(princ_in(alpha,v,p) for p in delta)
def selfcanon(u,t): return term_in(t,u,t)
def psi(a,arg): return cn(nrm((('D',a,arg),)))
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
def collect(r):
    s=set()
    for M in enum_ST(rounds=r):
        t=conv(translate(M)); st=[t]
        while st:
            x=st.pop()
            if not x: continue
            for (_,_,arg) in x: st.append(arg)
            s.add(x)
    return s
for r in (6,7):
    terms=[cn(t) for t in collect(r) if in_OT(t)]; pool=terms
    seen=set(); n=0; lemA=0  # for x=eta: (delta,eta] non-canon & psiSelf eta u=psiSelf delta u
    lemC=0  # for x=c
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)
            for u in range(0,w+1):
                if selfcanon(u,eta): continue
                if selfcanon(u,pw): continue
                key=(str(eta),w,u)
                if key in seen: continue
                seen.add(key); n+=1
                c=pw; d=cn(proj(u,eta))
                # lemma 'gap-above-rep' for eta and for c (the value-identity each = psiSelf delta u)
                if psi(u,eta)==psi(u,d): lemA+=1
                if psi(u,c)==psi(u,d): lemC+=1
    print(f"rounds={r}: inst={n}  psiSelf eta u==psiSelf delta u={lemA}/{n}  psiSelf c u==psiSelf delta u={lemC}/{n}")
