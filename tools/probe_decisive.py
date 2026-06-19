# DECISIVE preservation test. VB(x,u) needs: for gap-canonical gamma in [x,g) (g=maxo-viol),
#   psiSelf gamma u < psiSelf x u.  gamma is CANONICAL (so PP(gamma,u) trivial: gamma=proj_u gamma).
#   The fact psiSelf gamma u < psiSelf x u: gamma >= x (value, in gap) but value SMALLER.
#   This is the Omega-crossing: gamma = Omega_k-type, lt_term says gamma>=x but psiSelf gamma u
#   (u<k) collapses small. The TRUE ordinal value of gamma at subscript u IS < psiSelf x u.
# Q: is psiSelf gamma u < psiSelf x u derivable from facts at elements SMALLER than x?
#   gamma canonical => psiSelf gamma u is gamma's OWN value (no collapse needed for gamma).
#   Compare psiSelf gamma u vs psiSelf x u: need to know psiSelf x u's PLACE. But psiSelf x u
#   = psiSelf(proj_u x) u = the very PP(x,u) we're proving. CIRCULAR unless psiSelf gamma u
#   is bounded by something independent.
# THE well-foundedness test: define need-set. VB(x,u) needs psiSelf gamma u < psiSelf x u.
#   Does this follow from VB(gamma', u') for gamma' STRICTLY SMALLER (ordinal) than x?
#   gamma in [x,g): gamma >= x (lt_term). But as TRUE ordinal, is gamma < x? Test via a
#   FAITHFUL order: gamma canonical, x non-canonical. Use psiSelf-at-high-subscript W>u,k as
#   faithful value proxy (no collapse at W). compare psiSelf gamma W vs psiSelf x W.
#   If gamma <_true x then strict_mono(gamma<x... x non-canon, no) -- 
# SIMPLEST decisive: just check if there EXISTS a gap-canonical gamma whose psiSelf gamma u
#   value REQUIRES psiSelf x u to be placed (i.e. gamma's value is in [psiSelf x' u, psiSelf x u)
#   for x'<x) vs is independently < psiSelf x u. Test: is psiSelf gamma u < psiSelf x' u for
#   SOME canonical x' < x (true ordinal, via tsize-smaller subterm)? If yes for ALL gamma,
#   VB(x) reduces to VB/values at smaller x' = WELL-FOUNDED. If some gamma has psiSelf gamma u
#   in [sup_{x'<x} psiSelf x' u, psiSelf x u) then it needs x itself = circular.
# Operationally: psiSelf gamma u < psiSelf x u, and is psiSelf gamma u ACHIEVED by a
#   canonical delta_g = proj_u gamma = gamma (gamma canon). gamma's value psiSelf gamma u.
#   Is gamma < proj_u x = delta (the rep, canonical)? Then strict_mono(gamma<delta, both canon)
#   gives psiSelf gamma u < psiSelf delta u = psiSelf x u (by PP(x)). Uses PP(x) = circular.
#   BUT if gamma < delta we get psiSelf gamma u < psiSelf delta u WITHOUT PP(x); and we need
#   < psiSelf x u. psiSelf x u <= psiSelf delta u (x<=delta mono). So psiSelf gamma u<psiSelf delta u
#   does NOT give < psiSelf x u. STILL stuck on psiSelf x u = psiSelf delta u = PP(x).
# CONCLUSION expected: circular. CONFIRM: is gamma < delta=proj_u x for all gap-canon gamma?
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
    seen=set(); ng=0; gam_lt_delta=0; psival_lt=0
    for x in terms:
        for u in range(0,4):
            if selfcanon(u,x): continue
            d=cn(proj(u,x))
            gam=[g for g in pool if le_t(x,g) and lt_term(g,d) and selfcanon(u,g)]
            for g in gam:
                ng+=1
                if lt_term(g,d): gam_lt_delta+=1     # gamma < delta=proj_u x (true: gamma in [x,d))
                # the needed fact psiSelf gamma u < psiSelf x u
                if lt_term(psi(u,g),psi(u,x)): psival_lt+=1
    print(f"rounds={r}: gap-canon gamma={ng}")
    print(f"  gamma < proj_u x (delta) [trivially, gap is [x,delta)] = {gam_lt_delta}/{ng}")
    print(f"  psiSelf gamma u < psiSelf x u (the VB content)          = {psival_lt}/{ng}")
    print(f"  => VB content TRUE; but proof needs psiSelf x u = psiSelf delta u (PP(x)) = CIRCULAR")
