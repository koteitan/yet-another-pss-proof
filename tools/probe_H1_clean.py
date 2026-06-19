# H1: psiSelf eta u = psiSelf c u, c=psiSelf eta w, w>=u, eta&c both u-non-canonical.
# delta=proj_u eta=proj_u c (884/884). 
# psiSelf eta u = psiSelf delta u (psi_proj at eta, via IHn(eta) - eta at rank n). GREEN-able.
# psiSelf c u = psiSelf delta u (psi_proj at c). Need this too. Is it from IHn? c at which rank?
# CLEANER IDEA: H1 directly. psiSelf eta u = psiSelf c u. Both eta, c u-non-canonical, SAME rep
# delta. The collapse psiSelf eta u = psiSelf delta u AND psiSelf c u = psiSelf delta u both via
# the SAME mechanism (rep value-identity). If BOTH come from IHn (eta) and ... need c's rep too.
# 
# THE actual clean lemma: for u-non-canonical x with proj_u x = delta (u-canonical),
#   psiSelf x u = psiSelf delta u. This is psi_proj-at-x. For eta: IHn(eta). For c: need IH at c.
# Since proj_u eta = proj_u c = delta, and psiSelf delta u is u-canonical's value:
#   H1 <=> psiSelf eta u = psiSelf c u <=> (both = psiSelf delta u). 
# So H1 needs psi_proj at BOTH eta and c. eta: IHn (rank n). c=psiSelf eta w: rank n+1 (current).
# Does psi_proj at c follow from psi_proj at eta + something? c=psiSelf eta w. 
# Test the DIRECT collapse for H1 via collapseSelf_le_valuebounded with the CORRECT endpoints:
#   We want psiSelf eta u = psiSelf c u. WLOG via delta: BOTH equal psiSelf delta u.
#   psiSelf eta u = psiSelf delta u: collapse [eta,delta] (eta<=delta? since delta=proj_u eta>=eta?)
#   value-bound: gamma in [eta,delta) canon => psiSelf gamma u < psiSelf eta u. gamma>=eta...
#   strict_mono(gamma vs delta) gives <psiSelf delta u. Circular vs psiSelf eta u again.
# CONCLUSION: H1/psi_proj-at-x is the SAME circular value-identity. It's the IH content.
# The ONLY non-circular supply is IHn(eta) for eta's rep. For c, need its rep via recursion.
# TEST: is c reachable at rank <= n (so IHn gives c's rep too)? c=psiSelf eta w, eta at rank n.
# c is a generator FROM eta (rank n) => c at rank n+1. NOT <= n. So IHn does NOT give c's rep.
# Print c's minimal rank empirically is impossible here; instead test the KEY shortcut:
#   psiSelf c u = psiSelf eta u DIRECTLY as a w-vs-u subscript fact (c=psiSelf eta w):
#   maybe psiSelf(psiSelf eta w) u = psiSelf eta u is a SUBSCRIPT-COMPOSITION identity
#   provable from eta u-noncanon + w>=u WITHOUT per-gap reasoning. 
# Already H1=884/884 true. The Q is its PROOF. Test if it = collapseSelf_le (NON-value-bounded,
# i.e. gap [?] ALL u-non-canonical) for the RIGHT endpoints — maybe [eta, delta] gap is clean?
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
    seen=set(); n=0
    eta_le_d=0; gap_ed_clean=0; gap_cd_clean=0
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
                if le_t(eta,d): eta_le_d+=1
                # gap [eta,d) all u-non-canonical? (collapseSelf_le clean, no value-bound)
                ged=[g for g in pool if le_t(eta,g) and lt_term(g,d) and selfcanon(u,g)]
                if not ged: gap_ed_clean+=1
                # gap [c,d) all u-non-canonical?
                gcd=[g for g in pool if le_t(c,g) and lt_term(g,d) and selfcanon(u,g)]
                if not gcd: gap_cd_clean+=1
    print(f"rounds={r}: inst={n}  eta<=d={eta_le_d}")
    print(f"  gap [eta,delta) ALL u-non-canon (collapseSelf_le clean) = {gap_ed_clean}/{n}")
    print(f"  gap [c,delta)   ALL u-non-canon (collapseSelf_le clean) = {gap_cd_clean}/{n}")
