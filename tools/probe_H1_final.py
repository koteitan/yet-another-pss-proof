# H1 <=> psiSelf eta u = psiSelf c u, c=psiSelf eta w. Both u-non-canonical, same rep delta.
# CLEAN reduction: H1 follows from "psiSelf_proj_u: x u-non-canonical => psiSelf x u =
#   psiSelf (proj_u x) u" applied to BOTH eta and c (same delta=proj_u eta=proj_u c).
#   => psiSelf eta u = psiSelf delta u = psiSelf c u.
# psiSelf_proj_u at eta = IHn(eta) [GREEN, rank n]. At c = the residual.
# But ALTERNATIVELY: H1 might follow from IHn(eta) ALONE if we can show psiSelf c u =
#   psiSelf eta u via a SUBSCRIPT identity not needing c's rep. Test the subscript structure:
#   c = psiSelf eta w. psiSelf(psiSelf eta w) u. Is there a Buchholz subscript-composition
#   law psiSelf(psiSelf eta w) u = psiSelf eta u when eta u-non-canon & u<=w? 
# Test the KEY enabling fact for a DIRECT proof: is psiSelf eta w 's u-rep = eta's u-rep
#   because psiSelf eta w is "between" eta's rep delta and ... Let me test the cleanest
#   sufficient lemma that's NON-circular:
#   LEM: x u-non-canonical, proj_u x = delta => the gap (delta, x] modulo... 
# Actually test: does H1 follow from collapseSelf_le (PLAIN, non-value-bounded) on gap
#   (delta, max(eta,c)]? i.e. is EVERY ordinal in (delta, max(eta,c)] u-non-canonical?
#   (delta is the rep, everything strictly above delta up to eta/c is non-canonical = the
#   plateau above the rep). TEST gap (delta, eta] and (delta, c] all u-non-canonical:
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
    # gap (delta, eta] : ordinals g with delta < g <= eta, all u-non-canonical?
    ge_clean=0; gc_clean=0
    # value-bounded variant: gap (delta,eta] canonical g => psiSelf g u < psiSelf delta u? (g>delta canon)
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
                # gap (d, eta]
                ge=[g for g in pool if lt_term(d,g) and le_t(g,eta) and selfcanon(u,g)]
                if not ge: ge_clean+=1
                gc=[g for g in pool if lt_term(d,g) and le_t(g,c) and selfcanon(u,g)]
                if not gc: gc_clean+=1
    print(f"rounds={r}: inst={n}")
    print(f"  gap (delta,eta] ALL u-non-canon = {ge_clean}/{n}")
    print(f"  gap (delta,c]   ALL u-non-canon = {gc_clean}/{n}")
