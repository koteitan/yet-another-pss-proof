# Can hVB be supplied by the joint IH? The joint induction is OUTER on bound alpha,
# INNER on rank. For subA_nm/crux at (eta,w,u): the gap-canonical gamma satisfy gamma<eta.
# IH at alpha (the OUTER bound in noncanonValueMem_joint) is at SMALLER alpha. But here
# the relevant 'bound' is eta itself. hVB quantifies gamma<eta -- so an induction on eta
# (the GENERATOR ARGUMENT, which is <alpha in the joint induction) would give hVB from
# IH at gamma<eta. TEST the recursive structure: for u-canon gamma in [c,eta), is
# psiSelf gamma u < psiSelf c u DERIVABLE from the SAME crux at gamma's level, i.e. is
# this a well-founded recursion on eta?
# Concretely: hVB(eta) := all u-canon gamma in [psiSelf eta w, eta): psiSelf gamma u <
#   psiSelf(psiSelf eta w) u. Does hVB(eta) follow from {crux(eta') : eta'<eta}?
# The crux(eta): psiSelf(psiSelf eta w) u = psiSelf eta u. Given crux for all eta'<eta,
#   for gamma in gap (gamma<eta, u-canon): psiSelf gamma u < psiSelf eta u (strict_mono).
#   Need < psiSelf c u = psiSelf(psiSelf eta w) u. With crux(eta) itself: = psiSelf eta u.
#   So hVB(eta) <=> [psiSelf gamma u < psiSelf eta u] which is strict_mono = FREE, GIVEN
#   crux(eta) rewrites psiSelf c u to psiSelf eta u. But crux(eta) is what we're proving!
# RESOLUTION: prove crux(eta) and hVB(eta) SIMULTANEOUSLY by induction on eta:
#   to prove crux(eta) [= collapse via value-bound hVB(eta)], hVB(eta) needs psiSelf gamma u
#   < psiSelf c u; with strict_mono psiSelf gamma u < psiSelf eta u, suffices psiSelf eta u
#   <= psiSelf c u. BUT that's the >= half of crux(eta) -- circular WITHIN eta.
# So simultaneity on eta does NOT break it (the >= is needed AT eta, not below).
# THE ACTUAL Buchholz break: the value-bound comes from gamma being u-canonical AND
#   gamma < c in TRUE order (not term order). Test: among gap-canon gamma, the TRUE
#   ordinal order via psiSelf-INJECTIVITY proxy: gamma canon, c... is psiSelf gamma u
#   < psiSelf c u because gamma is genuinely a SMALLER canonical than the rep of c?
# Test: is psiSelf gamma u always = psiSelf (something) with that something < c-rep?
# Simpler decisive: count gap-canon gamma and whether psiSelf gamma u < psiSelf eta u
#   (strict_mono, FREE) ALWAYS holds (sanity: yes since gamma<eta canon). Then hVB needs
#   only crux. So the WHOLE subA_nm = crux = a SINGLE value-identity, supplied by caseB/IH.
import sys
sys.path.insert(0,'.')
from valnorm import conv, nrm, lt_term, G, in_OT
from wfe_explore import translate, enum_ST
Z=()
def cn(x): return tuple(('D',vv,cn(bb)) for _,vv,bb in x)
def le_t(a,b): return a==b or lt_term(a,b)
def acanon(u,t): return not any(not lt_term(x,t) for x in G(u,t))
def princ_in(alpha,v,p):
    _,u,xi=p
    if u<v: return True
    if not lt_term(xi,alpha): return False
    if not acanon(u,xi): return False
    return term_in(alpha,v,xi)
def term_in(alpha,v,delta):
    if delta==Z: return True
    return all(princ_in(alpha,v,p) for p in delta)
def psi(a,arg): return cn(nrm((('D',a,arg),)))
def selfcanon(u,t): return term_in(t,u,t)
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
for r in (7,):
    terms=[cn(t) for t in collect(r) if in_OT(t)]; pool=terms
    seen=set(); n=0; sm_free=0; tot=0
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)
            for u in range(0,4):
                if not(u<=w and selfcanon(u,eta) and (not selfcanon(u,pw))): continue
                key=(str(eta),w,u)
                if key in seen: continue
                seen.add(key); n+=1
                peu=psi(u,eta)
                gam=[g for g in pool if le_t(pw,g) and lt_term(g,eta) and selfcanon(u,g)]
                for g in gam:
                    tot+=1
                    if lt_term(psi(u,g),peu): sm_free+=1   # strict_mono to eta (FREE)
    print(f"rounds={r}: inst={n}  gap-canon total={tot}  psiSelf gamma u < psiSelf eta u (strict_mono, FREE)={sm_free}/{tot}")
