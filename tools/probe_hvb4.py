# Is hVB derivable WITHOUT crux, via: gap u-canon gamma has psiSelf gamma u < psiSelf c u
# because gamma < c in TRUE ordinal order (then strict_mono(gamma<c, gamma canon) FREE)?
# TRUE order proxy: for canonical a,b, a<b (true) <=> psiSelf a u < psiSelf b u (strict_mono,
# both subscripts). But gamma canonical, c=psiSelf eta w NOT canonical at u. So compare
# via VALUES: gamma < c (true) is hard to proxy. Use the nrm VALUE order which IS faithful
# (unlike lt_term at Omega-crossings): define true_lt(a,b) by comparing as ORDINALS.
# The nrm normal form's lt on FULLY NORMALIZED canonical terms = value order. Both gamma
# (canon) and c (a psiSelf value) are canonical-rep terms. Compare nrm(gamma) vs nrm(c)?
# Actually the cleanest faithful value comparison: psiSelf at a HIGH subscript that doesn't
# collapse. But simplest: just test whether psiSelf gamma u < psiSelf c u follows from
# psiSelf gamma w' < psiSelf c w' at a non-collapsing subscript... too complex.
#
# DIRECT TEST of the recursion claim: hVB(eta) for gap-canon gamma<eta. Each such gamma,
# being u-CANONICAL and < eta, would (at ITS OWN level as a bound) have been processed.
# The value psiSelf gamma u: is it < psiSelf c u BECAUSE psiSelf gamma u <= psiSelf gamma' u
# for the LARGEST u-canonical gamma' < c? i.e. is c's "u-floor" (largest canonical below
# whose psiSelf-u value bounds) the key? 
# SIMPLEST decisive: is hVB equivalent to "c is u-non-canonical AND the rep of c at u is
# >= eta"? We know (last turn) the minimal canonical realizer of psiSelf c u is... let me
# just check: does psiSelf c u = psiSelf eta u mean c and eta share the u-canonical rep,
# and is that rep = eta (eta u-canonical, the realizer)? If rep(c at u)=eta then every
# canonical gamma<eta has psiSelf gamma u < psiSelf eta u = psiSelf c u = hVB. So hVB <=
# "rep_u(psiSelf c u) = eta" = "eta is the least u-canonical with psiSelf . u = psiSelf c u".
# This is supplied by: eta u-canonical (hyp) + psiSelf eta u = psiSelf c u (crux) + 
# injectivity (no smaller canonical realizer). The "no smaller" = strict_mono. So:
#   rep_u(psiSelf c u) = eta  <=>  psiSelf eta u = psiSelf c u (crux) AND eta u-canon.
# STILL needs crux. CONFIRM the realizer is eta (re-test, value-faithful):
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
    seen=set(); n=0; eta_is_min_realizer=0
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)
            for u in range(0,4):
                if not(u<=w and selfcanon(u,eta) and (not selfcanon(u,pw))): continue
                key=(str(eta),w,u)
                if key in seen: continue
                seen.add(key); n+=1
                pcu=psi(u,pw)
                # is eta the MINIMAL u-canonical realizer of pcu in corpus?
                realizers=[g for g in pool if selfcanon(u,g) and psi(u,g)==pcu]
                if realizers:
                    mn=realizers[0]
                    for g in realizers[1:]:
                        if lt_term(g,mn): mn=g
                    if mn==eta: eta_is_min_realizer+=1
    print(f"rounds={r}: inst={n}  eta is MIN u-canonical realizer of psiSelf c u = {eta_is_min_realizer}/{n}")
