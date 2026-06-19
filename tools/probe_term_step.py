# TERM-level single maxo-step via tsize. x a TERM (in OT), g=maxo{u-violators in G_u(x)},
# g a SUBTERM (tsize smaller), g u-canonical. Want psiSelf(x) u = psiSelf(g) u [values via nrm].
# NoRealizer needs: no canonical xi<g with psiSelf xi u = psiSelf x u. On TERMS, can this
# follow from the G_u/maxo structure + IH(subterms)?
# Test the term-structural fact that could supply NoRealizer non-circularly:
#  the value psiSelf x u — is its canonical realizer FORCED to be >= g because every
#  coefficient of x below g is < x (so can't realize the value that needs the g-coefficient)?
# Concretely (Buchholz 1.9 necessity for terms = term_nec, ya-pss GREEN): if a canonical xi
#  realizes psiSelf x u and xi<g, then xi's G_u-coefficients are all < g (necessity), but
#  x has the coefficient g (maxo) with oV g >= oV x... 
# Simplest decisive term-test: among canonical TERMS xi with psiSelf(oV xi) u = psiSelf(oV x) u,
#  is the MINIMAL one = g (the maxo subterm)? AND is "xi<g => not realizes" because xi lacks
#  the g-coefficient? Test minimal canonical-term realizer == g:
import sys
sys.path.insert(0,'.')
from valnorm import conv, nrm, lt_term, G, in_OT
from wfe_explore import translate, enum_ST
Z=()
def cn(x): return tuple(('D',vv,cn(bb)) for _,vv,bb in x)
def le_t(a,b): return a==b or lt_term(a,b)
def acanon(u,t): return not any(not lt_term(x,t) for x in G(u,t))
def psi(a,arg): return cn(nrm((('D',a,arg),)))
def maxo(lst):
    m=lst[0]
    for h in lst[1:]:
        if lt_term(m,h): m=h
    return m
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
    terms=[cn(t) for t in collect(r) if in_OT(t)]; pool=[t for t in terms]
    seen=set(); n=0; min_real_eq_g=0; step_holds=0
    for x in terms:
        for u in range(0,4):
            bad=[gg for gg in G(u,x) if not lt_term(gg,x)]
            if not bad: continue
            g=cn(maxo([cn(b) for b in bad])); px=psi(u,x)
            key=(str(x),u)
            if key in seen: continue
            seen.add(key); n+=1
            if px==psi(u,g): step_holds+=1
            # minimal canonical-TERM realizer of px (term order)
            R=[xi for xi in pool if acanon(u,xi) and psi(u,xi)==px]
            if R:
                mn=R[0]
                for xi in R[1:]:
                    if lt_term(xi,mn): mn=xi
                if mn==g: min_real_eq_g+=1
    print(f"rounds={r}: term maxo-step inst={n}")
    print(f"  step psiSelf(oV x)u==psiSelf(oV g)u = {step_holds}/{n}")
    print(f"  minimal canonical-term realizer of psiSelf x u == g (maxo subterm) = {min_real_eq_g}/{n}")
