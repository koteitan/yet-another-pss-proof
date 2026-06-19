# MAKE-OR-BREAK: does NoRealizer(x,g,u) follow from term_nec + tsize-IH, non-circularly?
# x = oV(term), u-non-canonical. g = maxo u-violator subterm (= proj_u x in one step,
#   u-canonical). NoRealizer: no canonical xi<g with psiSelf xi u = psiSelf x u.
#
# term_nec (Buchholz 1.9 for terms): wf3 t, oV t in Cset_c(alpha) a => all coeffs of t < alpha.
# How term_nec refutes a realizer: suppose canonical xi<g, psiSelf xi u = psiSelf x u.
#   psiSelf x u as a value = psi_u(oV x). Its canonical realizer... 
# KEY: the PP_step is psiSelf x u = psiSelf g u (g=maxo viol). The collapse means
#   psi_u(oV x) = psi_u(oV g). g is u-canonical so this is the "x collapses to its rep g".
# NoRealizer says g is the LEAST canonical realizer. A realizer xi<g would mean psi_u(oV xi)
#   = psi_u(oV x) = psi_u(oV g), xi & g both canonical => xi=g (injectivity), contra xi<g.
#   BUT that uses psi_u(oV x)=psi_u(oV g) = PP_step = what we prove. CIRCULAR.
# So NoRealizer via injectivity needs PP_step. Does term_nec give NoRealizer WITHOUT PP_step?
#
# The term_nec route to NoRealizer (the ya-pss B2/necessity argument):
#   x is u-NON-canonical (oV x ∉ Cset_c(oV x) u). By contrapositive of term_nec-at-x:
#   x has a coefficient (G_u subterm) g with oV g >= oV x (the violator). 
#   Now suppose realizer xi<g canonical, psi_u(oV xi)=psi_u(oV x). 
#   Apply term_nec to... what term? The realizer xi is canonical: oV xi ∈ Cset_c(oV xi) u.
#   Hmm. Let me test the ACTUAL derivability structure empirically:
# TEST: is there a canonical xi (term) with oV xi < oV g AND psi_u(oV xi)=psi_u(oV x)?
#   (the realizer-below-g, should be NONE = 0). AND crucially: does its NON-existence
#   follow from "every canonical term with value-realizing psi_u(oV x) has a G_u-coeff >= oV x
#   hence (by term_nec at bound oV g) is NOT < oV g"? Test the term_nec-mechanism:
#   for the (nonexistent) realizer, would term_nec at bound oV g be violated?
import sys
sys.path.insert(0,'.')
from valnorm import conv, nrm, lt_term, G, in_OT
from wfe_explore import translate, enum_ST
Z=()
def cn(x): return tuple(('D',vv,cn(bb)) for _,vv,bb in x)
def le_t(a,b): return a==b or lt_term(a,b)
def acanon(u,t): return not any(not lt_term(x,t) for x in G(u,t))
def psi(a,arg): return cn(nrm((('D',a,arg),)))
def tsize(t):
    if t==Z: return 1
    return 1+sum(tsize(b) for _,_,b in t)
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
    terms=[cn(t) for t in collect(r) if in_OT(t)]; pool=terms
    seen=set(); n=0
    realizer_below_g=0
    # the KEY: among canonical terms xi with psi_u(oV xi)=psi_u(oV x), do ALL have
    #   xi NOT < g (term order), AND is the minimal one g itself, AND does the minimal
    #   realizer have SMALLER tsize than x (so IH could reach it)?
    minreal_tsize_lt_x=0; minreal_is_g=0; g_tsize_lt_x=0
    for x in terms:
        for u in range(0,4):
            bad=[gg for gg in G(u,x) if not lt_term(gg,x)]
            if not bad: continue
            g=cn(maxo([cn(b) for b in bad])); px=psi(u,x)
            key=(str(x),u)
            if key in seen: continue
            seen.add(key); n+=1
            if tsize(g)<tsize(x): g_tsize_lt_x+=1
            R=[xi for xi in pool if acanon(u,xi) and psi(u,xi)==px]
            below=[xi for xi in R if lt_term(xi,g)]
            if below: realizer_below_g+=1
            if R:
                mn=R[0]
                for xi in R[1:]:
                    if lt_term(xi,mn): mn=xi
                if mn==g: minreal_is_g+=1
                if tsize(mn)<tsize(x): minreal_tsize_lt_x+=1
    print(f"rounds={r}: term maxo-step inst={n}")
    print(f"  realizer xi<g (NoRealizer violation) = {realizer_below_g}/{n}")
    print(f"  minimal canonical realizer == g = {minreal_is_g}/{n}   g tsize<x tsize={g_tsize_lt_x}/{n}")
    print(f"  minimal realizer tsize < x tsize (IH reaches it) = {minreal_tsize_lt_x}/{n}")
