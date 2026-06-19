# The REAL term_nec mechanism for NoRealizer (ya-pss nrm.thy ROADMAP 続89(30) argument):
# NoRealizer <=> psi_u(oV x) NOT in Cset_c(oV g) u. Suppose IN.
# 1.9 necessity (term_nec on the GENERATOR psi_u(oV x)): G_u(psi_u(oV x)) ⊆ oV g.
#    Buchholz G_u(psi_u(beta)) = {beta} ∪ G_u(beta) when u<=u. So oV x ∈ G_u(psi_u(oV x)) ⊆ oV g
#    => oV x < oV g. CONSISTENT with oV x <= oV g (no contradiction yet).
# 2. The bad coefficient: x has G_u-coeff g (the maxo violator) with oV g >= oV x.
#    G_u(oV x) ∋ oV g (since g ∈ G_u(x) at term level => oV g ∈ G_u(oV x)).
#    Then G_u(psi_u(oV x)) = {oV x} ∪ G_u(oV x) ∋ oV g. By necessity ⊆ oV g => oV g < oV g. CONTRA!
# THIS is non-circular IF: (a) term_nec gives G_u(psi_u(oV x)) ⊆ oV g [necessity at the
#   value, bound oV g], and (b) oV g ∈ G_u(oV x) [the maxo coeff, term-structural].
# term_nec needs the value psi_u(oV x) ∈ Cset_c(oV g) u to be the oV of a WF3 TERM with that
#   G_u. psi_u(oV x) = oV(D_u(x)) where D_u(x)=the term (u,x). Is D_u(x) wf3? NO if x has a
#   u-violator (g). So term_nec does NOT apply to psi_u(oV x) directly (it's non-wf3)! 
# This is EXACTLY ya-pss's stall: term_nec needs wf3, but psi_u(oV x) for non-u-canonical x
#   is the value of a NON-wf3 term D_u(x). Must rewrite via the rep: psi_u(oV x)=psi_u(oV g)=
#   oV(D_u(g)) wf3 -- but that's PP_step = circular.
# DECISIVE TEST: confirm the necessity contradiction (oV g ∈ G_u(oV x) ⊆ ... < oV g) HOLDS,
#   AND that it requires the value as oV-of-wf3 (i.e. the rep), confirming circular.
# Compute: oV g ∈ G_u(oV x)? (term G_u(x) ∋ g => yes). And is D_u(x) [=term (u,x)] wf3? (NO, has violator)
import sys
sys.path.insert(0,'.')
from valnorm import conv, nrm, lt_term, G, in_OT
from wfe_explore import translate, enum_ST
Z=()
def cn(x): return tuple(('D',vv,cn(bb)) for _,vv,bb in x)
def le_t(a,b): return a==b or lt_term(a,b)
def Gu(u,t):
    out=[]
    for p in t:
        _,v,b=p
        if v>=u: out.append(b); out+=Gu(u,b)
    return out
def maxo(lst):
    m=lst[0]
    for h in lst[1:]:
        if lt_term(m,h): m=h
    return m
def Du(u,x): return ((  'D',u,x),)  # the term D_u(x)
def wf3_term(t): return in_OT(t)
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
    terms=[cn(t) for t in collect(r) if in_OT(t)]
    seen=set(); n=0; g_in_Gu_x=0; Dux_wf3=0; Dug_wf3=0
    for x in terms:
        for u in range(0,4):
            bad=[cn(gg) for gg in Gu(u,x) if not lt_term(cn(gg),x)]
            if not bad: continue
            g=maxo(bad)
            key=(str(x),u)
            if key in seen: continue
            seen.add(key); n+=1
            # oV g in G_u(oV x): g in G_u(x) (term) => yes structurally
            if g in [cn(z) for z in Gu(u,x)]: g_in_Gu_x+=1
            # D_u(x) wf3? (the term whose value is psi_u(oV x)) -- should be NON-wf3
            if wf3_term(Du(u,x)): Dux_wf3+=1
            # D_u(g) wf3? (the rep's term) -- should be wf3 (g u-canonical)
            if wf3_term(Du(u,g)): Dug_wf3+=1
    print(f"rounds={r}: inst={n}")
    print(f"  oV g in G_u(oV x) (the necessity-contra coeff) = {g_in_Gu_x}/{n}")
    print(f"  D_u(x) [value psi_u(oV x)] is wf3 = {Dux_wf3}/{n}  (LOW => term_nec can't apply to x's value)")
    print(f"  D_u(g) [value psi_u(oV g)=rep] is wf3 = {Dug_wf3}/{n}  (HIGH => term_nec applies only after PP rewrite)")
