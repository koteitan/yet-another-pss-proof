# THE decisive non-circular check. PP_step: psi_u(oV x)=psi_u(oV g), g=maxo-viol proper subterm,
#   g u-canonical, oV x <= oV g.
# Via psiSelf_eq_of_notMem(oV x<=oV g): suffices psi_u(oV x) NOT in Cset(oV g) u.
# Suppose IN. M1: canonical xi<oV g, psi_u(xi)=psi_u(oV x). 
# THE non-circular finish (ya-pss necessity B2 + term_nec): 
#   We want a contradiction from xi<oV g. The ya-pss stall is xi could = oV(proj_u x)=oV g
#   (NOT <). To rule out xi<oV g canonical realizing the value:
#   Apply term_nec to g (PROPER SUBTERM, IH available!): term_nec(g) at bound oV g... 
#   Actually the KEY: xi<oV g canonical with psi_u(xi)=psi_u(oV x)=psi_u(oV g) [if collapse].
#   g u-canonical, xi canonical, psi_u(oV g)=psi_u(xi) => xi=oV g (injectivity), contra xi<oV g.
#   This uses psi_u(oV x)=psi_u(oV g) [the collapse]. CIRCULAR.
# WITHOUT the collapse: xi<oV g, psi_u(xi)=psi_u(oV x). We know oV x has violator g (oV g>=oV x).
#   By term_nec contrapositive at x: oV x is u-NON-canonical (B2). 
#   Does psi_u(xi)=psi_u(oV x) with xi canonical, xi<oV g, lead to contradiction via term_nec?
#   psi_u(xi) in Cset... xi canonical => psi_u(xi) fires. 
# Let me TEST the genuinely-new angle: is the realizer xi (if existed) FORCED to have oV x as
#   a G_u-coefficient (by some necessity), but xi<oV g and oV x... Test whether the value
#   psi_u(oV x)'s ONLY canonical realizer (=g) being a proper subterm means: ANY OT canonical
#   term realizing it must CONTAIN g's structure, forcing tsize >= ... no.
# PRACTICAL decisive test: assume the tsize-IH = "psi_proj_notmem holds for all proper subterms".
#   Does psi_proj_notmem(x) [= PP_step at x] follow? psi_proj_notmem(x): psi_u(oV x) not in
#   Cset(oV g) u. The IH gives it for proper subterms. x's maxo-violator g is a proper subterm
#   => IH(g): psi_u(oV g) not in Cset(oV(proj_u g)) u. But proj_u g = g (g canonical), so IH(g)
#   is psi_u(oV g) not in Cset(oV g) u = psiSelf_notMem (TRIVIAL, free). USELESS for x.
#   => the IH at the subterm g is TRIVIAL (g canonical), supplies NOTHING for x's collapse.
# This is the CIRCULARITY: PP_step(x) needs the value psi_u(oV x)=psi_u(oV g), but IH(g) is
#   vacuous (g canonical). The tsize-IH does NOT supply the cross-level collapse psi_u(oV x)=
#   psi_u(oV g). CONFIRM: IH at proper subterms is all about THEIR reps (trivial for canonical
#   subterms like g); none gives x's collapse. Count: how many proper subterms have NON-trivial
#   psi_proj_notmem content that bears on x's collapse?
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
def subterms(t):
    out=set(); st=[t]
    while st:
        x=st.pop(); out.add(x)
        for _,_,b in x: st.append(b)
    return out
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
    seen=set(); n=0; g_canon_IH_trivial=0
    # does ANY proper subterm s of x have a maxo-u'-violator (non-trivial psi_proj) whose
    # collapse VALUE relates to x's collapse psi_u(oV x)=psi_u(oV g)?
    subterm_supplies=0
    for x in terms:
        for u in range(0,4):
            bad=[gg for gg in Gu(u,x) if not lt_term(cn(gg),x)]
            if not bad: continue
            g=cn(maxo([cn(b) for b in bad])); px=psi(u,x)
            key=(str(x),u)
            if key in seen: continue
            seen.add(key); n+=1
            # IH(g) trivial since g u-canonical?
            if acanon(u,g): g_canon_IH_trivial+=1
            # is there a proper subterm s with a u'-collapse psi_u'(oV s)=psi_u'(oV(its rep))
            # that EQUALS x's needed collapse value px? (the IH content that bears on x)
            subs=[s for s in subterms(x) if s!=x]
            bears=False
            for s in subs:
                for up in range(0,4):
                    bads=[gg for gg in Gu(up,s) if not lt_term(cn(gg),s)]
                    if not bads: continue  # s up-reduced, trivial
                    # s has a non-trivial up-collapse; does its value = px?
                    if psi(up,s)==px: bears=True
            if bears: subterm_supplies+=1
    print(f"rounds={r}: inst={n}")
    print(f"  g (maxo rep) u-canonical => IH(g) TRIVIAL = {g_canon_IH_trivial}/{n}")
    print(f"  a PROPER subterm has a NON-trivial collapse with value = px (IH bears on x) = {subterm_supplies}/{n}")
