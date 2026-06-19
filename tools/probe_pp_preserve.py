# Reframe VB(x,u) as psi_proj: PP(x,u) := psiSelf x u = psiSelf(proj_u x) u.
# proj_u x: iterates x -> maxo{u-violators of x} until u-reduced. Each step x -> g where
#   g = maxo{bad}, g in G_u(x), NOT (g<x). So proj_u x = proj_u(g) and the chain is
#   x -> g1 -> g2 -> ... -> delta (u-canonical fixpoint).
# psi_proj PRESERVATION through the proj-chain: PP(x,u) <- PP(g1,u) where g1=maxo-violator,
#   IF psiSelf x u = psiSelf g1 u (the SINGLE maxo-step collapse). Then PP(x)=PP(g1) chained.
# So the recursion is on the PROJ CHAIN (g1,g2,... each is a G_u-subterm, structurally SMALLER
# in tsize!). The base = delta (u-canonical, PP trivial: proj_u delta=delta).
# DECISIVE: is the single maxo-step psiSelf x u = psiSelf(maxo-violator) u derivable
#   non-circularly? maxo-violator g: g in G_u(x), NOT g<x (so x<=g value), g is a SUBTERM.
# This is EXACTLY the term-level psi_proj single step = CollapseResidueMaxo's content!
# Test: (A) proj-chain elements are tsize-smaller subterms (well-founded). (B) single
#   maxo-step value-collapse psiSelf x u = psiSelf g u holds (the per-step).
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
for r in (5,6,7):
    terms=[cn(t) for t in collect(r) if in_OT(t)]
    seen=set(); n=0; step_collapse=0; g_smaller_tsize=0; g_is_Gsub=0
    for x in terms:
        for u in range(0,4):
            bad=[gg for gg in G(u,x) if not lt_term(gg,x)]
            if not bad: continue   # x already u-reduced (proj fixpoint)
            g=cn(maxo([cn(b) for b in bad]))
            key=(str(x),u)
            if key in seen: continue
            seen.add(key); n+=1
            # single maxo-step value-collapse: psiSelf x u == psiSelf g u
            if psi(u,x)==psi(u,g): step_collapse+=1
            # g is a G_u-subterm
            if any(cn(b)==g for b in bad): g_is_Gsub+=1
            # tsize(g) < tsize(x)? (well-founded recursion on the proj chain)
            if tsize(g)<tsize(x): g_smaller_tsize+=1
    print(f"rounds={r}: maxo-step instances={n}")
    print(f"  single maxo-step collapse psiSelf x u == psiSelf(maxo-viol) u = {step_collapse}/{n}")
    print(f"  maxo-violator g is G_u-subterm of x = {g_is_Gsub}/{n}   tsize(g)<tsize(x) = {g_smaller_tsize}/{n}")
