# The term_nec MECHANISM for NoRealizer (the ya-pss psi_proj_nonmem argument, nrm.thy):
# Suppose realizer xi<g canonical, psi_u(oV xi)=psi_u(oV x). Then by M1, psi_u(oV x) is a
# generator in Cset(oV g) u with arg xi<oV g. The collapse psi_u(oV x)=psi_u(oV g) would give
# (via injectivity, xi & g... no g maybe noncanon) ... 
# ya-pss's ACTUAL stall: "the genuine collapse case needs xi = oV(proj a b) >= oV m, whose
# value-identity is psi_proj itself". So the realizer xi, if it exists, = oV(proj_u x) = oV g
# (the rep), NOT < g. The contradiction xi<g vs xi=rep needs xi=rep = PP. CIRCULAR.
# 
# So the QUESTION: does term_nec give "xi (canonical realizer) = oV g" WITHOUT psi_proj?
# term_nec at bound oV g applied to the term whose value is psi_u(oV x): the realizer xi is
# canonical, psi_u(oV xi)=psi_u(oV x). If we DON'T know xi=oV g, term_nec on xi gives xi's
# coeffs < (bound). Doesn't pin xi=oV g.
#
# DECISIVE TEST of whether the tsize-IH HELPS: the IH gives psi_proj_notmem at SMALLER terms.
# Does psi_proj at the subterm g (tsize smaller) — i.e. psi_u(oV g)=psi_u(oV(proj_u g))=psi_u(oV g)
# (g already u-canonical, trivial) — supply anything? g canonical so IH(g) is trivial. 
# The IH at OTHER smaller subterms: do they bound the realizer? Test if NoRealizer(x) reduces
# to NoRealizer/psi_proj at the PROPER subterms of x (tsize <). The realizer xi for psi_u(oV x):
# is xi's value psi_u(oV x) = psi_u(oV(some proper subterm of x))? If the value is "new" to x
# (not from a proper subterm), the IH can't supply it. TEST: is psi_u(oV x) achieved by any
# proper subterm of x at subscript u? (if NO, the value is genuinely x-level => IH useless).
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
    out=set()
    st=[t]
    while st:
        x=st.pop()
        out.add(x)
        for _,_,b in x: st.append(b)
    return out
def maxo(lst):
    m=lst[0]
    for h in lst[1:]:
        if lt_term(m,h): m=h
    return m
def Gu(u,t):
    out=[]
    for p in t:
        _,v,b=p
        if v>=u: out.append(b); out+=Gu(u,b)
    return out
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
    seen=set(); n=0
    val_from_subterm=0   # psi_u(oV x) = psi_u(oV sub) for a PROPER subterm sub (IH reaches)
    g_is_propersubterm=0 # g (the rep/realizer) is a proper subterm of x
    for x in terms:
        for u in range(0,4):
            bad=[gg for gg in Gu(u,x) if not lt_term(cn(gg),x)]
            if not bad: continue
            g=cn(maxo([cn(b) for b in bad])); px=psi(u,x)
            key=(str(x),u)
            if key in seen: continue
            seen.add(key); n+=1
            subs=[s for s in subterms(x) if s!=x]
            if any(psi(u,s)==px for s in subs): val_from_subterm+=1
            if g in subs: g_is_propersubterm+=1
    print(f"rounds={r}: inst={n}")
    print(f"  psi_u(oV x) achieved by a PROPER subterm (IH reaches the value) = {val_from_subterm}/{n}")
    print(f"  g (rep/realizer) IS a proper subterm of x = {g_is_propersubterm}/{n}")
