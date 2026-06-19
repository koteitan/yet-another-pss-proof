# Single maxo-step: psiSelf x u = psiSelf g u, g=maxo{u-viol x}, x<=g, tsize(g)<tsize(x).
# Via psiSelf_eq_of_notMem(x<=g): psiSelf x u NOT in CsetSelf(g) u.
# M1 witness xi<g canonical, psiSelf xi u = psiSelf x u. For contradiction: no such xi.
# By psiSelf_strict_mono_arg(xi<g, xi canon)... need g canonical? g may NOT be canonical
#  (g=maxo-violator, could be u-non-canon). Then strict_mono needs the SMALLER arg canon (xi is).
#  psiSelf xi u < psiSelf g u (xi<g, xi canon). So psiSelf x u < psiSelf g u. mono: <=. consistent.
# Hmm same issue. BUT the SINGLE step has g a SUBTERM (tsize smaller). The IH PP(g,u) gives
#  psiSelf g u = psiSelf(proj_u g) u = psiSelf delta u. So psiSelf x u in CsetSelf(g) u, and
#  via IH(g) the witness analysis at g... Let me test the CLEAN per-step claim:
#  "no canonical xi < g with psiSelf xi u = psiSelf x u" (the per-step non-realizer).
# AND whether x <= xi is forced (so xi in [x,g), and IH/strict_mono applies).
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
    seen=set(); n=0; realizer_below_g=0; g_canon=0
    for x in terms:
        for u in range(0,4):
            bad=[gg for gg in G(u,x) if not lt_term(gg,x)]
            if not bad: continue
            g=cn(maxo([cn(b) for b in bad])); px=psi(u,x)
            key=(str(x),u)
            if key in seen: continue
            seen.add(key); n+=1
            if selfcanon(u,g): g_canon+=1
            real=[xi for xi in pool if lt_term(xi,g) and selfcanon(u,xi) and psi(u,xi)==px]
            if real: realizer_below_g+=1
    print(f"rounds={r}: maxo-step inst={n}  g u-canonical={g_canon}/{n}")
    print(f"  canonical xi < g with psiSelf xi u = psiSelf x u (per-step realizer below) = {realizer_below_g}/{n}")
