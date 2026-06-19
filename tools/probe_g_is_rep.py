# Is the maxo-violator g = proj_u x (one step reaches the rep)? g u-canonical (586/586) suggests
# proj_u x = g in ONE step (g already u-reduced). Verify proj_u x == g AND proj_u g == g.
# If so, the recursion is: PP(x,u): psiSelf x u = psiSelf g u, g=proj_u x u-canonical, ONE step.
# Then "no canonical xi<g realizing psiSelf x u" + g canonical => via injectivity (if we knew
# psiSelf x u=psiSelf g u)... still need the collapse. 
# THE actual closing argument: psiSelf x u in CsetSelf(g) u => M1 xi<g canon, psiSelf xi u=psiSelf x u.
# g u-canonical, xi<g canon => psiSelf xi u < psiSelf g u (strict_mono). Also need psiSelf x u
# relation. The KEY: psiSelf x u >= psiSelf g u would contradict psiSelf xi u=psiSelf x u<psiSelf g u.
# Is psiSelf x u >= psiSelf g u? mono(x<=g) gives <=. So psiSelf x u <= psiSelf g u. For =, need >=.
# The >= is the collapse content. Circular STILL. 
# UNLESS: x is u-NON-canonical and g is its rep. The Buchholz fact: a u-non-canonical x has
# psiSelf x u = psiSelf(rep) u because x ∉ CsetSelf(x) u means psiSelf x u <= x < ... 
# Let me test the FINAL non-circular lever: psiSelf x u <= x (x u-non-canon, psiSelf_le_self),
# and g >= x, and psiSelf g u: is psiSelf x u = psiSelf g u provable from
# "x in [something, g] all u-non-canonical except g"? i.e. gap [x, g) ALL u-non-canonical
# (g is the FIRST canonical >= x)? Test gap [x,g) clean (we saw 12/586 NOT clean)... 
# but maybe gap (x, g) excluding endpoints, or the TRUE-order gap. Re-test with g=proj_u x:
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
    seen=set(); n=0; g_eq_proj=0; gap_clean_xg=0; multi_step=0
    for x in terms:
        for u in range(0,4):
            bad=[gg for gg in G(u,x) if not lt_term(gg,x)]
            if not bad: continue
            g=cn(maxo([cn(b) for b in bad]))
            key=(str(x),u)
            if key in seen: continue
            seen.add(key); n+=1
            d=cn(proj(u,x))
            if g==d: g_eq_proj+=1
            else: multi_step+=1
            # gap [x,g) all u-non-canonical (g first canonical)?
            gap=[gg for gg in pool if le_t(x,gg) and lt_term(gg,g) and selfcanon(u,gg)]
            if not gap: gap_clean_xg+=1
    print(f"rounds={r}: maxo-step inst={n}  g==proj_u x (one step)={g_eq_proj}  multi-step={multi_step}")
    print(f"  gap [x,g) ALL u-non-canonical = {gap_clean_xg}/{n}")
