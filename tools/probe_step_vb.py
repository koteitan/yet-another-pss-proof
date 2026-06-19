# Single maxo-step collapse psiSelf x u = psiSelf g u, g=maxo{u-violators of x}, x<=g (value).
# Via collapseSelf_le_valuebounded x g (x<=g) with value-bound: canonical gamma in [x,g) =>
#   psiSelf gamma u < psiSelf x u.  Is THIS value-bound non-circular (provable from
#   strict_mono or membership at SMALLER tsize)?
# Also test: is the gap [x,g) for the SINGLE step CLEAN (all u-non-canon)? Then plain
#   collapseSelf_le works! (vs the full [x, proj_u x) which was NOT clean).
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
def memC(a,v,d): return term_in(a,v,d)
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
    seen=set(); n=0; gap_clean=0; vb_strictmono=0; vb_mem=0; x_le_g=0
    for x in terms:
        for u in range(0,4):
            bad=[gg for gg in G(u,x) if not lt_term(gg,x)]
            if not bad: continue
            g=cn(maxo([cn(b) for b in bad]))
            key=(str(x),u)
            if key in seen: continue
            seen.add(key); n+=1
            if le_t(x,g): x_le_g+=1
            lo,hi=(x,g) if le_t(x,g) else (g,x)
            gam=[gg for gg in pool if le_t(lo,gg) and lt_term(gg,hi) and selfcanon(u,gg)]
            if not gam: gap_clean+=1
            # value-bound via strict_mono: all gap-canon gamma < x (so psiSelf gamma u<psiSelf x u)
            if all(lt_term(gg,x) for gg in gam): vb_strictmono+=1
            # value-bound via membership: all gap-canon gamma in CsetSelf(x) u
            if all(memC(x,u,gg) for gg in gam): vb_mem+=1
    print(f"rounds={r}: maxo-step inst={n}  x<=g={x_le_g}")
    print(f"  gap [x,g) CLEAN (all u-non-canon, => PLAIN collapseSelf_le) = {gap_clean}/{n}")
    print(f"  value-bound via strict_mono (gap-canon gamma < x)          = {vb_strictmono}/{n}")
    print(f"  value-bound via membership (gap-canon gamma in CsetSelf(x)u)= {vb_mem}/{n}")
