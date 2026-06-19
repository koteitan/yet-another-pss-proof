# Per-step ⟺ extra generators of C_u(oV g) (canonical xi with oV x <= xi < oV g, OR more
# precisely xi in C_u(oV g)∩[oVx,oVg) that AREN'T generators of C_u(oV x)) don't realize a
# value < psi_u(oV x). The hypothetical realizer of psi_u(oV x) in C_u(oV g): canonical xi<oV g,
# psi_u(xi)=psi_u(oV x). We know NONE exists (NoRealizer 0/586). 
# NON-CIRCULAR test: the extra generators have args xi with oV x <= xi (since C_u(oV x) already
# has all args < oV x). For such xi (>= oV x, canonical, < oV g): is psi_u(xi) > psi_u(oV x)
# WITHOUT assuming the collapse? xi >= oV x, xi canonical. psi_u(xi) vs psi_u(oV x):
#   xi canonical & xi >= oV x. If xi > oV x: strict_mono needs SMALLER canonical... xi is the
#   bigger. psi_u(oV x) <= psi_u(xi)? oV x <= xi mono => psi_u(oV x) <= psi_u(xi). So
#   psi_u(xi) >= psi_u(oV x) FREE (mono)! And for the realizer we'd need psi_u(xi)=psi_u(oV x),
#   i.e. EQUALITY. With psi_u(xi)>=psi_u(oV x), equality possible only if =. 
# So the realizer xi (>= oV x, canonical) has psi_u(xi) >= psi_u(oV x), and = would need
#   xi to be a canonical realizer. The KEY non-circular fact: is xi > oV x STRICT for all
#   extra canonical generators (then psi_u(xi) > psi_u(oV x) if also... no, mono gives >= only).
# TEST: are the extra canonical generators xi (in C_u(oV g), >= oV x, < oV g) such that
#   psi_u(xi) > psi_u(oV x) STRICTLY (so can't realize)? This would close it via MONO + strict.
#   Need: xi > oV x (strict) AND xi canonical => psi_u(oV x) < psi_u(xi)? mono gives <=.
#   strict needs oV x canonical (it's NOT). Hmm. Test the values directly:
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
    seen=set(); n=0
    # the generators of C_u(oV g) that are NOT in C_u(oV x): args xi (canonical, in band, ...).
    # We test: every canonical xi that is a member of C_u(oV g)∩[oVx, oVg) [the "extra zone"]
    # has psi_u(xi) >= psi_u(oV x) [mono, free if xi>=oV x] AND != psi_u(oV x) [strict].
    geq=0; strict=0; tot=0
    for x in terms:
        for u in range(0,4):
            bad=[gg for gg in G(u,x) if not lt_term(gg,x)]
            if not bad: continue
            g=cn(maxo([cn(b) for b in bad])); px=psi(u,x)
            key=(str(x),u)
            if key in seen: continue
            seen.add(key); n+=1
            extra=[xi for xi in pool if le_t(x,xi) and lt_term(xi,g) and acanon(u,xi)]
            allgeq=True; allstrict=True
            for xi in extra:
                pv=psi(u,xi); tot+=1
                if lt_term(pv,px): allgeq=False    # psi_u(xi) < psi_u(oV x) -- would be a problem
                if pv==px: allstrict=False          # = realizer
            if allgeq: geq+=1
            if allstrict: strict+=1
    print(f"rounds={r}: inst={n} extra-gen total={tot}")
    print(f"  all extra canonical xi (>=oVx,<oVg): psi_u(xi) >= psi_u(oV x) (mono-free?) = {geq}/{n}")
    print(f"  all extra: psi_u(xi) != psi_u(oV x) (no realizer) = {strict}/{n}")
