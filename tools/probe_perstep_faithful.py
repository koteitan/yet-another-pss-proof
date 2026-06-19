# The faithful per-step: psi_u(oV x) NOT in C_u(oV g) (g=maxo u-viol, oV x<=oV g).
# C_u(oV g) membership of the VALUE psi_u(oV x): via the generator-trace (faithful, not lt_term).
# psi_u(oV x) in C_u(oV g) <=> exists canonical xi < oV g with psi_u(xi)=psi_u(oV x) (M1),
#   OR psi_u(oV x) built by +/Om (but it's principal in band u, so only generator).
# We computed earlier: NO canonical xi<g realizes psi_u(oV x) (NoRealizer 0/586). So
#   psi_u(oV x) NOT in C_u(oV g) -- the per-step IS TRUE faithfully. The question (Step 2)
#   is the NON-CIRCULAR PROOF: does it follow from closure clauses + structure?
#
# THE non-circular angle to test NOW: oV x and oV g relation. g=maxo u-violator subterm.
# Buchholz Remark/2.2: the difference between C_u(oV x) and C_u(oV g) is the GENERATOR clause
# C3: psi_w(xi) for xi in [the bound) canonical. Bounds differ: oV x vs oV g (oV x<=oV g).
# Larger bound oV g ADMITS MORE generators (xi up to oV g vs up to oV x). So C_u(oV g) ⊇
# C_u(oV x) potentially. For AGREEMENT below T, the EXTRA generators (xi in [oV x, oV g))
# must all have psi_w(xi) >= T or already present. Test: the extra generators xi in [oVx,oVg)
# canonical -- is psi_u(xi) (the relevant ones, w=u in band) >= T=psi_u(oV g)? OR < and present?
# This is the value-bound AGAIN but now as a SET-CLOSURE clause. Test if it's the SAME circular
# value-bound or genuinely closure-structural.
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
    # extra generators: canonical xi with oV x <= xi < oV g (the bound-difference window).
    # Do they all have psi_u(xi) NOT below T (so don't add new members < T)? Or < T but present?
    extra_safe=0; extra_problematic=0
    for x in terms:
        for u in range(0,4):
            bad=[gg for gg in G(u,x) if not lt_term(gg,x)]
            if not bad: continue
            g=cn(maxo([cn(b) for b in bad]))
            key=(str(x),u)
            if key in seen: continue
            seen.add(key); n+=1
            T=psi(u,g)
            extra=[xi for xi in pool if le_t(x,xi) and lt_term(xi,g) and acanon(u,xi)]
            # safe if every extra generator's value psi_u(xi) >= T OR already in C_u(oV x)|<T
            ok=True
            for xi in extra:
                pv=psi(u,xi)
                if lt_term(pv,T) and not term_in(x,u,pv):
                    ok=False; break
            if ok: extra_safe+=1
            else: extra_problematic+=1
    print(f"rounds={r}: per-step inst={n}")
    print(f"  bound-difference generators all SAFE (value>=T or already present) = {extra_safe}/{n}")
    print(f"  problematic (new member <T from extra generator) = {extra_problematic}/{n}")
