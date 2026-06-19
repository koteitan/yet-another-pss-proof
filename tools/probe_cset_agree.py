# Step 2 make-or-break: C_u-set agreement below threshold, NON-circularity test.
# Per-step: psi_u(oV x) = psi_u(oV g), g=maxo u-violator subterm, oV x<=oV g.
# psi_u(a) = min{gamma : gamma not in C_u(a)}. Equal <=> C_u(oV x) and C_u(oV g) agree on
# the initial segment below the common value T := psi_u(oV g).
# AGREEMENT(x,g,u): C_u(oV x) ∩ [0,T) == C_u(oV g) ∩ [0,T), where T=psi_u(oV g).
# Model: C_u(a) on the canonical fragment = CsetSelf membership term_in(a,u,.). T via nrm.
# We test, for elements gamma in the corpus with gamma < T (value order via psiSelf? T is an
# ordinal). Represent T by its canonical term psi_u(oV g) = nrm(D_u(g)). gamma<T means the
# value gamma is below. Use canonical TERMS gamma_t with oV gamma_t < T.
#
# NON-CIRCULARITY: test if AGREEMENT holds AND whether it needs the value-equality.
# (A) AGREEMENT count (should be 0-viol if true).
# (B) the KEY non-circular probe: does C_u(oV x) ⊆ C_u(oV g) [one direction, below T] follow
#     from the closure clauses + structural oV x relation, NOT from psi-equality?
#     C_u(oV g) is the closure of g. oV x: x has u-violator g, x = context around g. Is every
#     generator-arg/coeff of oV x already in C_u(oV g)? Test: are oV x's "pieces" in C_u(oV g)?
#  Specifically: oV x itself -- is oV x in C_u(oV g)? (the membership that would give agreement)
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
for r in (5,6,7):
    terms=[cn(t) for t in collect(r) if in_OT(t)]; pool=terms
    seen=set(); n=0; agree=0; ovx_in_Cg=0
    # agreement below T=psi_u(oV g): for canonical-corpus gamma with value < T, in C_u(x) iff C_u(g)
    for x in terms:
        for u in range(0,4):
            bad=[gg for gg in G(u,x) if not lt_term(gg,x)]
            if not bad: continue
            g=cn(maxo([cn(b) for b in bad]))
            key=(str(x),u)
            if key in seen: continue
            seen.add(key); n+=1
            T=psi(u,g)   # threshold value = psi_u(oV g) (= psi_u(oV x) if collapse)
            # gamma ranges over corpus terms with value < T (value order: gamma < T means
            # the ordinal oV gamma < oV(D_u g). Proxy: lt_term(gamma, T) on canonical names.)
            viol=False
            for gamma in pool:
                if not lt_term(gamma,T): continue  # only below threshold
                inx=term_in(x,u,gamma); ing=term_in(g,u,gamma)
                if inx!=ing: viol=True; break
            if not viol: agree+=1
            # (B) is oV x in C_u(oV g)? (would be a route to agreement; test directly)
            if term_in(g,u,x): ovx_in_Cg+=1
    print(f"rounds={r}: per-step inst={n}")
    print(f"  AGREEMENT C_u(oV x)|<T == C_u(oV g)|<T  = {agree}/{n}")
    print(f"  oV x in C_u(oV g) = {ovx_in_Cg}/{n}")
