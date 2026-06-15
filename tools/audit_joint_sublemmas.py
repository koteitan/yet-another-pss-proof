# Verify the 4 joint-induction residual sub-lemmas at closure+5/+6 (explicit canonicity).
import sys
sys.path.insert(0,'.')
from valnorm import conv, nrm, lt_term, G
from wfe_explore import translate, enum_ST
Z=()
def noncanon_at(u,t): return any(not lt_term(x,t) for x in G(u,t))
def canon_at(u,t): return not noncanon_at(u,t)
def le_t(a,b): return a==b or lt_term(a,b)
def cn(t): return tuple(('D',v,cn(b)) for _,v,b in t)
def Om(k): return (('D',k,()),)
def princ_in_Cself(alpha, v, p):
    _,u,xi = p
    if u < v: return True
    if not lt_term(xi, alpha): return False
    if not canon_at(u, xi): return False
    return term_in_Cself(alpha, v, xi)
def term_in_Cself(alpha, v, delta):
    if delta == Z: return True
    return all(princ_in_Cself(alpha, v, p) for p in delta)
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
def audit(rounds):
    terms=set()
    for M in enum_ST(rounds=rounds):
        t=conv(translate(M)); st=[t]
        while st:
            x=st.pop()
            if not x: continue
            for (_,_,arg) in x: st.append(arg)
            terms.add(x)
    # subA_le: η canon@u, u≤w, ξ=psiSelf η w noncanon@u  =>  psiSelf η w ≤T η
    # subA_nm: same  =>  psiSelf(psiSelf η w) u ∉ CsetSelf η u  (princ in Cself(η,u) false)
    sA=0; sA_le=0; sA_nm=0
    seen=set()
    for xi in terms:
        if len(xi)!=1: continue
        w,eta=xi[0][1],xi[0][2]
        for u in range(0,w+1):
            if not noncanon_at(u,xi): continue
            if not canon_at(u,eta): continue
            key=(u,tuple(map(str,xi)))
            if key in seen: continue
            seen.add(key); sA+=1
            if le_t(xi,eta): sA_le+=1
            if not princ_in_Cself(eta,u,('D',u,xi)): sA_nm+=1
    print(f"rounds={rounds}: sub-case A instances={sA}")
    print(f"  subA_le (psiSelf η w ≤ η): {sA_le}/{sA}")
    print(f"  subA_nm (psiSelf(psiSelf η w) u ∉ CsetSelf η u): {sA_nm}/{sA}")
    # caseB: η noncanon@u. δ=proj u η works. Check δ<α not needed standalone; check
    #   the collapse value: psiSelf(proj u η) u == psiSelf(psiSelf η w) u, δ canon@u
    sB=0; B_ok=0
    seen=set()
    for xi in terms:
        if len(xi)!=1: continue
        w,eta=xi[0][1],xi[0][2]
        for u in range(0,w+1):
            if not noncanon_at(u,xi): continue
            if canon_at(u,eta): continue  # B: η noncanon@u
            key=(u,tuple(map(str,xi)))
            if key in seen: continue
            seen.add(key); sB+=1
            d=proj(u,eta)
            ok = (canon_at(u,d) and cn(nrm((('D',u,d),)))==cn(nrm((('D',u,xi),))))
            if ok: B_ok+=1
    print(f"  caseB instances={sB}  (δ=proj u η canon & value-collapse): {B_ok}/{sB}")
for r in (5,6):
    audit(r)
