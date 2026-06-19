# Is the per-step's canonical-rep witness establishable in the sub-eps range (where
# AcanonLtValue_lt_epsLvl is GREEN)? The per-step value psi_u(oV x): if oV x < epsLvl u,
# then oV x is u-CANONICAL (sub-eps everything canonical) => NOT a per-step case (x must be
# u-non-canonical). So ALL per-step cases have oV x >= epsLvl u (deep region). Confirm:
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
# epsLvl u proxy: a term is < epsLvl u iff it's u-canonical AND below the eps boundary.
# Simplest: every u-non-canonical term is >= epsLvl u (deep region) -- inherent. So no sub-eps
# per-step case exists. Confirm: per-step requires u-non-canonical x, which is deep.
r=7
terms=[cn(t) for t in collect(r) if in_OT(t)]
nperstep=0; allnoncanon=0
for x in terms:
    for u in range(0,4):
        bad=[gg for gg in G(u,x) if not lt_term(gg,x)]
        if not bad: continue
        nperstep+=1
        if not term_in(x,u,x): allnoncanon+=1  # x u-non-canonical (always in per-step)
print(f"per-step cases={nperstep}, x u-non-canonical (deep, sub-eps lever DEAD)={allnoncanon}/{nperstep}")
print("=> ALL per-step cases are deep-region (x u-non-canonical); the sub-eps AcanonLtValue_lt_epsLvl")
print("   lever does NOT apply. The canonical-rep witness needs the full construction.")
