# Full by_contra route for subA_nm, using CANONICAL witness (CsetSelf_witness_canonical).
# Assume psiSelf c u in CsetSelf(eta) u. Canon witness zeta: psiSelf zeta u = psiSelf c u,
# zeta<eta, zeta in CsetSelf(eta) u, zeta u-canonical.  (band forces u'=u)
# Then psiSelf_strict_mono_arg(zeta<eta, zeta canon): psiSelf zeta u < psiSelf eta u.
# => psiSelf c u < psiSelf eta u.   ... need a contradiction.
# We ALSO have eta u-canonical. CsetSelf_psi_closed(eta in CsetSelf(eta) u, ... ) but
# eta not < eta. Hmm.
# WAIT: the contradiction must come from c u-non-canonical + c=psiSelf eta w.
# zeta < eta, psiSelf zeta u = psiSelf c u = psiSelf(psiSelf eta w) u.
# Is zeta canonical with this value FORCED to relate to eta? Test: among the actual
# canonical witnesses (if membership held - it doesn't, 0), what would they be?
# Since membership is FALSE (0/623), the by_contra route IS valid - we just need ANY
# derivable contradiction. The cleanest: psiSelf c u < psiSelf eta u (from witness) must
# contradict a PROVABLE lower bound psiSelf eta u <= psiSelf c u.
# So we're back to needing the crux as a LOWER bound. UNLESS the witness gives more.
#
# NEW IDEA: zeta u-canonical, zeta<eta, psiSelf zeta u=psiSelf c u. Also c=psiSelf eta w
# is u-NON-canonical. By psiSelf_canonical_inj we CANNOT equate zeta and c (c non-canon).
# But consider: psiSelf zeta u = psiSelf c u. Apply the fact c u-non-canon =>
#   psiSelf c u <= c (psiSelf_le_self_of_not_canon). And zeta canonical, zeta < c?? or
#   zeta >= c? Test zeta vs c. If we could show zeta >= c... no.
# Let me just test: IS there a provable contradiction = does psiSelf c u < psiSelf eta u
# combined with c u-non-canon + u<=w + eta u-canon yield False via mono facts only?
# psiSelf c u < psiSelf eta u, and psiSelf eta u <= psiSelf eta w?? (X1: psiSelf eta u<=c).
# psiSelf c u < psiSelf eta u <= c. So psiSelf c u < c (strict). That's CONSISTENT
# (psiSelf c u <= c always). NO contradiction. So the witness route alone FAILS;
# the crux is irreducible content. CONFIRM by checking psiSelf c u < c is the norm:
import sys
sys.path.insert(0,'.')
from valnorm import conv, nrm, lt_term, G, in_OT
from wfe_explore import translate, enum_ST
Z=()
def cn(x): return tuple(('D',vv,cn(bb)) for _,vv,bb in x)
def le_t(a,b): return a==b or lt_term(a,b)
def acanon(u,t): return not any(not lt_term(x,t) for x in G(u,t))
def princ_in(alpha,v,p):
    _,u,xi=p
    if u<v: return True
    if not lt_term(xi,alpha): return False
    if not acanon(u,xi): return False
    return term_in(alpha,v,xi)
def term_in(alpha,v,delta):
    if delta==Z: return True
    return all(princ_in(alpha,v,p) for p in delta)
def psi(a,arg): return cn(nrm((('D',a,arg),)))
def noncanon_self(u,t): return not term_in(t,u,t)
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
for r in (7,):
    terms=[cn(t) for t in collect(r) if in_OT(t)]
    seen=set(); n=0; pcu_lt_c=0; pcu_eq_c=0; eta_eq_proj_u_c=0
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)
            for u in range(0,4):
                if not(u<=w and (not noncanon_self(u,eta)) and noncanon_self(u,pw)): continue
                key=(str(eta),w,u)
                if key in seen: continue
                seen.add(key); n+=1
                c=pw; pcu=psi(u,c)
                if lt_term(pcu,c): pcu_lt_c+=1
                if pcu==c: pcu_eq_c+=1
    print(f"rounds={r}: inst={n}  psiSelf c u < c={pcu_lt_c}  == c={pcu_eq_c}")
