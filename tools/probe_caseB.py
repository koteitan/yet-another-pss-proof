# Model-verify the EXACT NVM_caseB def at +5/+6/+7.
# caseB: forall alpha v u w eta,
#   eta<alpha, eta in CsetSelf(alpha) v, eta in CsetSelf(eta) w (eta w-CANONICAL),
#   eta NOT in CsetSelf(eta) u (eta u-NON-canonical), v<=u, u<=w, psiSelf eta w < alpha,
#   psiSelf eta w NOT in CsetSelf(psiSelf eta w) u (c u-non-canonical)
#  =>  EXISTS delta:  delta<alpha, delta in CsetSelf(alpha) v, delta in CsetSelf(delta) u
#       (delta u-canonical), psiSelf delta u = psiSelf(psiSelf eta w) u.
# The proposed witness: delta = proj_u eta (the u-canonical rep of eta).
# We test: (T) does SOME valid delta exist (the EXISTENTIAL is true)?  via proj_u eta.
#  Also check NOT under-hypothesized: drop hyps one at a time, see if it breaks (load-bearing).
# Faithful: value claims via psi_a-equality (nrm/oV) + acanon; closure membership via term_in.
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
def selfcanon(u,t): return term_in(t,u,t)   # t in CsetSelf(t) u
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
for r in (5,6,7):
    terms=[cn(t) for t in collect(r) if in_OT(t)]
    pool=terms
    seen=set(); n=0
    proj_works=0       # delta=proj_u eta satisfies all 4 conclusion conjuncts (vs alpha=eta-host upper)
    exists_some=0      # SOME delta in pool works
    # we don't have alpha quantified; use alpha = a term with eta<alpha in corpus.
    # The conclusion's alpha-dependent conjuncts: delta<alpha, delta in CsetSelf(alpha) v.
    # Test with the MINIMAL valid alpha (just above psiSelf eta w, since hξα: psiSelf eta w<alpha)
    # Actually delta must be < alpha AND psiSelf eta w < alpha. Use alpha = eta's enclosing host.
    # Simplify: test the alpha-INDEPENDENT core: delta = proj_u eta is u-canonical,
    #   delta<=eta (proj decreases? NO proj_u increases value... check), and
    #   psiSelf delta u = psiSelf(psiSelf eta w) u (the VALUE-IDENTITY, the heart).
    val_id=0; delta_ucanon=0; delta_lt_alpha_ok=0
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)
            for u in range(0,w+1):
                # hyps: eta w-canonical, eta u-NON-canonical, c=pw u-non-canonical
                if not selfcanon(w,eta): continue
                if selfcanon(u,eta): continue        # need eta u-NON-canonical
                if selfcanon(u,pw): continue          # need pw u-non-canonical
                key=(str(eta),w,u)
                if key in seen: continue
                seen.add(key); n+=1
                # witness delta = proj_u eta
                d=cn(proj(u,eta))
                # VALUE-IDENTITY heart: psiSelf delta u == psiSelf(psiSelf eta w) u
                if psi(u,d)==psi(u,pw): val_id+=1
                if selfcanon(u,d): delta_ucanon+=1
    print(f"rounds={r}: caseB instances (exact hyps)={n}")
    print(f"  delta=proj_u eta : VALUE-IDENTITY psiSelf delta u == psiSelf(psiSelf eta w)u = {val_id}/{n}")
    print(f"  delta=proj_u eta : u-canonical                                              = {delta_ucanon}/{n}")
