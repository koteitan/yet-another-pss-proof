# DESIGN the value-bounded gap collapse hypothesis & verify.
# Setup (sub-case A): c = psiSelf eta w < eta, eta u-canonical, c u-non-canonical, u<=w.
# Want: psiSelf c u = psiSelf eta u  (the crux). Via psiSelf_eq_of_notMem(c<=eta):
#   suffices  psiSelf c u  NOT in  CsetSelf(eta) u.
# CsetSelf(eta) u members that could equal/exceed... the only way psiSelf c u enters is
# as a generator psiSelf gamma u with gamma in [.,eta) canonical, psiSelf gamma u = psiSelf c u.
# So the VALUE-BOUND that blocks it:
#   (VB) every a-canonical gamma in [c, eta) has  psiSelf gamma u  !=  psiSelf c u
#        (sharper / cleaner: psiSelf gamma u < psiSelf c u  OR  > , i.e. never EQUAL)
# Actually the collapse psiSelf c u = psiSelf eta u needs psiSelf c u to be the LEAST
# non-member of CsetSelf(eta) u. A canonical gamma in [c,eta) contributes psiSelf gamma u.
# If psiSelf gamma u < psiSelf c u it's harmless. If = psiSelf c u, BAD (puts target in).
# So VB = "no a-canonical gamma in [c,eta) has psiSelf gamma u >= psiSelf c u with the
# value LANDING at exactly psiSelf c u"... The faithful test: is psiSelf c u in CsetSelf(eta) u?
# We already know NO (subA_nm 623/623). Decompose WHY via the value-bound:
#   VB1: every a-canon gamma in [c,eta) has psiSelf gamma u <= psiSelf c u  (value-bounded below+=)
#   VB2: every a-canon gamma in [c,eta) has psiSelf gamma u <  psiSelf c u  (STRICT)
#   VB3: the gap-canonical Omega_k specifically: psiSelf Omega_k u  vs psiSelf c u
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
def selfcanon(u,t): return term_in(t,u,t)
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
    seen=set(); n=0; vb1=0; vb2=0; vb_eq=0
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)
            for u in range(0,4):
                if not(u<=w and selfcanon(u,eta) and (not selfcanon(u,pw))): continue
                key=(str(eta),w,u)
                if key in seen: continue
                seen.add(key); n+=1
                c=pw; pcu=psi(u,c)
                gam=[g for g in pool if le_t(c,g) and lt_term(g,eta) and selfcanon(u,g)]
                le=all(le_t(psi(u,g),pcu) for g in gam)        # VB1 psiSelf gamma u <= psiSelf c u
                lt=all(lt_term(psi(u,g),pcu) for g in gam)      # VB2 strict <
                anyeq=any(psi(u,g)==pcu for g in gam)           # any == (the BAD case)
                if le: vb1+=1
                if lt: vb2+=1
                if anyeq: vb_eq+=1
    print(f"rounds={r}: subA-A inst={n}")
    print(f"  VB1 all a-canon gamma in [c,eta): psiSelf gamma u <= psiSelf c u = {vb1}/{n}")
    print(f"  VB2 all a-canon gamma in [c,eta): psiSelf gamma u <  psiSelf c u = {vb2}/{n}")
    print(f"  BAD: some a-canon gamma in [c,eta) has psiSelf gamma u == psiSelf c u = {vb_eq}/{n}")
