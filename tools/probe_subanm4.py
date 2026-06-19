# Direct route for subA_nm. c=psiSelf eta w, c u-non-canon, c<=eta, eta u-canon.
# Goal: psiSelf c u NOT in CsetSelf(eta) u.
# Candidate provable mechanism: CsetSelf(c) u == CsetSelf(eta) u  (the closures agree)
#   would give it from psiSelf_notMem c u. Holds iff gap [c,eta) all u-non-canonical?
#   BUT eta is u-CANONICAL and c<=eta, so eta in [c,eta]? eta is the endpoint.
#   CsetSelf_succ_eq needs the bound non-canonical. Here eta IS canonical => closures
#   DIFFER (eta enters its own closure). So CsetSelf(c)=CsetSelf(eta) likely FALSE.
# Test:
#  T-A: CsetSelf(c) u == CsetSelf(eta) u ? (membership-equal on corpus)
#  T-B: psiSelf c u  vs  psiSelf eta u : is psiSelf c u >= psiSelf eta u (the >= direction)?
#  T-C: KEY -- psiSelf eta u NOT in CsetSelf(eta) u (psiSelf_notMem) AND
#       psiSelf c u == psiSelf eta u would close. We established F3. Is F3 provable as
#       psiSelf c u <= psiSelf eta u (mono, since c<=eta) AND psiSelf eta u<=psiSelf c u?
#       The >= direction psiSelf eta u <= psiSelf c u is the crux. Test it holds.
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
for r in (6,7):
    terms=[cn(t) for t in collect(r) if in_OT(t)]
    pool=terms
    seen=set(); n=0; tb_ge=0; psicu_le=0; cstrict=0
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)
            for u in range(0,4):
                if not(u<=w and (not noncanon_self(u,eta)) and noncanon_self(u,pw)): continue
                key=(str(eta),w,u)
                if key in seen: continue
                seen.add(key); n+=1
                c=pw
                peu=psi(u,eta); pcu=psi(u,c)
                # T-B/C: psiSelf eta u <= psiSelf c u  (>= direction of F3)
                if le_t(peu,pcu): tb_ge+=1
                # psiSelf c u <= psiSelf eta u (mono direction, c<=eta)
                if le_t(pcu,peu): psicu_le+=1
                if lt_term(c,eta): cstrict+=1
    print(f"rounds={r}: subA-A inst={n}")
    print(f"  psiSelf eta u <= psiSelf c u  (>= dir, the CRUX) = {tb_ge}/{n}")
    print(f"  psiSelf c u <= psiSelf eta u  (mono, c<=eta)     = {psicu_le}/{n}")
    print(f"  c=psiSelf eta w STRICTLY < eta                   = {cstrict}/{n}")
