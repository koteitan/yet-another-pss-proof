# delta'=proj_u(psiSelf eta w) is u-canonical with value-id, but delta'>c. Is delta'<alpha?
# alpha must satisfy hξα: psiSelf eta w < alpha (and eta<alpha, eta in CsetSelf(alpha)v).
# Test delta' vs the eta-host enclosing alpha. Use IH output instead: the IH at c=psiSelf eta w
# gives a rep delta with delta < c... no, NoncanonValueMem gives delta < (the BOUND). The IH
# bound here for the value psiSelf c u is... NoncanonValueMem(alpha'=?, ...). 
# Reconsider: NoncanonValueMem says: xi in CsetSelf(alpha) v, xi<alpha, xi u-non-canon, v<=u
#   => psiSelf xi u in CsetSelf(alpha) v. The MEMBERSHIP. The REP version (rnk) gives
#   delta<alpha with value-id. Applied to xi=c=psiSelf eta w, bound alpha (the SAME alpha!):
#   need c in CsetSelf(alpha) v, c<alpha (have hξα), c u-non-canon (have hnc), v<=u (have).
#   => rep delta < alpha, delta in CsetSelf(alpha) v, delta u-canon, psiSelf delta u=psiSelf c u.
#   THAT'S EXACTLY caseB's conclusion! So caseB(eta) REDUCES to NoncanonValueMem-rep at
#   the SAME alpha but smaller GENERATOR c=psiSelf eta w (which is < eta? or < the rank).
# The recursion is on the INNER rank n (c appears at lower rank than psiSelf eta w's generator)
#   OR c<alpha lets the rnk-IH (IHn? IHα?) apply. KEY: is c in CsetSelf(alpha) v? TEST.
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
    seen=set(); ninst=0; c_in_C=0
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)
            for u in range(0,w+1):
                if selfcanon(u,eta): continue
                if selfcanon(u,pw): continue
                c=pw
                for v in range(0,u+1):
                    for alpha in pool[:120]:
                        if not lt_term(eta,alpha): continue
                        if not lt_term(pw,alpha): continue
                        if not memC(alpha,v,eta): continue   # eta in CsetSelf(alpha)v (hηC)
                        key=(str(eta),w,u,v,str(alpha))
                        if key in seen: continue
                        seen.add(key); ninst+=1
                        # is c=psiSelf eta w in CsetSelf(alpha) v ?  (then IH-rep at alpha applies to c)
                        if memC(alpha,v,c): c_in_C+=1
                        if ninst>120000: break
                    if ninst>120000: break
    print(f"rounds={r}: full inst={ninst}  c=psiSelf eta w in CsetSelf(alpha) v = {c_in_C}/{ninst}")
