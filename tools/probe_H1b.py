# H1: psiSelf c u = psiSelf eta u, c=psiSelf eta w. Q-le (c<=eta) only 671/884.
# When c>eta: need collapse [eta, c] instead. Test which orientation + value-bound.
# Case A (c<=eta): collapseSelf_le_valuebounded eta c with VB: gamma in [c,eta) canon => psiSelf gamma u<psiSelf c u. (qvb confirmed)
# Case B (eta<c): collapseSelf_le_valuebounded c eta? need eta<=c, VB: gamma in [eta,c) canon => psiSelf gamma u<psiSelf eta u.
#   i.e. collapse [eta,c], target psiSelf eta u.
# Test both VBs in their respective orientations + that one always applies.
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
    seen=set(); n=0
    cle=0; cgt=0; ceq=0
    caseA_vb=0; caseB_vb=0
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)
            for u in range(0,w+1):
                if selfcanon(u,eta): continue
                if selfcanon(u,pw): continue
                key=(str(eta),w,u)
                if key in seen: continue
                seen.add(key); n+=1
                c=pw; pcu=psi(u,c); peu=psi(u,eta)
                if c==eta: ceq+=1
                elif lt_term(c,eta):  # c<eta : collapse [c,eta], target psiSelf c u
                    cle+=1
                    gam=[g for g in pool if le_t(c,g) and lt_term(g,eta) and selfcanon(u,g)]
                    if all(lt_term(psi(u,g),pcu) for g in gam): caseA_vb+=1
                else:  # eta<c : collapse [eta,c], target psiSelf eta u
                    cgt+=1
                    gam=[g for g in pool if le_t(eta,g) and lt_term(g,c) and selfcanon(u,g)]
                    if all(lt_term(psi(u,g),peu) for g in gam): caseB_vb+=1
    print(f"rounds={r}: inst={n}  c<eta={cle} c=eta={ceq} c>eta={cgt}")
    print(f"  caseA(c<eta) value-bound vs psiSelf c u = {caseA_vb}/{cle}")
    print(f"  caseB(eta<c) value-bound vs psiSelf eta u = {caseB_vb}/{cgt}")
