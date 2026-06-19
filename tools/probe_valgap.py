# Generalized collapse hypothesis: gap [c,eta) points gamma, instead of "u-non-canonical",
# require "psiSelf gamma u  is NOT a NEW value", i.e. for the collapse psiSelf c u =
# psiSelf eta u to hold via a value-stationarity argument: every gamma in [c,eta) has
# psiSelf gamma u  IN  CsetSelf(eta) u OR <= the plateau. The cleanest generalization
# that collapseSelf_le's succ-induction needs: at each succ step delta -> delta+1, need
# psiSelf delta u = psiSelf (delta+1) u, which collapseSelf_succ gives from
# "delta NOT in CsetSelf(delta) u" (delta u-non-canonical). For a u-CANONICAL Omega_k
# in the gap that FAILS. BUT maybe psiSelf delta u = psiSelf(delta+1) u ALSO holds when
# delta IS canonical but psiSelf delta u re-collapses? NO: if delta u-canonical then
# delta in CsetSelf(delta) u so psiSelf delta u FIRES and CsetSelf(delta+1)!=CsetSelf(delta)
# generally => psiSelf could JUMP. TEST: across the gap, does psiSelf STAY CONSTANT at
# subscript u  i.e. psiSelf c u == psiSelf gamma u  for ALL gamma in [c,eta]? (the plateau
# is genuinely flat in VALUE even though canonicity varies)
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
for r in (6,7):
    terms=[cn(t) for t in collect(r) if in_OT(t)]
    pool=terms
    seen=set(); n=0; flat=0; ex=[]
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)
            for u in range(0,4):
                if not(u<=w and selfcanon(u,eta) and (not selfcanon(u,pw))): continue
                key=(str(eta),w,u)
                if key in seen: continue
                seen.add(key); n+=1
                c=pw; pcu=psi(u,c); peu=psi(u,eta)
                # all gamma in [c,eta) have psiSelf gamma u == pcu (value-flat plateau)?
                gammas=[g for g in pool if le_t(c,g) and lt_term(g,eta)]
                isflat = all(psi(u,g)==pcu for g in gammas)
                if isflat: flat+=1
                elif len(ex)<3:
                    bad=[(str(g),str(psi(u,g))) for g in gammas if psi(u,g)!=pcu][:2]
                    ex.append((u,str(c),str(pcu),bad))
    print(f"rounds={r}: subA-A inst={n}  VALUE-FLAT gap (psiSelf .u const on [c,eta))={flat}/{n}")
    for u,c,pcu,bad in ex:
        print(f"     u={u} pcu={pcu} non-flat gamma(val): {bad}")
