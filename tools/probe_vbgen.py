# GENERAL value-bounded gap collapse (the Lean lemma to prove):
#   alpha<=beta, AND for all gamma in [alpha,beta):
#       gamma a-non-canonical  OR  psiSelf gamma a < psiSelf alpha a
#   =>  psiSelf alpha a = psiSelf beta a.
# Test over ARBITRARY alpha<beta pairs in the corpus (not just sub-case A), at subscript a.
# Also LOAD-BEARING: drop the value-bound (require only non-canonical) and check it then
# has counterexamples (= collapseSelf_le's hyp is strictly stronger / our hyp strictly weaker
# but still sound). And check the hyp is SATISFIABLE beyond the trivial all-non-canonical case.
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
    terms=sorted({cn(t) for t in collect(r) if in_OT(t)}, key=lambda z:(len(str(z)),str(z)))
    # limit pairs for tractability: sample
    pool=terms
    import itertools
    checked=0; hyp_holds=0; collapse_ok=0; collapse_fail=0
    # also: hyp with VALUE-BOUND but NOT all-noncanonical (the genuinely-new regime)
    newregime=0; newregime_ok=0
    N=len(terms)
    for a in range(0,3):
      cnt=0
      for i in range(0, N, max(1,N//120)):
        alpha=terms[i]
        pa=psi(a,alpha)
        for j in range(i+1, N, max(1,N//120)):
            beta=terms[j]
            if not lt_term(alpha,beta): continue
            cnt+=1
            if cnt>4000: break
            gam=[g for g in pool if le_t(alpha,g) and lt_term(g,beta)]
            # hyp: every gamma non-canonical OR psiSelf gamma a < psiSelf alpha a
            ok=True; has_canon=False
            for g in gam:
                if selfcanon(a,g):
                    has_canon=True
                    if not lt_term(psi(a,g),pa): ok=False; break
            checked+=1
            if ok:
                hyp_holds+=1
                if psi(a,alpha)==psi(a,beta): collapse_ok+=1
                else: collapse_fail+=1
                if has_canon:
                    newregime+=1
                    if psi(a,alpha)==psi(a,beta): newregime_ok+=1
    print(f"rounds={r}: checked pairs(sampled)={checked}")
    print(f"  hyp holds={hyp_holds}  collapse OK={collapse_ok}  collapse FAIL(viol)={collapse_fail}")
    print(f"  NEW regime (hyp holds WITH a canonical gap point)={newregime}  collapse OK={newregime_ok}")
