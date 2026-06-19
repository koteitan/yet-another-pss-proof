# FINAL: the single maxo-step psiSelf x u = psiSelf g u, g=proj_u x = maxo-violator,
#   g u-canonical, g a G_u-SUBTERM of x (tsize smaller). 
# At the ORDINAL level (joint induction), x is an arbitrary ordinal in CsetSelf, NOT a term.
#   "maxo-violator g" / "G_u(x)" require x to be oV-of-a-term. The ordinal psiSelf eta w in
#   caseB is NOT obviously oV-of-a-wf3-term with accessible G_u.
# DECISIVE QUESTION: at the ordinal level, the single step needs NoRealizer(x,g,u) which =
#   PP(x). The recursion order: g is a SUBTERM (tsize smaller) IF x is a term. The joint
#   induction is on ORDINALS (alpha,n), where the "smaller" elements are arguments of
#   GENERATORS (psiSelf zeta v with zeta<alpha), NOT G_u-coefficients/subterms.
# So: is g=proj_u x reachable as a GENERATOR-ARGUMENT at smaller bound/rank in CsetSelf(alpha)?
#   g u-canonical, g=proj_u x. In caseB x=psiSelf eta w. g=proj_u(psiSelf eta w)=proj_u eta
#   (shared rep). proj_u eta: is it < alpha? < eta? Test g=proj_u eta vs eta (the rank-n elt).
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
for r in (6,7):
    terms=[cn(t) for t in collect(r) if in_OT(t)]
    seen=set(); n=0; g_lt_eta=0; g_gt_eta=0; g_eq_eta=0; g_lt_c=0; g_gt_c=0
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)
            for u in range(0,w+1):
                if selfcanon(u,eta): continue
                if selfcanon(u,pw): continue
                key=(str(eta),w,u)
                if key in seen: continue
                seen.add(key); n+=1
                g=cn(proj(u,eta))   # = proj_u(psiSelf eta w) = the rep
                if lt_term(g,eta): g_lt_eta+=1
                elif g==eta: g_eq_eta+=1
                else: g_gt_eta+=1
                if lt_term(g,pw): g_lt_c+=1
                elif lt_term(pw,g): g_gt_c+=1
    print(f"rounds={r}: caseB inst={n}")
    print(f"  rep g=proj_u eta  vs eta:  g<eta={g_lt_eta} g=eta={g_eq_eta} g>eta={g_gt_eta}")
    print(f"  rep g vs c=psiSelf eta w:  g<c={g_lt_c} g>c={g_gt_c}")
