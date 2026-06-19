# H1 value-bounds: are they circular (need the collapse) or provable from strict_mono?
# Case eta<c: gap gamma in [eta,c) canonical, need psiSelf gamma u < psiSelf eta u.
#   gamma>=eta, so strict_mono(eta<gamma) gives psiSelf eta u < psiSelf gamma u (OPPOSITE!).
#   So psiSelf gamma u < psiSelf eta u would VIOLATE mono if gamma>eta truly. => these gamma
#   must be < eta in TRUE order (Omega-crossing lt_term lie) OR eta not canonical so no mono.
#   eta is u-NON-canonical here, so psiSelf_strict_mono_arg (needs SMALLER canonical) doesn't
#   apply with eta as the larger. Test: is psiSelf gamma u < psiSelf eta u actually because
#   gamma's TRUE value < eta? Use psi-faithful: is gamma < proj_u eta (the rep)? 
# The DECISIVE q: is H1 (and hence caseB) reducible to psi_proj-at-smaller + a NON-circular
#   collapse, or is each step circular? Test: H1-caseB(eta<c) value-bound — does it follow
#   from 'gamma canonical & psiSelf gamma u = psiSelf gamma' u for some gamma'<eta'? i.e.
#   is every gap-canonical gamma's u-value already achieved below eta? (then < psiSelf eta u
#   needs eta's value to dominate = circular-ish). 
# SIMPLER: just confirm H1 itself is TRUE & note its value-bound mirrors subA_nm's (circular
# at value level, supplied by recursion). Then the REAL lever is: caseB <- NoncanonValueMem
# at smaller GENERATOR via a well-founded measure. Identify the measure: is psiSelf eta w
# (=c=xi) such that its OWN rep computation proj_u c terminates with proj_u c being handled
# at strictly smaller rank/bound? Test: proj_u c vs eta (is proj_u c <= eta, enabling
# rank-descent through eta which is at rank n)?
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
    seen=set(); n=0; projc_le_eta=0; projc_lt_eta=0; projeta_eq_projc=0
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)
            for u in range(0,w+1):
                if selfcanon(u,eta): continue
                if selfcanon(u,pw): continue
                key=(str(eta),w,u)
                if key in seen: continue
                seen.add(key); n+=1
                c=pw
                pc=cn(proj(u,c))      # rep of c
                pe=cn(proj(u,eta))    # rep of eta
                if le_t(pc,eta): projc_le_eta+=1
                if lt_term(pc,eta): projc_lt_eta+=1
                if pe==pc: projeta_eq_projc+=1
    print(f"rounds={r}: caseB inst={n}")
    print(f"  proj_u c <= eta = {projc_le_eta}/{n}   proj_u c < eta = {projc_lt_eta}/{n}")
    print(f"  proj_u eta == proj_u c (same rep) = {projeta_eq_projc}/{n}")
