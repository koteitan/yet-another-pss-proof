# VB(x,u) := for all u-canonical gamma in [x, proj_u x): psiSelf gamma u < psiSelf x u.
# (x u-non-canonical; proj_u x >= x is the rep.)
# Equivalent reformulation (the actual content): for u-canonical gamma with
#   x <= gamma < proj_u x,  psiSelf gamma u < psiSelf x u.
# Since gamma >= x and gamma canonical, gamma != x (x non-canon). strict_mono(gamma vs proj_u x,
# both... no proj_u x is the rep). The circular issue: psiSelf gamma u vs psiSelf x u.
#
# RECURSION ORDER in noncanonValueMem_joint: OUTER well-founded on bound alpha, INNER on
# rank n. VB(x,u) is needed when x is a generator at rank n+1 (x=psiSelf eta w) or the
# datum eta. The IH gives facts for: (a) all beta<alpha [outer], (b) all elements at rank<=n
# in CsetSelf(alpha) [inner IHn].
#
# DECISIVE TEST: is VB(x,u) derivable from VB(x',u') for x' STRICTLY SMALLER (x'<x as
# ordinals, since the rank/bound both ultimately bound by ordinal size)? I.e. does
#   VB(x,u)  follow from  { VB(gamma', u) : gamma' < x, gamma' relevant } ?
# Reformulate VB(x,u) NON-circularly: psiSelf gamma u < psiSelf x u for canonical gamma in
# [x, proj_u x). KEY INSIGHT to test: gamma canonical & gamma >= x & gamma < proj_u x.
# Claim: such gamma has psiSelf gamma u < psiSelf x u BECAUSE gamma's u-value is realized
# BELOW x. Test: for these gamma, is psiSelf gamma u = psiSelf gamma' u for some gamma' < x
# canonical? (then psiSelf gamma u = psiSelf gamma' u < psiSelf x u by... mono? gamma'<x).
# Actually psiSelf gamma' u for gamma'<x: if gamma' canonical, psiSelf gamma' u < psiSelf x u?
# needs x's behavior. Let me TEST the core preservation claim directly:
#   PRES: for u-canonical gamma in [x, proj_u x), does psiSelf gamma u < psiSelf x u follow
#   from "gamma in CsetSelf(x) u"?  i.e. is gamma in the u-closure of x (then strict_mono_mem
#   gives psiSelf gamma u < psiSelf x u)?  TEST gamma in CsetSelf(x) u.
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
    terms=[cn(t) for t in collect(r) if in_OT(t)]; pool=terms
    # x ranges over u-non-canonical terms (the VB subjects)
    seen=set(); ngam=0
    gam_in_Cx=0      # gamma in CsetSelf(x) u  (=> strict_mono_mem gives psiSelf gamma u<psiSelf x u, NON-circular!)
    gam_notin=0
    ex=[]
    for x in terms:
        for u in range(0,4):
            if selfcanon(u,x): continue   # x must be u-non-canonical
            px=cn(proj(u,x))
            gam=[g for g in pool if le_t(x,g) and lt_term(g,px) and selfcanon(u,g)]
            for g in gam:
                ngam+=1
                # is gamma in CsetSelf(x) u? (the u-closure of x, bound x)
                if memC(x,u,g): gam_in_Cx+=1
                else:
                    gam_notin+=1
                    if len(ex)<3: ex.append((u,str(x),str(g)))
    print(f"rounds={r}: VB gap-canonical gamma instances={ngam}")
    print(f"  gamma in CsetSelf(x) u (=> psiSelf gamma u<psiSelf x u via strict_mono_mem, NON-CIRCULAR) = {gam_in_Cx}/{ngam}")
    print(f"  gamma NOT in CsetSelf(x) u = {gam_notin}")
    for u,x,g in ex: print(f"    u={u} x={x} gamma={g}")
