# Full caseB with alpha quantified. For each (eta,w,u) instance and each alpha in corpus
# with eta<alpha AND psiSelf eta w<alpha AND eta in CsetSelf(alpha) v (for some v<=u):
#   delta=proj_u eta must satisfy: delta<alpha, delta in CsetSelf(alpha) v, delta u-canon,
#   psiSelf delta u = psiSelf(psiSelf eta w) u.
# Test the FULL existential is satisfiable by proj_u eta. Also LOAD-BEARING: check whether
# dropping 'eta in CsetSelf(eta) w' (the w-canonical hyp) or 'eta in CsetSelf(alpha) v'
# admits a counterexample (def under-hypothesized like subA_nm was).
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
def memC(alpha,v,delta): return term_in(alpha,v,delta)   # delta in CsetSelf(alpha) v
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
    pool=terms
    seen=set(); ninst=0; ok=0; bad_examples=[]
    delta_lt_alpha_fail=0; delta_inC_fail=0
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)
            for u in range(0,w+1):
                if not selfcanon(w,eta): continue       # eta w-canonical
                if selfcanon(u,eta): continue           # eta u-NON-canonical
                if selfcanon(u,pw): continue            # pw u-non-canonical
                d=cn(proj(u,eta))
                # iterate alpha & v
                for v in range(0,u+1):
                    for alpha in pool:
                        if not lt_term(eta,alpha): continue       # eta<alpha
                        if not lt_term(pw,alpha): continue        # psiSelf eta w<alpha
                        if not memC(alpha,v,eta): continue        # eta in CsetSelf(alpha) v
                        key=(str(eta),w,u,v,str(alpha))
                        if key in seen: continue
                        seen.add(key); ninst+=1
                        c1 = lt_term(d,alpha)
                        c2 = memC(alpha,v,d)
                        c3 = selfcanon(u,d)
                        c4 = (psi(u,d)==psi(u,pw))
                        if c1 and c2 and c3 and c4: ok+=1
                        else:
                            if not c1: delta_lt_alpha_fail+=1
                            if not c2: delta_inC_fail+=1
                            if len(bad_examples)<3:
                                bad_examples.append((v,u,w,str(eta),str(alpha),c1,c2,c3,c4))
                        if ninst>200000: break
                    if ninst>200000: break
    print(f"rounds={r}: full caseB instances (alpha quantified)={ninst}")
    print(f"  delta=proj_u eta satisfies ALL 4 conclusion conjuncts = {ok}/{ninst}")
    print(f"  delta<alpha fails={delta_lt_alpha_fail}  delta in CsetSelf(alpha)v fails={delta_inC_fail}")
    for b in bad_examples: print("   BAD:",b)
