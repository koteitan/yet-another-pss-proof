# LOAD-BEARING: does caseB's EXISTENTIAL fail if we DROP key hyps? (subA_nm lesson:
# confirm the def is not silently provable from a weaker/false form.)
# Drop-1: drop 'eta in CsetSelf(alpha) v' (hηC). Then is there alpha,v,eta where the
#   conclusion (delta=proj_u eta in CsetSelf(alpha) v) FAILS? If yes, hηC load-bearing.
# Drop-2: drop 'psiSelf eta w < alpha' (hξα). delta=proj_u eta < alpha may fail.
# Also: confirm proj_u eta is the UNIQUE viable witness vs the value being realized by
#   a SMALLER canonical (would indicate the rep could be smaller, affecting recursion).
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
def memC(alpha,v,delta): return term_in(alpha,v,delta)
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
for r in (7,):
    terms=[cn(t) for t in collect(r) if in_OT(t)]; pool=terms
    seen=set()
    drop1_viol=0  # WITHOUT hηC: delta=proj_u eta NOT in CsetSelf(alpha) v
    drop1_n=0
    rep_eq_proj=0; rep_smaller=0; rep_n=0
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)
            for u in range(0,w+1):
                if not selfcanon(w,eta): continue
                if selfcanon(u,eta): continue
                if selfcanon(u,pw): continue
                d=cn(proj(u,eta))
                # uniqueness: minimal u-canonical realizer of psiSelf(pw) u
                target=psi(u,pw)
                reals=[g for g in pool if selfcanon(u,g) and psi(u,g)==target]
                if reals:
                    mn=reals[0]
                    for g in reals[1:]:
                        if lt_term(g,mn): mn=g
                    rep_n+=1
                    if mn==d: rep_eq_proj+=1
                    elif lt_term(mn,d): rep_smaller+=1
                # Drop-1 stress: alpha with eta<alpha, psiSelf eta w<alpha, but eta NOT in CsetSelf(alpha)v
                for v in range(0,u+1):
                    for alpha in pool[:80]:
                        if not lt_term(eta,alpha): continue
                        if not lt_term(pw,alpha): continue
                        if memC(alpha,v,eta): continue   # DROP hηC: take alpha where it FAILS
                        key=(str(eta),w,u,v,str(alpha))
                        if key in seen: continue
                        seen.add(key); drop1_n+=1
                        if not memC(alpha,v,d): drop1_viol+=1
    print(f"rounds={r}:")
    print(f"  rep uniqueness: minimal u-canon realizer == proj_u eta = {rep_eq_proj}/{rep_n}  (smaller={rep_smaller})")
    print(f"  DROP hηC stress: instances={drop1_n}  delta NOT in CsetSelf(alpha)v (=> hηC load-bearing)={drop1_viol}")
