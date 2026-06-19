# ALTERNATIVE recursion: the value needing a rep is psiSelf(psiSelf eta w) u, where
# c=psiSelf eta w is u-non-canonical and c<alpha (hξα). Try delta' = proj_u c (rep of c).
# Then psi_proj at c (subscript u): psiSelf(proj_u c) u = psiSelf c u = psiSelf(psiSelf eta w)u.
# This is psi_proj/NoncanonValueMem AT c (c<alpha) = the OUTER IH at c directly! No H1 needed.
# Test: delta' = proj_u(psiSelf eta w): value-identity psiSelf delta' u == psiSelf(psiSelf eta w)u,
#   delta' u-canonical, delta' < alpha (need delta'<=c<alpha or delta'<alpha).
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
    seen=set(); n=0; valid=0; ucanon=0; dlt_c=0; dle_c=0
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
                dp=cn(proj(u,c))    # delta' = proj_u(psiSelf eta w)
                if psi(u,dp)==psi(u,c): valid+=1   # value-identity (= psi_proj at c)
                if selfcanon(u,dp): ucanon+=1
                if le_t(dp,c): dle_c+=1             # delta' <= c (so < alpha since c<alpha)
    print(f"rounds={r}: caseB inst={n}")
    print(f"  delta'=proj_u(psiSelf eta w): value-id psiSelf delta' u==psiSelf c u = {valid}/{n}")
    print(f"  delta' u-canonical = {ucanon}/{n}   delta' <= c (=>delta'<alpha) = {dle_c}/{n}")
