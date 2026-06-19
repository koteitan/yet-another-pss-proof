# Design caseB's recursion. delta=proj_u eta. Key value-identity chain to establish:
#   psiSelf(psiSelf eta w) u  =?=  psiSelf eta u  =?=  psiSelf (proj_u eta) u = psiSelf delta u
# Test the two halves:
#  H1: psiSelf(psiSelf eta w) u == psiSelf eta u   (the plateau, = subA_nm crux but here
#      eta is u-NON-canonical so subA_nm route differs; still test)
#  H2: psiSelf eta u == psiSelf (proj_u eta) u     (= psi_proj at eta, subscript u:
#      proj_u eta is the u-canonical rep of eta, value-preserving). THIS is the IH content
#      (the value-identity for the SMALLER datum eta, supplied by IH(eta)).
# If H1 and H2 both hold, caseB's value-id = H1 . H2 (compose), with delta=proj_u eta.
#  H2 is exactly NoncanonValueMem/psi_proj AT eta (smaller bound) = the OUTER IH.
#  H1 is the subscript-collapse psiSelf(psiSelf eta w) u = psiSelf eta u (w>=u).
import sys
sys.path.insert(0,'.')
from valnorm import conv, nrm, lt_term, G, in_OT
from wfe_explore import translate, enum_ST
Z=()
def cn(x): return tuple(('D',vv,cn(bb)) for _,vv,bb in x)
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
for r in (5,6,7):
    terms=[cn(t) for t in collect(r) if in_OT(t)]
    seen=set(); n=0; h1=0; h2=0; both=0
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)
            for u in range(0,w+1):
                if not selfcanon(w,eta): continue
                if selfcanon(u,eta): continue
                if selfcanon(u,pw): continue
                key=(str(eta),w,u)
                if key in seen: continue
                seen.add(key); n+=1
                d=cn(proj(u,eta))
                peu=psi(u,eta)
                H1 = (psi(u,pw)==peu)          # psiSelf(psiSelf eta w)u == psiSelf eta u
                H2 = (peu==psi(u,d))           # psiSelf eta u == psiSelf(proj_u eta) u
                if H1: h1+=1
                if H2: h2+=1
                if H1 and H2: both+=1
    print(f"rounds={r}: caseB inst={n}  H1(c-collapse)={h1}/{n}  H2(psi_proj@eta)={h2}/{n}  both={both}/{n}")
