# psi_proj at x: psiSelf x u = psiSelf(proj_u x)u, x<=proj_u x, via collapseSelf_le_valuebounded
# x (proj_u x): value-bound canonical gamma in [x, proj_u x) => psiSelf gamma u < psiSelf x u.
# x is u-non-canonical. gamma canonical. Is psiSelf gamma u < psiSelf x u?
# This is the SAME value-bound shape as before -- check if circular or free.
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
    terms=[cn(t) for t in collect(r) if in_OT(t)]; pool=terms
    seen=set(); n=0; vb_eta=0; vb_c=0
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
                de=cn(proj(u,eta)); dc=cn(proj(u,c))
                peu=psi(u,eta); pcu=psi(u,c)
                ge=[g for g in pool if le_t(eta,g) and lt_term(g,de) and selfcanon(u,g)]
                if all(lt_term(psi(u,g),peu) for g in ge): vb_eta+=1
                gc=[g for g in pool if le_t(c,g) and lt_term(g,dc) and selfcanon(u,g)]
                if all(lt_term(psi(u,g),pcu) for g in gc): vb_c+=1
    print(f"rounds={r}: inst={n}")
    print(f"  psi_proj@eta value-bound (gamma in [eta,proj_u eta) canon: psiSelf gamma u<psiSelf eta u)={vb_eta}/{n}")
    print(f"  psi_proj@c   value-bound (gamma in [c,proj_u c) canon: psiSelf gamma u<psiSelf c u)    ={vb_c}/{n}")
