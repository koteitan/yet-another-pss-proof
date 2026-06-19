# KEY non-circular route for PP(x,u): psiSelf x u = psiSelf delta u (delta=proj_u x, x<=delta).
# Via psiSelf_eq_of_notMem: psiSelf x u NOT in CsetSelf(delta) u.
# M1 canonical witness would be xi<delta, xi canon, psiSelf xi u = psiSelf x u.
# CLAIM (non-circular): NO canonical xi < delta has psiSelf xi u = psiSelf x u, because the
#   MINIMAL canonical realizer of psiSelf x u is delta itself (proj_u x = delta, and delta is
#   the least canonical with that value). So the witness can't exist => non-membership => collapse.
# This needs: "delta = proj_u x is the LEAST u-canonical with psiSelf . u = psiSelf x u".
# TEST: is there a canonical xi < delta with psiSelf xi u = psiSelf x u? (should be 0 = no realizer below)
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
for r in (5,6,7):
    terms=[cn(t) for t in collect(r) if in_OT(t)]; pool=terms
    seen=set(); n=0; has_realizer_below=0; ex=[]
    for x in terms:
        for u in range(0,4):
            if selfcanon(u,x): continue
            d=cn(proj(u,x)); px=psi(u,x)
            key=(str(x),u)
            if key in seen: continue
            seen.add(key); n+=1
            # canonical xi < delta with psiSelf xi u = psiSelf x u ?
            real=[xi for xi in pool if lt_term(xi,d) and selfcanon(u,xi) and psi(u,xi)==px]
            if real:
                has_realizer_below+=1
                if len(ex)<3: ex.append((u,str(x),str(d),str(real[0])))
    print(f"rounds={r}: PP instances={n}")
    print(f"  canonical xi < delta=proj_u x with psiSelf xi u = psiSelf x u (BREAKS non-circular route) = {has_realizer_below}/{n}")
    for u,x,d,xi in ex: print(f"    u={u} x={x} delta={d} xi={xi}")
