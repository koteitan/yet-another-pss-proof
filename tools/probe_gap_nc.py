# crux via collapseSelf_le: need every gamma in [c, eta) u-non-canonical, c=psiSelf eta w.
# Then psiSelf c u = psiSelf eta u (collapseSelf_le eta c). TEST gap u-non-canonicity.
# WATCH: lt_term unfaithful at Omega-crossings. Use acanon (faithful) + term value order
# for the gap membership. The gap [c, eta): gamma with c<=gamma<eta. Among CORPUS canon
# terms. If any gamma in gap is u-CANONICAL => collapseSelf_le inapplicable (the IntervalNoncanon
# Omega-crossing trap). This is the SAME trap that killed the collapse face. TEST if it bites.
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
def noncanon_self(u,t): return not term_in(t,u,t)
# canonicity acanon(u,t) is the SELF test t in CsetSelf(t) u == term_in(t,u,t)
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
    terms=[cn(t) for t in collect(r) if in_OT(t)]
    pool=terms
    seen=set(); n=0; gap_clean=0; gap_has_canon=0; ex=[]
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)
            for u in range(0,4):
                if not(u<=w and selfcanon(u,eta) and (not selfcanon(u,pw))): continue
                key=(str(eta),w,u)
                if key in seen: continue
                seen.add(key); n+=1
                c=pw
                # gamma in corpus with c<=gamma<eta, gamma u-canonical?
                bad=[g for g in pool if le_t(c,g) and lt_term(g,eta) and selfcanon(u,g)]
                if bad:
                    gap_has_canon+=1
                    if len(ex)<3: ex.append((u,c,eta,[str(g) for g in bad[:3]]))
                else:
                    gap_clean+=1
    print(f"rounds={r}: subA-A inst={n}")
    print(f"  gap [c,eta) CLEAN (all u-non-canon) = {gap_clean}/{n}")
    print(f"  gap has a u-CANONICAL gamma (TRAP)  = {gap_has_canon}/{n}")
    for u,c,eta,b in ex:
        print(f"     u={u} canonical-in-gap (sample)={b}")
