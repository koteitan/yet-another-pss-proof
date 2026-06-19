# H1: psiSelf(psiSelf eta w) u == psiSelf eta u, for w>=u, eta u-non-canonical,
#     psiSelf eta w u-non-canonical. Find its provability / right hypotheses.
# Candidate route via collapseSelf_le_valuebounded or psiSelf_eq_of_notMem:
#   psiSelf(psiSelf eta w) u = psiSelf eta u. Let c=psiSelf eta w. We have c<=eta? (eta
#   u-non-canon => not directly). Test c vs eta and the needed direction.
# Sub-questions:
#  Q-le: c=psiSelf eta w  <=  eta ?  (needed to apply collapseSelf_le_valuebounded c..eta)
#  Q-vb: value-bound: every u-canon gamma in [c,eta) has psiSelf gamma u < psiSelf c u?
#  Also test H1 UNCONDITIONALLY and under fewer hyps (load-bearing / not silently false).
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
    seen=set()
    # context: w>=u, eta u-non-canon, c=pw u-non-canon (the caseB sub-context; eta may be w-canon or not)
    n=0; qle=0; qvb=0; h1=0
    # ALSO unconditional-ish: just w>=u (drop canonicity hyps) -> count H1 viols
    nu=0; h1u=0
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)
            for u in range(0,w+1):
                pwu=psi(u,pw); peu=psi(u,eta)
                # unconditional (only w>=u)
                nu+=1
                if pwu==peu: h1u+=1
                # caseB context
                if selfcanon(u,eta): continue       # eta u-NON-canon
                if selfcanon(u,pw): continue          # pw u-non-canon
                key=(str(eta),w,u)
                if key in seen: continue
                seen.add(key); n+=1
                if pwu==peu: h1+=1
                if le_t(pw,eta): qle+=1
                gam=[g for g in pool if le_t(pw,g) and lt_term(g,eta) and selfcanon(u,g)]
                if all(lt_term(psi(u,g),pwu) for g in gam): qvb+=1
    print(f"rounds={r}:")
    print(f"  H1 UNCONDITIONAL (only w>=u): {h1u}/{nu}  (low => needs hyps)")
    print(f"  caseB-context inst={n}: H1={h1}/{n}  Q-le(c<=eta)={qle}/{n}  Q-vb(value-bound)={qvb}/{n}")
