# Crux: psiSelf eta u <= psiSelf(psiSelf eta w) u. Try via opow formula:
# psiSelf alpha v = omega^(Om v + alpha) for v>=1, alpha<eps(Om v+1) (and v=0 variant).
# In range, psiSelf eta u = w^(Om u+eta), psiSelf c u = w^(Om u + c) where c=psiSelf eta w.
# Crux <=> Om u+eta <= Om u + c <=> eta <= c = psiSelf eta w.
# So CRUX  <=>  eta <= psiSelf eta w  (when in opow range)!  TEST: eta <= psiSelf eta w?
# That's AcanonLtValue-flavoured (eta < psiSelf eta w) but at subscript w with eta u-canon.
# Recall AcanonLtValue is FALSE above eps (Om_{w+1}). So eta<=psiSelf eta w may FAIL.
# But we're in sub-case A where psiSelf eta w is u-NON-canonical, i.e. >= Om_{w+1} band...
# subA_le gives Om_{w+1} <= eta. Then eta >= Om_{w+1} > psiSelf eta w?? Let's test all:
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
    seen=set(); n=0; eta_le_c=0; eta_lt_c=0; eta_eq_c=0
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)
            for u in range(0,4):
                if not(u<=w and (not noncanon_self(u,eta)) and noncanon_self(u,pw)): continue
                key=(str(eta),w,u)
                if key in seen: continue
                seen.add(key); n+=1
                c=pw
                if le_t(eta,c): eta_le_c+=1
                if lt_term(eta,c): eta_lt_c+=1
                if eta==c: eta_eq_c+=1
    print(f"rounds={r}: inst={n}  eta<=c={eta_le_c}  eta<c={eta_lt_c}  eta==c={eta_eq_c}")
