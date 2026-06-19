# In sub-case A (eta u-canon, u<=w, psiSelf eta w u-non-canon), what is the proof
# structure of  psiSelf(psiSelf eta w) u  NOT in CsetSelf(eta) u ?
# Candidate facts to use:
#  F1: psiSelf eta u == psiSelf eta w   (the plateau: eta's value is u-w-constant here)
#  F2: psiSelf eta w >= eta ? or <= eta (hle says <=)
#  F3: psiSelf(psiSelf eta w) u == psiSelf eta u  (the GOAL via psiSelf_eq_of_notMem)
#  F4: eta u-canonical => psiSelf eta u NOT in CsetSelf(eta) u (psiSelf_notMem at eta)
#      and psiSelf eta u ... relationship to puw.
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
    seen=set()
    n=0; f1=0; f3=0; hle_ok=0; puw_eq_psiEtaU=0
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)
            for u in range(0,4):
                if not(u<=w and (not noncanon_self(u,eta)) and noncanon_self(u,pw)): continue
                key=(str(eta),w,u)
                if key in seen: continue
                seen.add(key); n+=1
                peu=psi(u,eta)        # psiSelf eta u
                puw=psi(u,pw)         # psiSelf(psiSelf eta w) u
                if peu==pw: f1+=1     # F1 plateau psiSelf eta u == psiSelf eta w
                if puw==peu: f3+=1    # F3 goal value-equality
                if le_t(pw,eta): hle_ok+=1
    print(f"rounds={r}: subA-A instances={n}")
    print(f"  F1 psiSelf eta u == psiSelf eta w        = {f1}/{n}")
    print(f"  F3 psiSelf(psiSelf eta w)u==psiSelf eta u= {f3}/{n}")
    print(f"  hle psiSelf eta w <= eta                 = {hle_ok}/{n}")
