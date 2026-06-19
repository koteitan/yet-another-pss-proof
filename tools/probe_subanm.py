# NVM_subA_nm: psiSelf(psiSelf eta w) u  NOT in  CsetSelf(psiResSelf eta) eta u
# UNCONDITIONAL (no canonicity hyp on eta/w/u). Verify on the canonical fragment.
import sys
sys.path.insert(0,'.')
from valnorm import conv, nrm, lt_term, G, in_OT
from wfe_explore import translate, enum_ST
Z=()
def cn(x): return tuple(('D',vv,cn(bb)) for _,vv,bb in x)
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
    tot=0; viol=0
    seen=set()
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)           # psiSelf eta w
            for u in range(0,4):
                puw=psi(u,pw)       # psiSelf(psiSelf eta w) u
                key=(str(eta),w,u)
                if key in seen: continue
                seen.add(key); tot+=1
                # is puw in CsetSelf(eta,u)?  membership test via term_in
                if term_in(eta,u,puw): viol+=1
    print(f"rounds={r}: instances={tot}  subA_nm VIOLATIONS (puw in C_eta_u)={viol}")
