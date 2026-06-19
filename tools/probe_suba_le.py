# subA_le: eta u-canon, u<=w, psiSelf eta w u-non-canon  =>  Om(w+1) <= eta.
# Its docstring: "a u-canonical eta < Om_{w+1} makes psiSelf eta w u-canonical".
# Test: is subA_le reducible to a CLEAN band fact (no collapse), i.e.
#   eta < Om_{w+1}  =>  psiSelf eta w  is u-canonical (contrapositive)?
# Model Om(k) as a term ('D',k,()). eta < Om(w+1) means eta's lead subscript <= w.
import sys
sys.path.insert(0,'.')
from valnorm import conv, nrm, lt_term, G, in_OT
from wfe_explore import translate, enum_ST
Z=()
def cn(x): return tuple(('D',vv,cn(bb)) for _,vv,bb in x)
def le_t(a,b): return a==b or lt_term(a,b)
def Om(k): return (('D',k,()),)
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
    seen=set(); n=0; concl=0; lt_Omw1=0
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)
            for u in range(0,4):
                if not(u<=w and (not noncanon_self(u,eta)) and noncanon_self(u,pw)): continue
                key=(str(eta),w,u)
                if key in seen: continue
                seen.add(key); n+=1
                # conclusion Om(w+1) <= eta
                if le_t(Om(w+1),eta): concl+=1
                if lt_term(eta,Om(w+1)): lt_Omw1+=1
    print(f"rounds={r}: subA-A inst={n}  concl Om(w+1)<=eta={concl}/{n}  eta<Om(w+1)={lt_Omw1}")
