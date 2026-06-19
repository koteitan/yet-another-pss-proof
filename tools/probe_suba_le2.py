# In sub-case A, where is eta relative to bands? subA_le concl: Om(w+1)<=eta.
# We confirmed eta>=Om(w+1) (623/623). So eta is ABOVE Om(w+1) -- WAY above epsLvl w
# (since epsLvl w = eps(Om w+1) < Om(w+1) <= eta). So eta is in the deep collapse region,
# OPOW FORMULA (range alpha<eps(Om u+1)) does NOT apply to eta at subscript u either
# (eta >= Om(w+1) > eps(Om u+1) for u<=w). CONFIRM: eta >= Om(u+1) too (so psiSelf eta u
# is also out of clean opow range as a function of eta).
# This means BOTH subA_le and subA_nm/crux are in the region where the opow lever is dead.
# Print the band structure to confirm the obstruction is real.
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
for r in (7,):
    terms=[cn(t) for t in collect(r) if in_OT(t)]
    seen=set(); n=0; eta_ge_Omu1=0; eta_ge_Omw1=0
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)
            for u in range(0,4):
                if not(u<=w and (not noncanon_self(u,eta)) and noncanon_self(u,pw)): continue
                key=(str(eta),w,u)
                if key in seen: continue
                seen.add(key); n+=1
                if le_t(Om(u+1),eta): eta_ge_Omu1+=1
                if le_t(Om(w+1),eta): eta_ge_Omw1+=1
    print(f"rounds={r}: inst={n}  eta>=Om(u+1)={eta_ge_Omu1}  eta>=Om(w+1)={eta_ge_Omw1}")
