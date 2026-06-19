# subA_nm consumed at line 1074 WITH hle: psiSelf eta w <= eta. Test under that hyp.
# Also test the EVEN sharper context (sub-case A): eta u-canonical, u<=w,
#   psiSelf eta w u-non-canonical.
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
def noncanon_self(u,t):
    # t u-non-canonical means t NOT in CsetSelf(t) u  ==  exists violating principal
    return not term_in(t,u,t)
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
    seen=set()
    # context 1: only hle (psiSelf eta w <= eta)
    c1=0; c1v=0
    # context 2: full sub-case A
    c2=0; c2v=0
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)
            hle = le_t(pw,eta)
            for u in range(0,4):
                key=(str(eta),w,u)
                if key in seen: continue
                seen.add(key)
                puw=psi(u,pw)
                inC = term_in(eta,u,puw)   # violation if True
                if hle:
                    c1+=1
                    if inC: c1v+=1
                # full sub-case A: u<=w, eta u-canonical, pw u-non-canonical
                if u<=w and (not noncanon_self(u,eta)) and noncanon_self(u,pw):
                    c2+=1
                    if inC: c2v+=1
    print(f"rounds={r}: ctx1(hle only) inst={c1} viol={c1v} | ctx2(full subA) inst={c2} viol={c2v}")
