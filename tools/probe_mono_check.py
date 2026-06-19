# DECISIVE: does the term model respect psiSelf monotonicity on OT canonical inputs?
# psiSelf_mono_arg (Lean, ground truth): a <= b  =>  psiSelf a u <= psiSelf b u.
# Test in model: for OT terms a,b with le_term(a,b), is le_term(psi(u,a), psi(u,b))?
# If this FAILS, the model's psi/lt_term is unfaithful and the "623/623 hVB" was bogus.
import sys; sys.path.insert(0,'.')
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
for r in (7,):
    terms=[cn(t) for t in collect(r) if in_OT(t)]
    mono_viol=0; tot=0
    for i,a in enumerate(terms):
        for b in terms:
            if not le_t(a,b): continue
            for u in range(0,3):
                tot+=1
                pa=psi(u,a); pb=psi(u,b)
                if not le_t(pa,pb):
                    mono_viol+=1
                    if mono_viol<=5:
                        print(f"  MONO VIOL u={u}: a<=b but psi(u,a) NOT<= psi(u,b)")
    print(f"rounds={r}: psiSelf-mono checks={tot}  VIOLATIONS={mono_viol}")
