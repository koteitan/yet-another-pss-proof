# Single maxo-step as carried-hyp lemma. PP_step(x,g,u): x<=g, g u-canonical,
#   NO canonical xi<g with psiSelf xi u = psiSelf x u  =>  psiSelf x u = psiSelf g u.
# PROOF (check it's complete & non-circular):
#  psiSelf_eq_of_notMem(x<=g): suffices psiSelf x u ∉ CsetSelf(g) u.
#  Suppose ∈. M1/CsetSelf_witness_canonical: ∃ canonical xi<g, psiSelf xi u = psiSelf x u.
#    (band forces subscript u). DIRECTLY contradicts the no-realizer hypothesis. DONE.
#  => PP_step is GREEN given the no-realizer hyp. NO circularity in the PROOF.
# So the residue is: "no canonical xi<g realizes psiSelf x u" =: NoRealizer(x,g,u).
# NOW: is NoRealizer derivable in the recursion? It's about the value psiSelf x u and
#   canonical xi<g. Since g=proj_u x is the rep and g canonical:
#   if psiSelf xi u = psiSelf x u with xi canonical, and IF psiSelf x u = psiSelf g u (PP),
#   then psiSelf xi u = psiSelf g u, xi,g canonical => xi=g (inj), contra xi<g. 
#   => NoRealizer follows from PP(x) = CIRCULAR (PP is what we prove).
#   BUT in the INDUCTION: PP(x) is proven from PP at smaller (the proj of subterms). Is
#   NoRealizer(x,g,u) derivable from PP at SMALLER args (not PP(x))?
# DECISIVE final test: a hypothetical realizer xi<g canonical with psiSelf xi u=psiSelf x u.
#   xi's value = psiSelf x u. Is xi NECESSARILY = g (forcing contra) WITHOUT assuming PP(x)?
#   xi canonical, psiSelf xi u = psiSelf x u. The canonical realizer of psiSelf x u is UNIQUE
#   (psiSelf_canonical_inj: two canonicals with same value are equal). So ANY canonical
#   realizer = the UNIQUE one. g IS a canonical realizer (psiSelf g u = psiSelf x u = PP... 
#   circular to assert g realizes). 
# Hmm. The uniqueness gives: at most ONE canonical xi has psiSelf xi u = psiSelf x u. Call it R
#   (the rep, EXISTS since values are realized). NoRealizer says R >= g. And g=proj_u x.
#   Is R = proj_u x = g? That's "the unique canonical realizer of psiSelf x u is proj_u x" =
#   PP(x) essentially. TEST whether R (unique canonical realizer) == g, computed independently:
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
    terms=[cn(t) for t in collect(r) if in_OT(t)]; pool=terms
    seen=set(); n=0; R_eq_g=0; R_exists=0
    for x in terms:
        for u in range(0,4):
            bad=[gg for gg in G(u,x) if not lt_term(gg,x)]
            if not bad: continue
            g=cn(maxo([cn(b) for b in bad])); px=psi(u,x)
            key=(str(x),u)
            if key in seen: continue
            seen.add(key); n+=1
            # unique canonical realizer R of px in pool
            R=[xi for xi in pool if selfcanon(u,xi) and psi(u,xi)==px]
            if R:
                R_exists+=1
                if g in R: R_eq_g+=1   # g is the (a) canonical realizer
    print(f"rounds={r}: inst={n}  canonical realizer of psiSelf x u exists in pool={R_exists}")
    print(f"  g=maxo-viol IS a canonical realizer of psiSelf x u = {R_eq_g}/{n}  (= PP content)")
