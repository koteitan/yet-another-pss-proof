# H1 via the rep delta=proj_u eta (u-canonical, psiSelf delta u = psiSelf eta u).
# H1: psiSelf eta u = psiSelf(psiSelf eta w) u, i.e. psiSelf delta u = psiSelf c u (c=psiSelf eta w).
# Apply collapseSelf_le_valuebounded between delta and c (whichever order), value-bound via
# strict_mono on canonicals < the larger. Since delta is u-canonical:
#  - if c <= delta: collapse [c,delta] target psiSelf c u; need gap canon gamma: psiSelf gamma u<psiSelf c u
#  - if delta <= c: collapse [delta,c] target psiSelf delta u; gap canon gamma: psiSelf gamma u<psiSelf delta u
#    and gamma<delta? no gamma in [delta,c). Hmm gamma>=delta. strict_mono wrong way again.
# The CLEAN one: delta u-canonical. For ANY canonical gamma, gamma<delta <=> psiSelf gamma u<psiSelf delta u
#   (strict_mono both ways via injectivity). So value-bound 'psiSelf gamma u<psiSelf delta u'
#   <=> gamma<delta (for canonical gamma). 
# TEST: relationship delta=proj_u eta vs c=psiSelf eta w, and whether the gap canonicals
#   between them are all < delta (making the value-bound FREE via strict_mono to delta).
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
def proj(u,t):
    while True:
        bad=[x for x in G(u,t) if not lt_term(x,t)]
        if not bad: return t
        t=maxo(bad)
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
    seen=set(); n=0
    c_le_delta=0; delta_le_c=0
    # value-bound for collapse [min(c,delta), max(c,delta)] target psiSelf(min) u, via gamma<delta:
    vb_free=0   # all gap canon gamma have gamma < delta (=> psiSelf gamma u<psiSelf delta u free)
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)
            for u in range(0,w+1):
                if selfcanon(u,eta): continue
                if selfcanon(u,pw): continue
                key=(str(eta),w,u)
                if key in seen: continue
                seen.add(key); n+=1
                c=pw; d=cn(proj(u,eta))
                lo,hi=(c,d) if le_t(c,d) else (d,c)
                gam=[g for g in pool if le_t(lo,g) and lt_term(g,hi) and selfcanon(u,g)]
                # value-bound holds via strict_mono if every gap canon gamma < d (the rep)
                if all(lt_term(g,d) for g in gam): vb_free+=1
                if le_t(c,d): c_le_delta+=1
                else: delta_le_c+=1
    print(f"rounds={r}: caseB inst={n}  c<=delta={c_le_delta} delta<c={delta_le_c}")
    print(f"  gap canonicals all < delta=proj_u eta (=> value-bound FREE via strict_mono) = {vb_free}/{n}")
