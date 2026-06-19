# H1: psiSelf eta u = psiSelf c u. c<=delta? NO earlier c<=delta (884/884, c<=delta).
# Wait: earlier probe_H1_via_rep: c<=delta 884/884. And delta=proj_u eta. And gap(delta,eta]
# and (delta,c] non-canon. So BOTH eta and c are in (delta, ...]. Order of eta vs c:
#   we had c<=eta (subA region) mixed. Let me get eta vs c and the DIRECT collapse:
#   collapseSelf_le between min(eta,c) and max(eta,c): gap [min,max) non-canonical?
#   Since both >delta and (delta,max] all non-canon, [min,max) subset (delta,max] => non-canon
#   EXCEPT min itself: is min u-canonical? min in {eta,c} both u-NON-canonical (hyps)! 
#   So [min,max) : min is non-canon (good), and (min,max) subset (delta,max] non-canon. CLEAN!
#   => collapseSelf_le max min (min<=max) (gap [min,max) all u-non-canon) gives
#      psiSelf min u = psiSelf max u = H1.  NO value-bound needed, PLAIN collapseSelf_le!
# Verify: gap [min(eta,c), max(eta,c)) ALL u-non-canonical.
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
    seen=set(); n=0; gap_clean=0; eta_lt_c=0; c_lt_eta=0; eq=0
    for eta in terms:
        for w in range(0,4):
            pw=psi(w,eta)
            for u in range(0,w+1):
                if selfcanon(u,eta): continue
                if selfcanon(u,pw): continue
                key=(str(eta),w,u)
                if key in seen: continue
                seen.add(key); n+=1
                c=pw
                if c==eta: eq+=1; gap_clean+=1; continue
                lo,hi=(eta,c) if lt_term(eta,c) else (c,eta)
                if lt_term(eta,c): eta_lt_c+=1
                else: c_lt_eta+=1
                # gap [lo, hi) all u-non-canonical? (lo itself u-non-canon by hyp; check interior)
                gap=[g for g in pool if le_t(lo,g) and lt_term(g,hi) and selfcanon(u,g)]
                if not gap: gap_clean+=1
    print(f"rounds={r}: inst={n}  eta<c={eta_lt_c} c<eta={c_lt_eta} eq={eq}")
    print(f"  gap [min(eta,c),max(eta,c)) ALL u-non-canon (=> H1 via PLAIN collapseSelf_le) = {gap_clean}/{n}")
