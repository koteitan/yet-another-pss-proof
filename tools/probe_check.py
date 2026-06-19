# CRITICAL re-check: delta=proj_u(c), is psiSelf c u == psiSelf delta u with delta<c & delta canonical?
# If delta canonical AND delta<c then strict_mono => psiSelf delta u<psiSelf c u, CONTRADICTING ==.
# So EITHER delta is NOT canonical, OR delta is NOT < c, OR my == finding was wrong. Recheck all.
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
r=7
terms=[cn(t) for t in collect(r) if in_OT(t)]
seen=set(); n=0
d_canon=0; d_lt_c=0; d_eq_c=0; d_gt_c=0; val_eq=0; both_problem=0
for eta in terms:
    for w in range(0,4):
        pw=psi(w,eta)
        for u in range(0,w+1):
            if selfcanon(u,eta): continue
            if selfcanon(u,pw): continue
            key=(str(eta),w,u)
            if key in seen: continue
            seen.add(key); n+=1
            c=pw; d=cn(proj(u,c))
            if selfcanon(u,d): d_canon+=1
            if lt_term(d,c): d_lt_c+=1
            elif d==c: d_eq_c+=1
            else: d_gt_c+=1
            ve = (psi(u,c)==psi(u,d))
            if ve: val_eq+=1
            # the problematic combo: d canonical AND d<c AND psiSelf c u == psiSelf d u
            if selfcanon(u,d) and lt_term(d,c) and ve: both_problem+=1
print(f"inst={n}: d=proj_u c canonical={d_canon}  d<c={d_lt_c} d=c={d_eq_c} d>c={d_gt_c}")
print(f"  psiSelf c u == psiSelf d u = {val_eq}")
print(f"  PROBLEM (d canon & d<c & val_eq, would violate strict_mono) = {both_problem}")
