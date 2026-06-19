# Is C_u(oV x) == C_u(oV g) as FULL sets? (Buchholz Remark: omitting canonicity doesn't change C,
# but here x->g is value-change, not canonicity-omission). Test full-set equality + the
# monotone direction C_u(oV x) ⊆ C_u(oV g) [oV x<=oV g, larger bound = bigger closure].
# Faithful: membership via term_in (generator-trace). Test over corpus elements (both directions).
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
for r in (6,7):
    terms=[cn(t) for t in collect(r) if in_OT(t)]; pool=terms
    seen=set(); n=0; subset_xg=0; full_eq=0; eq_below_T=0
    for x in terms:
        for u in range(0,4):
            bad=[gg for gg in G(u,x) if not lt_term(gg,x)]
            if not bad: continue
            g=cn(maxo([cn(b) for b in bad]))
            key=(str(x),u)
            if key in seen: continue
            seen.add(key); n+=1
            T=psi(u,g)
            sub=True; full=True; belowT=True
            for d in pool:
                inx=term_in(x,u,d); ing=term_in(g,u,d)
                if inx and not ing: sub=False
                if inx!=ing:
                    full=False
                    if lt_term(d,T): belowT=False
            if sub: subset_xg+=1
            if full: full_eq+=1
            if belowT: eq_below_T+=1
    print(f"rounds={r}: inst={n}")
    print(f"  C_u(oV x) ⊆ C_u(oV g) (monotone, corpus) = {subset_xg}/{n}")
    print(f"  C_u(oV x) == C_u(oV g) FULL (corpus)      = {full_eq}/{n}")
    print(f"  agree below T (corpus, lt_term threshold) = {eq_below_T}/{n}")
