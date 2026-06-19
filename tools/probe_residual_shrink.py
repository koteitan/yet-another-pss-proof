import sys; sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term as olt, fmtb
Z=()
def Glist(u,x):
    if x==(): return []
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    head=([b]+Glist(u,b)) if u<=a else []
    return head+Glist(u,c)
def Gset(u,x): return set(Glist(u,x))
def fires(u,x): return any(not olt(g,x) for g in Glist(u,x))
def leadof(x): return 0 if x==() else x[0][1]
def harg(x): return () if x==() else x[0][2]
def maxo(x,ys):
    m=x
    for y in ys:
        if olt(m,y): m=y
    return m
def proj(u,x):
    while True:
        gs=[g for g in Glist(u,x) if not olt(g,x)]
        if not gs: return x
        x=maxo(gs[0],gs[1:])
def takeW(r):
    out=[]
    for p in r:
        if p[0]>0: out.append(p)
        else: break
    return out
def NT(S): return nrm(conv(translate(list(S))))
base=enum_ST(seed_max_v=6,oper_ns=(1,2,3,4),max_len=16,rounds=7)
forms=list(set(base))
chk=0
# After a-canon (kills Gterm a hb) + nontied(lead<a kills lead<a): residual = g in Gterm0 hb \ Gterm a hb with lead g>=a.
# How many such residual criticals remain? are they exactly the "tied" lead g=lead hb ones, or broader?
resid_tot=0; resid_with_leadlt_hb=0; tied_only=0
import collections
leaddist=collections.Counter()
for M in forms:
    M=list(M)
    if not M or M[0][0]!=0: continue
    W=takeW(M[1:])
    if not W: continue
    X=NT(tuple(W))
    if X==() or not fires(0,X): continue
    a=X[0][1]; hb=harg(X); Lhb=leadof(hb)
    chk+=1
    Ga=Gset(a,hb)
    for g in Glist(0,hb):
        if g in Ga: continue            # killed by a-canon
        if leadof(g)<a: continue        # killed by nontied (lead<a<lead hb)
        # residual critical
        resid_tot+=1
        leaddist[("lead g vs lead hb", "=" if leadof(g)==Lhb else ("<" if leadof(g)<Lhb else ">"))]+=1
print(f"firing X checked={chk}")
print(f"  residual 0-criticals (not in Gterm a hb, lead>=a) = {resid_tot}")
print(f"  lead-vs-leadhb distribution: {dict(leaddist)}")
