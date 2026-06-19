import sys; sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term, fmtb
Z=()
def Glist(u,x):
    if x==(): return []
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    head=([b]+Glist(u,b)) if u<=a else []
    return head+Glist(u,c)
def fires(u,x): return any(not lt_term(g,x) for g in Glist(u,x))
def harg(x): return () if x==() else x[0][2]
def leadof(x): return 0 if x==() else x[0][1]
def maxo(x,ys):
    m=x
    for y in ys:
        if lt_term(m,y): m=y
    return m
def proj(u,x):
    while True:
        gs=[g for g in Glist(u,x) if not lt_term(g,x)]
        if not gs: return x
        x=maxo(gs[0],gs[1:])
def takeW(r):
    out=[]
    for p in r:
        if p[0]>0: out.append(p)
        else: break
    return out
def NT(S): return nrm(conv(translate(list(S))))
# KEY QUESTION: for firing X, is harg X = proj 0 (harg X)? And does the head subscript a of X relate?
# Also: is harg X itself a proj k output for k = lead X +1?  X = P a hb hc; conjecture: proj a (harg X)=harg X always (a-canonical, weaker)
base=enum_ST(seed_max_v=4,oper_ns=(1,2,3),max_len=12,rounds=5)
forms=list(set(base))
chk=0; fail0=0; failA=0; failAplus=0
for M in forms:
    M=list(M)
    if not M or M[0][0]!=0: continue
    W=takeW(M[1:])
    if not W: continue
    X=NT(tuple(W))
    if X==() or not fires(0,X): continue
    a=X[0][1]; hb=harg(X)
    chk+=1
    # claim0: proj0 hb = hb  (the target)
    if proj(0,hb)!=hb: fail0+=1
    # claimA: proj a hb = hb  (a-canonical, weaker, should hold by nrm structure)
    if proj(a,hb)!=hb: failA+=1
    # claimA+1: proj (a+1) hb = hb
    if proj(a+1,hb)!=hb: failAplus+=1
print(f"firing X checked={chk}")
print(f"  proj0 hb != hb (TARGET fails)= {fail0}")
print(f"  proj a hb != hb (a-canon fails)= {failA}")
print(f"  proj (a+1) hb != hb fails= {failAplus}")
