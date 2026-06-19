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
# For buried-tied residual g (outside Gterm a hb, lead g>=lead hb): verify olt g hb, and check
#  candidate green levers: (1) g is a *proper* subterm-occurrence => smaller; (2) tail-position;
#  (3) does g appear deeper in hb's structure than the head spine?  Measure: is g always olt hb (TRUE),
#  and is g always a Gterm-element of harg(hb) i.e. one level deeper?
chk=0; resid=0; bad=0; deeper=0; tail=0
for M in forms:
    M=list(M)
    if not M or M[0][0]!=0: continue
    W=takeW(M[1:])
    if not W: continue
    X=NT(tuple(W))
    if X==() or not fires(0,X): continue
    a=X[0][1]; hb=harg(X)
    chk+=1
    Ga=Gset(a,hb)
    Lhb=leadof(hb)
    for g in Glist(0,hb):
        if g in Ga: continue
        if leadof(g)<Lhb: continue
        resid+=1
        if not olt(g,hb): bad+=1
        # is g in Gterm 0 (harg hb)?  (one level deeper, under the head-arg of hb)
        if g in Gset(0,harg(hb)): deeper+=1
print(f"firing X={chk}  buried-tied residual criticals={resid}")
print(f"  NOT olt g hb (would be FALSE enshrine): {bad}")
print(f"  g in Gterm0(harg hb) (one level deeper): {deeper}/{resid}")
