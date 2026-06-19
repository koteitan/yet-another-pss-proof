import sys; sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term as olt
def Gl(u,x):
    if x==(): return []
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    return (([b]+Gl(u,b)) if u<=a else [])+Gl(u,c)
def Gs(u,x): return set(Gl(u,x))
def fires(u,x): return any(not olt(g,x) for g in Gl(u,x))
def leadof(x): return 0 if x==() else x[0][1]
def harg(x): return () if x==() else x[0][2]
def takeW(r):
    out=[]
    for p in r:
        if p[0]>0: out.append(p)
        else: break
    return out
def NT(S): return nrm(conv(translate(list(S))))
base=enum_ST(seed_max_v=8,oper_ns=(1,2,3,4,5),max_len=20,rounds=8)
forms=list(set(base))
chk=0;resid=0;bad_core=0;bad_olt=0;bad_leadeq=0
for M in forms:
    M=list(M)
    if not M or M[0][0]!=0: continue
    W=takeW(M[1:])
    if not W: continue
    X=NT(tuple(W))
    if X==() or not fires(0,X): continue
    a=X[0][1]; hb=harg(X); L=leadof(hb); Ga=Gs(a,hb)
    chk+=1
    for g in Gl(0,hb):
        if g in Ga: continue
        if leadof(g)<L: continue
        resid+=1
        if leadof(g)!=L: bad_leadeq+=1
        if not olt(harg(g),harg(hb)): bad_core+=1
        if not olt(g,hb): bad_olt+=1
print(f"DEEP firing X={chk}  buried-tied residual={resid}")
print(f"  lead g != lead hb (would break green reduction): {bad_leadeq}")
print(f"  harg g NOT <o harg hb (core sorry false): {bad_core}")
print(f"  g NOT <o hb (overall false): {bad_olt}")
