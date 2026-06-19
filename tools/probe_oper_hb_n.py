import sys; sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term, fmtb
from fast_pss import oper
Z=()
def Glist(u,x):
    if x==(): return []
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    head=([b]+Glist(u,b)) if u<=a else []
    return head+Glist(u,c)
def fires(u,x): return any(not lt_term(g,x) for g in Glist(u,x))
def harg(x): return () if x==() else x[0][2]
def takeW(r):
    out=[]
    for p in r:
        if p[0]>0: out.append(p)
        else: break
    return out
def NT(S): return nrm(conv(translate(list(S))))
def hbOf(M):
    M=list(M)
    if not M or M[0][0]!=0: return None
    W=takeW(M[1:])
    if not W: return None
    X=NT(tuple(W))
    if not fires(0,X): return None
    return harg(X)
base=enum_ST(seed_max_v=4,oper_ns=(1,2,3),max_len=10,rounds=3)
forms=list(set(base))
shown=0
for M in forms:
    h0=hbOf(M)
    if h0 is None: continue
    hs=[]
    ok=True
    for n in (1,2,3):
        hn=hbOf(list(oper(list(M),n)))
        hs.append(fmtb(hn)[:46] if hn is not None else "(nofire)")
    print(f"hb(N)   = {fmtb(h0)[:46]}")
    for n,h in zip((1,2,3),hs): print(f"  [{n}] = {h}")
    shown+=1
    if shown>=8: break
