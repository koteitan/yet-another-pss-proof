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
def leadof(x): return 0 if x==() else x[0][1]
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
# Characterize hb(N) -> hb(N[1]) precisely. Is hb(N[1]) a structural rewrite of hb(N)?
# Hypotheses: (a) hb(N[1]) is got by replacing the DEEPEST principal D_k(0) leaf-area of hb(N).
#  Look at hb(N) and hb(N[n]) side by side for n=1,2.
base=enum_ST(seed_max_v=4,oper_ns=(1,2,3),max_len=12,rounds=4)
forms=list(set(base))
import collections
samples=[]
# test: hb(N[1]) vs hb(N): does hb(N[1]) = hb(N) with rightmost/deepest D_k(0) replaced?
for M in forms:
    h0=hbOf(M)
    if h0 is None: continue
    M1=list(oper(list(M),1))
    h1=hbOf(M1)
    if h1 is None: continue
    if len(samples)<20:
        samples.append((fmtb(h0),fmtb(h1)))
for a,b in samples:
    print(f"hb(N)= {a:34}  hb(N[1])= {b}")
