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
    return harg(X), X, W
# enumerate standard M, compute hb(M) and hb(M[n]) for n=1..3, look at relationship
base=enum_ST(seed_max_v=4,oper_ns=(1,2,3),max_len=12,rounds=5)
forms=list(set(base))
print("base forms=",len(forms),flush=True)
samples=[]; 
# relationship stats: is hb(M[n]) related to hb(M)? check if hb(M) is a G_0-critical of hb(M[n]) or subterm
hb_in_next=0; checked=0
for M in forms:
    r0=hbOf(M)
    if r0 is None: continue
    hbM,XM,WM=r0
    for n in (1,2,3):
        Mn=list(oper(list(M),n))
        rn=hbOf(Mn)
        if rn is None: continue
        hbN,XN,WN=rn
        checked+=1
        # is hbM among G_0(hbN) or a subterm-ish? or hbN nests hbM?
        rel=[]
        if hbM==hbN: rel.append("EQ")
        if hbM in Glist(0,hbN): rel.append("hbM in G0(hbN)")
        if hbN in Glist(0,hbM): rel.append("hbN in G0(hbM)")
        if lt_term(hbM,hbN): rel.append("hbM<hbN")
        elif lt_term(hbN,hbM): rel.append("hbN<hbM")
        if "hbM in G0(hbN)" in rel: hb_in_next+=1
        if len(samples)<14:
            samples.append((fmtb(XM)[:26],fmtb(hbM)[:22],n,fmtb(hbN)[:30],rel))
print(f"checked M->M[n] firing pairs={checked}  hbM in G0(hbN)={hb_in_next}")
for s in samples:
    print(f"  X={s[0]:26} hbM={s[1]:22} n={s[2]} hbN={s[3]:30} {s[4]}")
