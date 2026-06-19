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

base=enum_ST(seed_max_v=5,oper_ns=(1,2,3,4,5),max_len=16,rounds=8)
extra=set(base); cur=list(extra)
for _ in range(4):
    new=[]
    for M in cur:
        M=list(M)
        if len(M)<2: continue
        for n in (1,2,3,4,5):
            tt=tuple(oper(M,n))
            if len(tt)<=22 and tt not in extra: extra.add(tt); new.append(tt)
    cur=new
    if not cur: break
print("ST closure=",len(extra),flush=True)
seen=set(); tot=0
# H: every tied G_0-critical of hb equals NT of some contiguous infix of W
H_fail=0; ex=[]; tied_total=0
for M in extra:
    M=list(M)
    if not M or M[0][0]!=0: continue
    W=takeW(M[1:])
    if not W: continue
    aM=tuple(W)
    X=NT(aM)
    if X in seen: continue
    seen.add(X)
    if not fires(0,X): continue
    tot+=1
    hb=harg(X); k=leadof(hb)
    # all NT-images of contiguous infixes of W
    nts=set()
    for i in range(len(W)):
        for j in range(i+1,len(W)+1):
            nts.add(NT(tuple(W[i:j])))
    for g in Glist(0,hb):
        if leadof(g)==k:  # tied
            tied_total+=1
            if g not in nts:
                H_fail+=1
                if len(ex)<10: ex.append((fmtb(hb)[:40],fmtb(g)[:30]))
print(f"firing={tot} tied criticals={tied_total}")
print(f"H (tied crit = NT of infix of W) FAIL = {H_fail}")
for e in ex: print("   H-fail: hb=",e[0]," g=",e[1])
