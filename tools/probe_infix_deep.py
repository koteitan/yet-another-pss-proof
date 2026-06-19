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
ntc={}
def NT(S):
    v=ntc.get(S)
    if v is None: v=nrm(conv(translate(list(S)))); ntc[S]=v
    return v
base=enum_ST(seed_max_v=5,oper_ns=(1,2,3,4,5),max_len=16,rounds=8)
extra=set(base); cur=list(extra)
for _ in range(5):
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
seen=set(); tot=0; tied=0; infix_fail=0; suffix_fail=0; ex=[]
for M in extra:
    M=list(M)
    if not M or M[0][0]!=0: continue
    W=takeW(M[1:])
    if not W: continue
    Wt=tuple(W); X=NT(Wt)
    if X in seen: continue
    seen.add(X)
    if not fires(0,X): continue
    tot+=1
    hb=harg(X); k=leadof(hb); n=len(W)
    tiedg=[g for g in Glist(0,hb) if leadof(g)==k]
    if not tiedg: 
        if tot%100000==0: print(f"  ...firing={tot} tied={tied} infix_fail={infix_fail}",flush=True)
        continue
    infix_nts=set()
    suffix_nts=set(NT(tuple(W[i:])) for i in range(n))
    for i in range(n):
        for j in range(i+1,n+1): infix_nts.add(NT(tuple(W[i:j])))
    for g in tiedg:
        tied+=1
        if g not in infix_nts:
            infix_fail+=1
            if len(ex)<6: ex.append((fmtb(hb)[:38],fmtb(g)[:26]))
        if g not in suffix_nts: suffix_fail+=1
    if tot%100000==0: print(f"  ...firing={tot} tied={tied} infix_fail={infix_fail} suffix_fail={suffix_fail}",flush=True)
print(f"FINAL firing={tot} tied={tied}")
print(f"H_infix FAIL={infix_fail}   H_suffix FAIL={suffix_fail}")
for e in ex: print("   infix-fail:",e)
