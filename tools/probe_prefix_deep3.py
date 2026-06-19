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
ROUNDS=int(sys.argv[1]) if len(sys.argv)>1 else 5
MAXLEN=int(sys.argv[2]) if len(sys.argv)>2 else 22
for _ in range(ROUNDS):
    new=[]
    for M in cur:
        M=list(M)
        if len(M)<2: continue
        for n in (1,2,3,4,5):
            tt=tuple(oper(M,n))
            if len(tt)<=MAXLEN and tt not in extra: extra.add(tt); new.append(tt)
    cur=new
    if not cur: break
print("ST closure=",len(extra),flush=True)
seen=set(); tot=0; tied_total=0; H_prefix_fail=0; olt_fail=0; ex=[]
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
    prefix_nts=set(NT(tuple(W[:j])) for j in range(1,n+1))
    for g in Glist(0,hb):
        if leadof(g)==k:
            tied_total+=1
            if not lt_term(g,hb): olt_fail+=1
            if g not in prefix_nts:
                H_prefix_fail+=1
                if len(ex)<6: ex.append((fmtb(hb)[:40],fmtb(g)[:26]))
    if tot%100000==0:
        print(f"  ...firing={tot} tied={tied_total} H_prefix_fail={H_prefix_fail} olt_fail={olt_fail}",flush=True)
print(f"FINAL firing={tot} tied criticals={tied_total}")
print(f"olt g hb FAIL={olt_fail}  H_prefix FAIL={H_prefix_fail}")
for e in ex: print("   prefix-fail: hb=",e[0]," g=",e[1])
