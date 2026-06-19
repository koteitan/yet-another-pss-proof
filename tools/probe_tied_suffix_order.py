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
for _ in range(4):
    new=[]
    for M in cur:
        M=list(M)
        if len(M)<2: continue
        for n in (1,2,3,4,5):
            tt=tuple(oper(M,n))
            if len(tt)<=20 and tt not in extra: extra.add(tt); new.append(tt)
    cur=new
    if not cur: break
print("ST closure=",len(extra),flush=True)
# LEMMA L: for standard host, i0<i, lead(NT W[i0:])==lead(NT W[i:])==k  ==> olt(NT W[i:])(NT W[i0:])
# test over ALL suffix pairs of arg-zones W (not just criticals), all standard M
seen=set(); pairs=0; Lfail=0; ex=[]
forms=0
for M in extra:
    M=list(M)
    if not M or M[0][0]!=0: continue
    W=takeW(M[1:])
    if len(W)<2: continue
    Wt=tuple(W)
    if Wt in seen: continue
    seen.add(Wt); forms+=1
    n=len(W)
    nts=[NT(tuple(W[i:])) for i in range(n)]
    leads=[leadof(t) for t in nts]
    for i0 in range(n):
        for i in range(i0+1,n):
            if leads[i0]==leads[i]:
                pairs+=1
                if not lt_term(nts[i],nts[i0]):
                    Lfail+=1
                    if len(ex)<8: ex.append((fmtb(nts[i0])[:30],fmtb(nts[i])[:30],leads[i0]))
print(f"arg-zones={forms}  tied-lead suffix pairs={pairs}")
print(f"(L: tied-lead later-suffix <o earlier-suffix) FAIL={Lfail}")
for e in ex: print("   L-fail: earlier=",e[0]," later=",e[1]," k=",e[2])
