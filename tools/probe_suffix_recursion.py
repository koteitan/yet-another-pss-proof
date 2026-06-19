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
def tailc(x): return tuple(x[1:]) if x!=() else ()
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
base=enum_ST(seed_max_v=5,oper_ns=(1,2,3,4,5),max_len=14,rounds=6)
extra=set(base); cur=list(extra)
for _ in range(3):
    new=[]
    for M in cur:
        M=list(M)
        if len(M)<2: continue
        for n in (1,2,3,4,5):
            tt=tuple(oper(M,n))
            if len(tt)<=18 and tt not in extra: extra.add(tt); new.append(tt)
    cur=new
    if not cur: break
print("ST closure=",len(extra),flush=True)
seen=set(); tot=0
allG_suffix_fail=0   # ALL G_0-criticals of hb are suffix-NTs?
harg_suffix_fail=0   # harg(hb) is a suffix-NT?
# recursion: hb=NT(W[i0:]); is harg(hb)=NT(W[i1:]) with i1>i0, and hc-part too?
rec_fail=0; ex=[]
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
    hb=harg(X); n=len(W)
    suf={NT(tuple(W[i:])):i for i in range(n)}  # suffix-NT -> smallest i
    sufset=set(suf)
    # all G_0-criticals of hb suffix-NT?
    if not all(g in sufset for g in Glist(0,hb)): allG_suffix_fail+=1
    # harg(hb) suffix-NT?
    hh=harg(hb)
    if hh!=() and hh not in sufset: harg_suffix_fail+=1
    # recursion: hb=NT(W[i0:]); harg(hb)=NT(W[i1:]), i1>i0
    if hb in suf:
        i0=suf[hb]
        if hh==() or (hh in suf and suf[hh]>i0): pass
        else:
            rec_fail+=1
            if len(ex)<6: ex.append((fmtb(hb)[:34],fmtb(hh)[:24], suf.get(hh,'NA'), i0))
    else:
        rec_fail+=1
print(f"firing={tot}")
print(f"(ALL G_0(hb) are suffix-NT) FAIL={allG_suffix_fail}/{tot}")
print(f"(harg(hb) is suffix-NT) FAIL={harg_suffix_fail}/{tot}")
print(f"(RECURSION hb=NT(W[i0:]) & harg(hb)=NT(W[i1:]),i1>i0) FAIL={rec_fail}/{tot}")
for e in ex: print("   rec-fail:",e)
