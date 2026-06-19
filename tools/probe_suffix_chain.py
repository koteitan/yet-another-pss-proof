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
mono_fail=0   # NT(W[i:]) strictly decreasing as i increases?
hb_is_suffix=0 # hb == NT(W[i0:]) for some i0?
hb_eq_W1=0    # hb == NT(W[1:])?
samples=[]
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
    chain=[NT(tuple(W[i:])) for i in range(n)]  # i=0 is full W=X
    # monotone strictly decreasing for i=1..n-1 ? (drop i=0 which is X itself)
    ok=True
    for i in range(1,n-1):
        if not lt_term(chain[i+1],chain[i]): ok=False; break
    if not ok: mono_fail+=1
    # hb among suffix chain?
    if hb in chain[1:]: hb_is_suffix+=1
    if n>=2 and hb==chain[1]: hb_eq_W1+=1
    if len(samples)<10:
        samples.append((fmtb(X)[:34], fmtb(hb)[:28], [fmtb(c)[:16] for c in chain]))
print(f"firing={tot}")
print(f"(MONO) NT(W[i:]) strictly decreasing i=1..: FAIL={mono_fail}/{tot}")
print(f"(hb in suffix-chain[1:]) count={hb_is_suffix}/{tot}")
print(f"(hb == NT(W[1:])) count={hb_eq_W1}/{tot}")
print("--- samples (X | hb | [NT(W[i:]) i=0..]) ---")
for x,h,ch in samples: print(f"  X={x:34} hb={h:28} chain={ch}")
