import sys, random; sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
random.seed(11)
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
def proj0(x):
    bb=x
    while True:
        V=[g for g in Glist(0,bb) if not lt_term(g,bb)]
        if not V: break
        m=V[0]
        for g in V[1:]:
            if lt_term(m,g): m=g
        bb=m
    return bb
def harg(x): return () if x==() else x[0][2]
def leadof(x): return 0 if x==() else x[0][1]
def maxsub(t):
    if t==(): return 0
    m=0
    for p in t: m=max(m,p[1],maxsub(p[2]))
    return m
def wf3(t):
    if t==(): return True
    for p in t:
        a,b=p[1],p[2]
        # G_a(b) < b
        for g in Glist(a,b):
            if not lt_term(g,b): return False
        if not wf3(b): return False
    return True
def takeW(r):
    out=[]
    for p in r:
        if p[0]>0: out.append(p)
        else: break
    return out
def NT(S): return nrm(conv(translate(list(S))))

# (1) standard firing arg-zone images: maxsub(hb)==lead(hb)?
print("=== (1) standard forms: maxsub(hb)==lead(hb)? (deep) ===")
base=enum_ST(seed_max_v=5,oper_ns=(1,2,3,4,5),max_len=16,rounds=8)
extra=set(base); cur=list(extra)
for _ in range(6):
    new=[]
    for M in cur:
        M=list(M)
        if len(M)<2: continue
        for n in (1,2,3,4,5):
            tt=tuple(oper(M,n))
            if len(tt)<=24 and tt not in extra: extra.add(tt); new.append(tt)
    cur=new
    if not cur: break
print("ST closure=",len(extra),flush=True)
seen=set(); tot=0; ml_fail=0; ex=[]
for M in extra:
    M=list(M)
    if not M or M[0][0]!=0: continue
    aM=tuple(takeW(M[1:]))
    if not aM: continue
    X=NT(aM)
    if X in seen: continue
    seen.add(X)
    if not fires(0,X): continue
    tot+=1
    hb=harg(X)
    if maxsub(hb)!=leadof(hb):
        ml_fail+=1
        if len(ex)<8: ex.append((fmtb(X)[:45],fmtb(hb)[:45],maxsub(hb),leadof(hb)))
print(f"firing={tot}  maxsub(hb)!=lead(hb) FAIL={ml_fail}")
for e in ex: print("   fail:",e)

# (2) sufficiency: random wf3 with maxsub==lead: is proj0=identity?
print("\n=== (2) sufficiency: wf3 t & maxsub t==lead t  ==>  proj0 t == t ? ===")
def randtree(depth, maxk):
    if depth<=0 or random.random()<0.3: return Z
    n=random.randint(1,3); ps=[]
    for _ in range(n):
        a=random.randint(0,maxk); ps.append((0,a,randtree(depth-1,maxk)))
    return tuple(ps)
tested=0; suff_fail=0; ex2=[]
tries=0
while tested<100000 and tries<3000000:
    tries+=1
    t=randtree(4, random.randint(1,4))
    if t==(): continue
    if not wf3(t): continue
    if maxsub(t)!=leadof(t): continue
    tested+=1
    if proj0(t)!=t:
        suff_fail+=1
        if len(ex2)<8: ex2.append((fmtb(t)[:55],))
print(f"wf3 & maxsub==lead tested={tested}  proj0!=t (sufficiency FAIL)={suff_fail}")
for e in ex2: print("   suff-fail:",e)
