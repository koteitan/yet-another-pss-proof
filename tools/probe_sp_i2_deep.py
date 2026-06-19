import sys; sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term, fmtb
from fast_pss import oper
def Glist(u,x):
    if x==(): return []
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    head=([b]+Glist(u,b)) if u<=a else []
    return head+Glist(u,c)
def fires(a,x): return any(not lt_term(g,x) for g in Glist(a,x))
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
def takeW(r):
    out=[]
    for p in r:
        if p[0]>0: out.append(p)
        else: break
    return out
def NT(S): return nrm(conv(translate(list(S))))
def harg(x): return () if x==() else x[0][2]
def leadof(x): return 0 if x==() else x[0][1]
def subs_set(t):
    s=set()
    def go(t):
        if t==(): return
        for p in t: s.add(p[1]); go(p[2])
    go(t); return s
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
print('deep ST closure =',len(extra),flush=True)
seen=set(); tot=0
sp_fail=0; i2_fail=0; canon_fail=0; i1_fail=0
sp_ex=[]; i2_ex=[]; canon_ex=[]
leadX={}
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
    hb=harg(X); lX=leadof(X)
    leadX[lX]=leadX.get(lX,0)+1
    if not (X!=() and len(X)==1): pass # X may be sum; that's fine
    # SP: hb single principal
    if not (hb!=() and len(hb)==1):
        sp_fail+=1
        if len(sp_ex)<6: sp_ex.append((fmtb(X)[:55],fmtb(hb)[:55]))
    # I2: lead X == 1
    if lX!=1:
        i2_fail+=1
        if len(i2_ex)<6: i2_ex.append((fmtb(X)[:60],lX))
    # 0-canonical
    if proj0(hb)!=hb:
        canon_fail+=1
        if len(canon_ex)<6: canon_ex.append((fmtb(X)[:55],fmtb(hb)[:55]))
    if 0 in subs_set(hb): i1_fail+=1
print(f"firing X = {tot}")
print(f"(SP) hb single principal: FAIL={sp_fail}/{tot}")
for e in sp_ex: print("   SP-fail:",e)
print(f"(I2) lead X==1: FAIL={i2_fail}/{tot}  leadX dist={dict(sorted(leadX.items()))}")
for e in i2_ex: print("   I2-fail:",e)
print(f"hb 0-canonical: FAIL={canon_fail}/{tot}")
for e in canon_ex: print("   canon-fail:",e)
print(f"(I1 dead) hb has D_0 principal: {i1_fail}/{tot}")
