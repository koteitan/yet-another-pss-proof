import sys; sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term as olt, fmtb
Z=()
def Glist(u,x):
    if x==(): return []
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    head=([b]+Glist(u,b)) if u<=a else []
    return head+Glist(u,c)
def leadof(x): return 0 if x==() else x[0][1]
def harg(x): return () if x==() else x[0][2]
def maxo(x,ys):
    m=x
    for y in ys:
        if olt(m,y): m=y
    return m
def proj(u,x):
    while True:
        gs=[g for g in Glist(u,x) if not olt(g,x)]
        if not gs: return x
        x=maxo(gs[0],gs[1:])
def subterms(x):
    if x==(): return
    yield x
    yield from subterms(x[0][2])
    yield from subterms(tuple(x[1:]))
# DEEP: large ST_PS closure, all nrm-output subterms, head a-canonicity
base=enum_ST(seed_max_v=7,oper_ns=(1,2,3,4,5),max_len=20,rounds=8)
forms=list(set(base))
print("forms=",len(forms),flush=True)
seen=set(); chk=0; fail=0; samples=[]
for M in forms:
    Y=nrm(conv(translate(list(M))))
    for s in subterms(Y):
        if s in seen: continue
        seen.add(s)
        a=s[0][1]; hb=harg(s)
        chk+=1
        if proj(a,hb)!=hb:
            fail+=1
            if len(samples)<6: samples.append((fmtb(s)[:30],a))
print(f"distinct nrm-output subterms checked={chk}")
print(f"  proj (lead s) (harg s) != harg s  FAILS={fail}")
for s in samples: print("   ",s)
