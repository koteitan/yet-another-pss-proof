import sys; sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term, fmtb
import itertools
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
        if lt_term(m,y): m=y
    return m
def proj(u,x):
    while True:
        gs=[g for g in Glist(u,x) if not lt_term(g,x)]
        if not gs: return x
        x=maxo(gs[0],gs[1:])
# GENERAL claim (no firing, no ST): for ANY term t, let Y=nrm t. If Y=P a hb hc then proj a hb = hb.
# i.e. head argument of any nrm output is canonical at its own head subscript.
# Enumerate random three-terms t and check.
import random
def randterm(depth):
    if depth<=0 or random.random()<0.3: return Z
    a=random.randint(0,4)
    b=randterm(depth-1)
    c=randterm(depth-1)
    # c must be a P-list; keep as tuple of pairs: represent term as tuple of (0,a,b)-rows? 
    # valnorm three representation: tuple of (depth?,sub,arg). Let's mimic conv output shape.
    return ((0,a,b),)+ (c if isinstance(c,tuple) else ())
# Actually easier: use nrm outputs from real translate to get valid shapes, then test ALL their subterms' heads.
base=enum_ST(seed_max_v=5,oper_ns=(1,2,3),max_len=12,rounds=5)
forms=list(set(base))
chk=0; fail=0; samples=[]
def subterms(x):
    if x==(): return
    yield x
    yield from subterms(x[0][2])
    yield from subterms(tuple(x[1:]))
seen=set()
for M in forms:
    Y=nrm(conv(translate(list(M))))
    for s in subterms(Y):
        if s in seen: continue
        seen.add(s)
        a=s[0][1]; hb=harg(s)
        chk+=1
        if proj(a,hb)!=hb:
            fail+=1
            if len(samples)<8: samples.append((fmtb(s)[:28],a,fmtb(hb)[:20]))
print(f"nrm-output subterms checked={chk} (distinct)")
print(f"  proj (lead) (harg) != harg  fails={fail}")
for s in samples: print("   ",s)
