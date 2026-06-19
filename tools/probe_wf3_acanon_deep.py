import sys; sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from valnorm import lt_term as olt, fmtb
from functools import lru_cache
Z=()
def Glist(u,x):
    if x==(): return []
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    head=([b]+Glist(u,b)) if u<=a else []
    return head+Glist(u,c)
def Gset(u,x): return set(Glist(u,x))
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
def wf3(x):
    if x==(): return True
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    if not (wf3(b) and wf3(c)): return False
    for g in Glist(a,b):
        if not olt(g,b): return False
    if c==(): return True
    e=c[0][1]; f=c[0][2]
    return (e<a) or (e==a and (olt(f,b) or f==b))

# size-bounded wf3 enumeration: number of principals <= N, subscripts in 0..S.
# Build all wf3 terms with <= N principal nodes.
def gen_wf3(N, S):
    # returns set of wf3 terms with at most N principals
    by_size = {0: {Z}}
    allterms = {Z}
    for sz in range(1, N+1):
        cur=set()
        # a principal P a b c contributes 1 + |b| + |c| principals; build from smaller
        for bsz in range(0, sz):
            csz = sz-1-bsz
            if csz<0: continue
            bs = by_size.get(bsz, set())
            cs = by_size.get(csz, set())
            for a in range(0, S+1):
                for b in bs:
                    for c in cs:
                        t=((0,a,b),)+c
                        if wf3(t): cur.add(t)
        by_size[sz]=cur
        allterms |= cur
    return allterms

import itertools
for (N,S) in [(5,3),(6,2),(4,4)]:
    terms=[t for t in gen_wf3(N,S) if t!=()]
    checked=0; fail=0; cex=None
    for hb in terms:
        L=leadof(hb)
        for a in range(0,L):
            if proj(a,hb)!=hb: continue
            Ga=Gset(a,hb)
            for g in Glist(0,hb):
                if g in Ga: continue
                if leadof(g)<L: continue
                checked+=1
                if not olt(g,hb):
                    fail+=1
                    if cex is None: cex=(hb,a,g)
    msg = "PROVABLE (0 fail)" if fail==0 else "NAIVE-FALSE"
    print(f"[wf3 N<={N} S<={S}] terms={len(terms)} residual-instances={checked} FAIL={fail}  => {msg}")
    if cex:
        hb,a,g=cex
        print("   CEX hb=",fmtb(hb)," a=",a," g=",fmtb(g))
