"""T8: in the ascending true-root decomposition, every column of R with level < v0+d0
is a row-0 ancestor of the last column (i.e. the low columns are exactly the spine)."""
import sys, collections
sys.path.insert(0,'.')
from probe_bmocf_ancestor import enum_depth
from fast_pss import idx1, hasParent1, parent1, hasParent0, parent0, le0, fmt

def true_root(M):
    j1=len(M)-1
    if j1<=0: return None
    i1=idx1(M,j1)
    if i1==1: return parent1(M,j1) if hasParent1(M,j1) else None
    return parent0(M,j1) if hasParent0(M,j1) else None

for (vmax,ns,ml,rounds) in [(5,(1,2,3,4,5),13,9),(4,(1,2,3),18,10),(6,(1,2,3),16,8),(3,(1,2,3,4,5,6),20,12)]:
    hosts=sorted(set(tuple(M) for M in enum_depth(vmax,ns,ml,rounds) if len(M)>=2 and M[0]==(0,0)))
    tot=0; bad=0; exs=[]; badt6=0
    for M in hosts:
        Ml=list(M); j1=len(Ml)-1; lp=Ml[j1]
        j0=true_root(Ml)
        if j0 is None: continue
        blk=Ml[j0:j1]
        if not blk: continue
        v0,w0=blk[0]; R=blk[1:]
        if not all(v0<x[0] for x in R): continue
        d0=lp[0]-v0
        if d0<=0 or lp[1]!=w0+1: continue
        tot+=1
        low=[(j0+1+t,x) for t,x in enumerate(R) if x[0]<v0+d0]
        if any(not le0(M,p,j1) for (p,x) in low):
            bad+=1
            if len(exs)<3: exs.append((M,j0,d0,R))
        if not all(x[1]>=w0 for (p,x) in low): badt6+=1
    print(f"vmax={vmax} ns={ns} ml={ml} r={rounds}: hosts={len(hosts)} decomp={tot} T8-FAIL={bad} T6-FAIL={badt6}")
    for e in exs: print("   ",fmt(e[0]),"j0=",e[1],"d0=",e[2],"R=",e[3])
