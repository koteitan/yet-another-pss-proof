import sys
sys.path.insert(0,'.')
from probe_bmocf_ancestor import enum_depth
from probe_copycrux import pairlt, seqlex, sle, shiftr0, copies
from fast_pss import idx1, hasParent1, parent1, hasParent0, parent0, entry as fentry
def true_root(M):
    j1=len(M)-1
    if j1<=0: return None
    i1=idx1(M,j1)
    if i1==1:
        return parent1(M,j1) if hasParent1(M,j1) else None
    return parent0(M,j1) if hasParent0(M,j1) else None
for rounds,ml in [(6,11),(8,11)]:
    hosts=[tuple(M) for M in enum_depth(5,(1,2,3,4,5),ml,rounds) if len(M)>=2 and M[0]==(0,0)]  # NO row1<=1 restriction
    hosts=sorted(set(hosts)); hs=set(hosts)
    nAll=vAll=0; nCorr=vCorr=0; exs=[]
    for M in hosts:
        Ml=list(M); j1=len(Ml)-1
        lp=Ml[j1]
        tr=true_root(Ml)
        # enumerate ALL split points j0 satisfying the STATED hypotheses
        for j0 in range(0,j1):
            G=Ml[:j0]; blk=Ml[j0:j1]
            if not blk: continue
            v0,w0=blk[0]; R=blk[1:]
            if not all(v0<x[0] for x in R): continue
            d0=lp[0]-v0
            if d0<=0: continue
            if lp[1]!=w0+1: continue
            pref=G+blk; qh=(v0+d0,w0); blkp=shiftr0(d0,blk)
            for N in hosts:
                Nl=list(N)
                if len(Nl)<=len(pref) or Nl[:len(pref)]!=pref: continue
                if Nl[len(pref)]!=qh: continue
                S=Nl[len(pref)+1:]
                Shi=[]
                for p in S:
                    if v0+d0<p[0]: Shi.append(p)
                    else: break
                ok=sle(Shi, shiftr0(d0, list(R)+copies(d0,blkp,len(Shi))))
                nAll+=1
                if not ok:
                    vAll+=1
                    if len(exs)<3: exs.append((M,N,j0,tr))
                if tr is not None and j0==tr:
                    nCorr+=1
                    if not ok: vCorr+=1
    print(f"[+{rounds}] ALL decompositions: inst={nAll} VIOL={vAll}   |  ONLY oper's true root: inst={nCorr} VIOL={vCorr}")
    for e in exs: print("   viol M=",e[0]," N=",e[1]," j0=",e[2]," true_root=",e[3])
