import sys
sys.path.insert(0,'.')
from probe_bmocf_ancestor import enum_depth
from probe_arch_global_inv import oper_decomp
from probe_copycrux import pairlt, seqlex, sle, shiftr0, copies
for rounds,ml,MMAX in [(5,9,8),(6,10,10),(7,11,12)]:
    hosts=[tuple(M) for M in enum_depth(2,(1,2,3),ml,rounds) if len(M)>=2 and all(p[1]<=1 for p in M) and M[0]==(0,0)]
    hosts=sorted(set(hosts)); nI=nV=0; exs=[]; need_m=0
    for M in hosts:
        dec=oper_decomp(list(M))
        if dec is None: continue
        G,blk,d0,lp=dec
        if not blk or d0<=0: continue
        v0,w0=blk[0]; R=blk[1:]
        if not all(v0<x[0] for x in R): continue
        if lp!=(v0+d0,w0+1): continue
        pref=list(G)+list(blk); qh=(v0+d0,w0); blkp=shiftr0(d0,list(blk))
        for N in hosts:
            Nl=list(N)
            if len(Nl)<=len(pref) or Nl[:len(pref)]!=pref: continue
            if Nl[len(pref)]!=qh: continue
            S=Nl[len(pref)+1:]
            Shi=[]
            for p in S:
                if v0+d0 < p[0]: Shi.append(p)
                else: break
            nI+=1
            hit=None
            for m in range(0,MMAX+1):
                if sle(Shi, shiftr0(d0, list(R)+copies(d0,blkp,m))): hit=m; break
            if hit is None:
                nV+=1
                if len(exs)<5: exs.append((M,N,tuple(blk),d0,tuple(Shi)))
            elif hit>0: need_m+=1
    print(f"[+{rounds}] AscArgDom instances={nI}  ***VIOLATIONS={nV}***  (needed m>0 in {need_m})")
    for e in exs: print("   viol:",e)
