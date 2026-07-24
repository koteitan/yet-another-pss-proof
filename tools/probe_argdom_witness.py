import sys
sys.path.insert(0,'.')
from probe_bmocf_ancestor import enum_depth
from probe_arch_global_inv import oper_decomp
from probe_copycrux import pairlt, seqlex, sle, shiftr0, copies
def constituents(Shi):
    """split S_hi into top-level blocks (root = minimal row-0 among them)."""
    if not Shi: return []
    base=min(p[0] for p in Shi); out=[]; cur=[]
    for p in Shi:
        if p[0]==base and cur: out.append(cur); cur=[p]
        else: cur.append(p)
    if cur: out.append(cur)
    return out
for rounds,ml in [(5,9),(6,10),(7,11)]:
    hosts=[tuple(M) for M in enum_depth(2,(1,2,3),ml,rounds) if len(M)>=2 and all(p[1]<=1 for p in M) and M[0]==(0,0)]
    hosts=sorted(set(hosts)); nI=0; vC=vL=0; exC=[]
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
                if v0+d0<p[0]: Shi.append(p)
                else: break
            nI+=1
            cs=constituents(Shi)
            # (C) m = number of constituents
            mC=len(cs)
            okC=sle(Shi, shiftr0(d0, list(R)+copies(d0,blkp,mC)))
            # (L) m = len(S_hi)  (crude length bound)
            mL=len(Shi)
            okL=sle(Shi, shiftr0(d0, list(R)+copies(d0,blkp,mL)))
            if not okC:
                vC+=1
                if len(exC)<4: exC.append((M,N,tuple(Shi),mC))
            if not okL: vL+=1
    print(f"[+{rounds}] inst={nI}   (C) m=#constituents VIOL={vC}   (L) m=|S_hi| VIOL={vL}")
    for e in exC: print("   C-viol:",e)
