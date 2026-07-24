"""Census with the RIGHT boundary p = |G|+|blk| (copy 0 belongs to M itself)."""
import sys, collections
sys.path.insert(0,'.')
from probe_bmocf_ancestor import enum_depth
from probe_copycrux import sle, shiftr0
from fast_pss import idx1, hasParent1, parent1, hasParent0, parent0, fmt
from probe_badbranch_cases import arg, c4, decomp

st=collections.Counter(); exs={}
for (vmax,ns,ml,rounds) in [(4,(1,2,3),10,6),(5,(1,2,3,4,5),11,7)]:
    hosts=sorted(set(tuple(M) for M in enum_depth(vmax,ns,ml,rounds) if len(M)>=2 and M[0]==(0,0)))
    for M in hosts:
        d=decomp(list(M))
        if d is None: continue
        G,blk,d0=d; g=len(G); L=len(blk); p=g+L
        for n in (1,2,3,4):
            N=list(G)
            for k in range(n): N+=shiftr0(k*d0,blk)
            if len(N)>18: continue
            for i in range(len(N)):
                u,w=N[i]; A=arg(N,i)
                for t in range(len(A)):
                    if A[t][1]!=w: continue
                    e=A[t][0]-u
                    if e<=0: continue
                    j=i+1+t; A1=A[:t]; B=arg(N,j); endA=i+1+len(A)
                    if not c4(A1,u,e,w): continue
                    if j < p:
                        st['B: j < p  (both in G++blk)']+=1
                        st['   B1: arg(i) stays in G++blk' if endA<=p else '   B2: arg(i) reaches the tower']+=1
                    elif i >= p:
                        st['A1: p <= i  (both beyond copy 0)']+=1
                    else:
                        st['A2: i < p <= j  (CROSS)']+=1
                        if 'A2' not in exs and n>=2 and g>0: exs['A2']=(M,n,i,j,G,blk,d0)
                    if not sle(B,shiftr0(e,A)): st['VIOLATION']+=1
for k,v in sorted(st.items()): print(f"  {k}: {v}")
for k,(M,n,i,j,G,blk,d0) in exs.items():
    print(f"  witness {k}: M={fmt(M)} n={n} i={i} j={j} G={fmt(G)} blk={fmt(blk)} d0={d0}")
