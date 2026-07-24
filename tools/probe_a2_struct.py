"""Case A2 (cross) structural census: which instances survive the
'data fits in a smaller tower' reduction, and what do the survivors look like?"""
import sys, collections
sys.path.insert(0,'.')
from probe_bmocf_ancestor import enum_depth
from probe_copycrux import sle, seqlex, shiftr0
from fast_pss import fmt
from probe_badbranch_cases import arg, c4, decomp

st=collections.Counter(); exs=collections.defaultdict(list)
for (vmax,ns,ml,rounds) in [(4,(1,2,3),10,6),(5,(1,2,3,4,5),11,7)]:
    hosts=sorted(set(tuple(M) for M in enum_depth(vmax,ns,ml,rounds) if len(M)>=2 and M[0]==(0,0)))
    for M in hosts:
        d=decomp(list(M))
        if d is None: continue
        G,blk,d0=d; g=len(G); L=len(blk); p=g+L
        v0,w0=blk[0]
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
                    j=i+1+t; A1=A[:t]; B=arg(N,j)
                    if not c4(A1,u,e,w): continue
                    if not (i < p <= j): continue
                    st['A2 total']+=1
                    datalen = j+1+len(B)     # |X|+1+|A1|+1+|B|
                    # smallest tower containing the data
                    if datalen<=g: mneed=0
                    else: mneed=-(-(datalen-g)//L)
                    if mneed<n:
                        st['A2 reducible to smaller tower (m<n)']+=1
                        continue
                    st['A2 RESIDUAL (data reaches last copy)']+=1
                    kj=(j-g)//L; oj=(j-g)%L
                    st[f'  residual: d0>0={d0>0}']+=1
                    st[f'  residual: w<=w0 = {w<=w0}']+=1
                    st[f'  residual: i<g={i<g} i==g={i==g}']+=1
                    st[f'  residual: kj={kj} n={n}']+=1
                    st[f'  residual: |B|<=|A1| = {len(B)<=len(A1)}']+=1
                    if len(exs['res'])<25:
                        exs['res'].append((M,n,G,blk,d0,i,j,u,w,e,tuple(A1),tuple(B),tuple(A)))
                    if not sle(B,shiftr0(e,A)): st['VIOLATION']+=1
for k,v in sorted(st.items()): print(f"  {k}: {v}")
print()
for (M,n,G,blk,d0,i,j,u,w,e,A1,B,A) in exs['res'][:25]:
    print(f"M={fmt(M)} n={n} G={fmt(G)} blk={fmt(blk)} d0={d0} i={i} j={j} u={u} w={w} e={e}")
    print(f"    A1={fmt(A1)} B={fmt(B)} shift_e(A)={fmt(shiftr0(e,A))}")
