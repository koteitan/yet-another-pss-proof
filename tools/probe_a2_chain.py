"""Case A2: test the 'preimage chain' proof strategy.

Chain:  B = arg_N(j)  --(tower self-similarity, k steps back)-->  sle B (shiftr0 (k*d0) B0)
        where c0 = blk[o1] is the copy-0 preimage of the deeper column, B0 = arg_N(pos c0);
        then (i, pos c0) should be a CASE-B instance giving sle B0 (shiftr0 (u2-u) A).
Compose: sle B (shiftr0 e A).

Report:  order of i vs pos(c0);  validity of each link; whether the (i,pos c0) pair
satisfies the ArgDomCore side conditions.
"""
import sys, collections
sys.path.insert(0,'.')
from probe_bmocf_ancestor import enum_depth
from probe_copycrux import sle, seqlex, shiftr0
from fast_pss import fmt
from probe_badbranch_cases import arg, c4, decomp

def spineOK(A,L,w):
    for t,x in enumerate(A):
        if x[0] < L and all(x[0] < y[0] for y in A[t+1:]):
            if not (w <= x[1]): return False
    return True

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
                    # copy index / offset of the deeper column
                    k1=(j-g)//L; o1=(j-g)%L
                    j0=g+o1                       # position of the copy-0 preimage
                    c0=N[j0]; u2=c0[0]; B0=arg(N,j0)
                    assert c0[1]==w and u2+k1*d0==u+e, (c0,w,u2,k1,d0,u,e)
                    # link (a): tower self-similarity
                    st['(a) sle B (shift k1*d0 B0): '+str(sle(B,shiftr0(k1*d0,B0)))]+=1
                    # order of i vs j0
                    if i==j0: st['i == pos(c0)  (self-similar, done)']+=1; continue
                    if i>j0:
                        st['*** i > pos(c0)  CHAIN BREAKS ***']+=1
                        if len(exs['gt'])<10: exs['gt'].append((M,n,G,blk,d0,i,j,j0,u,w,e,u2))
                        continue
                    st['i < pos(c0)']+=1
                    st['   u2>u: '+str(u2>u)]+=1
                    # link (b): the case-B pair (i, j0)
                    A1p=N[i+1:j0]
                    ok_h1 = all(u<x[0] for x in A1p)
                    ok_sp = spineOK(A1p,u2,w)
                    st['   (b) hyps h1={} spine={}'.format(ok_h1,ok_sp)]+=1
                    st['   (b) sle B0 (shift (u2-u) A): '+str(sle(B0,shiftr0(u2-u,A)))]+=1
                    if not (ok_h1 and ok_sp) and len(exs['bad'])<10:
                        exs['bad'].append((M,n,G,blk,d0,i,j,j0,u,w,e,u2,tuple(A1p)))
                    # does B0 spill past p?
                    st['   (b) B0 spills past p: '+str(j0+1+len(B0)>p)]+=1
                    if j0+1+len(B0)>p:
                        st['      spill & o1==0: '+str(o1==0)]+=1
                        if o1!=0 and len(exs['spill'])<10:
                            exs['spill'].append((M,n,G,blk,d0,i,j,j0,o1,u,w,e,u2,tuple(B0)))
for k,v in sorted(st.items()): print(f"  {k}: {v}")
print()
for key in ('gt','bad','spill'):
    for r in exs[key][:6]:
        print(f"  {key}: {r}")
