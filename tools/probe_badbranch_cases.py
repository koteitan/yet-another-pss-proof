"""Case census for the `bad` branch of the ArgDomCore derivation induction.

For M in ST_PS in the bad branch, N = M[n] = G ++ copies d0 blk n.
Classify every SpineOK-passing ArgDomCore instance (i,j) of N by where i,j sit:
  (a) both in G
  (b) both in the SAME copy k
  (c) in DIFFERENT copies k<k'   -- split by same/different offset within blk
  (X) cross: i in G, j in a copy
Also: for (a)/(b), does arg(i) stay inside that region (so the instance really is
an instance of M / a shift of one)?
"""
import sys, collections
sys.path.insert(0,'.')
from probe_bmocf_ancestor import enum_depth
from probe_copycrux import sle, shiftr0
from fast_pss import idx1, hasParent1, parent1, hasParent0, parent0, entry as fent, fmt

def arg(N,i):
    lv=N[i][0]; out=[]
    for p in N[i+1:]:
        if p[0]>lv: out.append(p)
        else: break
    return out

def c4(A1,u,e,w):
    return all(x[1]>=w for t,x in enumerate(A1)
               if x[0]<u+e and all(y[0]>x[0] for y in A1[t+1:]))

def decomp(M):
    j1=len(M)-1
    if j1<=0: return None
    if M[j1]==(0,0): return None
    i1=idx1(M,j1)
    if i1==1:
        if not hasParent1(M,j1): return None
        j0=parent1(M,j1); d0=M[j1][0]-M[j0][0]
    else:
        if not hasParent0(M,j1): return None
        j0=parent0(M,j1); d0=0
    return M[:j0], M[j0:j1], d0

st=collections.Counter(); exs={}
for (vmax,ns,ml,rounds) in [(4,(1,2,3),10,6),(5,(1,2,3,4,5),11,7)]:
    hosts=sorted(set(tuple(M) for M in enum_depth(vmax,ns,ml,rounds) if len(M)>=2 and M[0]==(0,0)))
    for M in hosts:
        d=decomp(list(M))
        if d is None: continue
        G,blk,d0=d; g=len(G); L=len(blk)
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
                    ki = None if i<g else (i-g)//L
                    kj = None if j<g else (j-g)//L
                    endA = i+1+len(A)   # first position past arg(i)
                    if ki is None and kj is None:
                        st['(a) both in G']+=1
                        st['(a) argA stays in G' if endA<=g else '(a) argA LEAVES G']+=1
                    elif ki is None:
                        st['(X) CROSS i in G, j in a copy']+=1
                        if '(X)' not in exs: exs['(X)']=(M,n,i,j,G,blk,d0)
                    elif ki==kj:
                        st['(b) same copy']+=1
                        st['(b) argA stays in copy' if endA<=g+(ki+1)*L else '(b) argA LEAVES the copy']+=1
                    else:
                        ri=(i-g)%L; rj=(j-g)%L
                        st['(c) different copies']+=1
                        if ri==rj:
                            st['(c) SAME offset in blk']+=1
                        else:
                            st['(c) DIFFERENT offset in blk  <-- refutes "same original column"']+=1
                            if '(c-diff)' not in exs: exs['(c-diff)']=(M,n,i,j,G,blk,d0)
                    if not sle(B,shiftr0(e,A)): st['VIOLATION']+=1
for k,v in sorted(st.items()): print(f"  {k}: {v}")
for k,v in exs.items():
    M,n,i,j,G,blk,d0=v
    print(f"  witness {k}: M={fmt(M)} n={n} i={i} j={j} G={fmt(G)} blk={fmt(blk)} d0={d0}")
