"""Case A2, link (b): can SpineOK A1p c0.1 w be derived from SpineOK A1 (u+e) w
by 'right-visible in A1p  =>  right-visible in A1'?  Look for counterexamples."""
import sys, collections
sys.path.insert(0,'.')
from probe_bmocf_ancestor import enum_depth
from probe_copycrux import sle, shiftr0
from fast_pss import fmt
from probe_badbranch_cases import arg, c4, decomp

def rv(A,t):   # is A[t] right-visible in A ?
    return all(A[t][0] < y[0] for y in A[t+1:])

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
                    k1=(j-g)//L; o1=(j-g)%L; j0=g+o1; c0=N[j0]
                    if i>=j0: continue
                    A1p=N[i+1:j0]                  # = A1[:j0-i-1]
                    st['case (ii) total']+=1
                    # look for x in A1p right-visible in A1p, x.1<c0.1, NOT right-visible in A1
                    bad=False
                    for s,x in enumerate(A1p):
                        if x[0]<c0[0] and all(x[0]<y[0] for y in A1p[s+1:]):
                            if not all(x[0]<y[0] for y in A1[s+1:]):
                                bad=True
                                if len(exs['x'])<12:
                                    exs['x'].append((fmt(M),n,fmt(G),fmt(blk),d0,i,j,j0,x,c0,u,w,e,fmt(A1p),fmt(A1)))
                    st['   right-visibility LEAK: '+str(bad)]+=1
                    # also: is w <= w0 ?
                    st['   w<=w0: '+str(w<=w0)]+=1
                    # spill structure
                    blkt=blk[o1+1:]
                    B0=arg(N,j0)
                    spill = len(B0)>len(blkt) or (len(B0)==len(blkt) and j0+1+len(B0)>=p)
                    st['   spill(all blkt passes): '+str(all(c0[0]<y[0] for y in blkt))]+=1
for k,v in sorted(st.items()): print(f"  {k}: {v}")
print()
for r in exs['x'][:12]: print("  LEAK:",r)
