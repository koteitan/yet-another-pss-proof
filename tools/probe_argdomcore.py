import sys
sys.path.insert(0,'.')
from probe_bmocf_ancestor import enum_depth
from probe_copycrux import pairlt, seqlex, sle, shiftr0
def spineOK(A,L,w):
    for i,x in enumerate(A):
        if x[0] < L and all(x[0] < y[0] for y in A[i+1:]):
            if not (w <= x[1]): return False
    return True
for rounds,ml in [(6,11),(8,11)]:
    hosts=[tuple(M) for M in enum_depth(5,(1,2,3,4,5),ml,rounds) if len(M)>=2 and M[0]==(0,0)]
    hosts=sorted(set(hosts)); nI=nV=0; exs=[]; nSpine=0
    for M in hosts:
        Ml=list(M); L=len(Ml)
        for i in range(L):
            u,w=Ml[i]
            for j in range(i+1,L):
                if Ml[j][1]!=w: continue
                e=Ml[j][0]-u
                if e<=0: continue
                A1=Ml[i+1:j]
                if not all(u<x[0] for x in A1): continue
                rest=Ml[j+1:]
                B=[];k=0
                while k<len(rest) and u+e<rest[k][0]: B.append(rest[k]);k+=1
                A2=[]
                while k<len(rest) and u<rest[k][0]: A2.append(rest[k]);k+=1
                Z=rest[k:]
                if A2 and not (A2[0][0]<=u+e): continue
                if Z and not (Z[0][0]<=u): continue
                if not spineOK(A1,u+e,w): continue
                nSpine+=1; nI+=1
                A=A1+[(u+e,w)]+B+A2
                if not sle(B, shiftr0(e,A)):
                    nV+=1
                    if len(exs)<4: exs.append((M,i,j,tuple(B),tuple(shiftr0(e,A))))
    print(f"[+{rounds}] ArgDomCore instances(SpineOK-passing)={nI}  ***VIOLATIONS={nV}***")
    for e_ in exs: print("   viol:",e_)
