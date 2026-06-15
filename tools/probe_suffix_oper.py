#!/usr/bin/env python3
"""Test the SUFFIX-CLOSURE induction step for ST_PS.

Hypothesis (SUF): if M in ST_PS, then every row-0-headed nonempty suffix S of M
is in ST_PS.  We want to prove this by induction on ST_PS (diag/oper).  The hard
case is oper: M[n] = take j0 M ++ n tiled blocks.  We test what row-0-headed
suffixes of M[n] look like, to find the induction-step argument.

Concretely, for M in ST_PS and the oper image N=M[n], enumerate each row-0-headed
suffix S of N and classify:
  (a) S is a row-0-headed suffix of M itself (so IH on M gives S in ST_PS); OR
  (b) S spans into the tiled region.
Print the distribution and look at case (b) shapes.
"""
import sys, itertools
sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from fast_pss import diagSeq, oper, Lng
from wfe_explore import enum_ST

ST=list(enum_ST(seed_max_v=6,oper_ns=(1,2,3,4,5),max_len=18,rounds=10))
STset=set(ST)
print('corpus',len(ST),flush=True)

# For the induction we only need: N = M[n] with M in ST_PS, 1<=n. For each
# row-0-headed suffix S of N, is S in ST_PS (corpus)?  And: is S a row0-suffix
# of M, OR does S equal M[m] for some m, OR a row0-suffix of some tiled copy?
def row0_suffixes(N):
    return [tuple(N[i:]) for i in range(len(N)) if N[i][0]==0]

not_in=0; tot=0; ex=[]
caseA=caseB=0
for M in ST:
    if Lng(M)<=1: continue
    for n in (1,2,3):
        N=oper(list(M),n)
        for i in range(len(N)):
            if N[i][0]!=0: continue
            S=tuple(N[i:]); tot+=1
            if S not in STset:
                not_in+=1
                if len(ex)<10: ex.append((M,n,N,i,S))
print(f'(SUF) row0-suffixes of M[n], M in corpus: tot={tot} not-in-corpus={not_in}',flush=True)
for M,n,N,i,S in ex[:8]:
    print('  M=',M,'n=',n); print('   N=',N); print('   suffix@',i,'=',S)
print('DONE',flush=True)
