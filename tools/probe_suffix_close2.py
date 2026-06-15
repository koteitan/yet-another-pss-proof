#!/usr/bin/env python3
"""Find the induction witness for suffix-closure.

For N = oper M n (M in ST_PS), and a row-0-headed suffix S of N (S != N, i.e.
the suffix starts at index i>=1), classify S:
  Let G = take j0 M (the green prefix copied verbatim), and the tiled part
  T = concat(blk_k). N = G ++ T.
  Case (i)  : i < len(G): S = M[i:] ++ T'... no, S = N[i:] = G[i:] ++ T. Hmm.
  We instead test the GLOBAL recursive witness:
   (W) every row-0-headed suffix S of N (any N in ST_PS, len>=1) is EITHER
       a row-0-headed suffix of a STRICTLY SHORTER ST_PS element we can build,
       OR S == N.
  Practically, just verify membership against a FRESH independent closure that
  goes deeper, to confirm tail-zone (drop first arg-block) membership beyond the
  finite-corpus artifact: test the EXACT tail_zone, not all suffixes, with a
  proper membership oracle = BFS reachability check that tries to reach S from
  some diagSeq within a depth bound.
"""
import sys, itertools
sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from fast_pss import diagSeq, oper, Lng
from wfe_explore import enum_ST

def dropW(r): return list(itertools.dropwhile(lambda q: 0 < q[0], r))

# A much deeper closure as membership oracle
DEEP=set(enum_ST(seed_max_v=8,oper_ns=(1,2,3,4,5,6),max_len=26,rounds=14))
print('DEEP oracle size',len(DEEP),flush=True)

# test tail-zone of a moderate corpus against DEEP
MID=list(enum_ST(seed_max_v=6,oper_ns=(1,2,3,4,5),max_len=16,rounds=9))
nonempty_notin=0; tot=0; ex=[]
for M in MID:
    if not M or M[0][0]!=0: continue
    tz=tuple(dropW(list(M[1:])))
    if not tz: continue
    tot+=1
    if tz not in DEEP:
        nonempty_notin+=1
        if len(ex)<10: ex.append((M,tz))
print(f'tail-zone(nonempty) against DEEP oracle: tot={tot} not-in={nonempty_notin}',flush=True)
for M,tz in ex[:10]: print(' M=',M); print('   tz=',tz)
print('DONE',flush=True)
