#!/usr/bin/env python3
"""Weakest-premise test for the E6 master lemma:

  For ALL nonempty contiguous sublists S of standard hosts and ALL u in 0..6:
     pfire u (NT S)  ==>  proj u (NT S) = NT (msfx S)
  where msfx S = suffix from the FIRST max-row1 column.

If this holds, the Isabelle premise is just 'S contiguous sublist of M : ST_PS'
with u universally quantified -- no host column, no domination needed.
"""
import sys
sys.path.insert(0,'.')
from wfe_explore import translate, fmt, enum_ST
from valnorm import conv, nrm, lt_term, fmtb
from mine_proj import G, proj
from mine_e6 import NT

def msfx(seg):
    r1=[c[1] for c in seg]
    m=max(r1)
    return seg[r1.index(m):]

def main():
    ST=enum_ST(seed_max_v=4,oper_ns=(1,2,3,4),max_len=13,rounds=7)
    NF=sorted({tuple(M) for M in ST},key=str)
    segs=set()
    for M in NF:
        L=len(M)
        for i in range(L):
            for j in range(i+1,min(L,i+11)+1):
                segs.add(tuple(M[i:j]))
    print('contiguous sublists:',len(segs),flush=True)
    tot=fires=bad=0; ex=[]
    for S in segs:
        S=list(S)
        nt=NT(S)
        for u in range(0,7):
            tot+=1
            p=proj(u,nt)
            if p==nt: continue
            fires+=1
            if p!=NT(msfx(S)):
                bad+=1
                if len(ex)<8: ex.append((S,u,p))
    print(f'(S,u) pairs={tot} fires={fires} suffix-mismatch={bad}')
    for S,u,p in ex:
        print(f' u={u} S={"".join(f"({x},{y})" for x,y in S)}')
        print(f'   proj={fmtb(p)[:70]}')
        print(f'   NTms={fmtb(NT(msfx(S)))[:70]}')

if __name__=='__main__':
    main()
