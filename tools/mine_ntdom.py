#!/usr/bin/env python3
"""NT_dom statistics on the fbseg closure: for pieces c#rest with
T = dropWhile (fst c <) rest = c1#rest1, classify:
  - level: fst c1 = fst c (eq) vs fst c1 < fst c (drop)
  - subscript: snd c1 vs snd c  (NT_dom claims snd c1 <= snd c always)
  - on snd-tie: olt A B1?  (NT_dom claims never)
Also for the drop case: is snd c1 <= snd c provable prospects — check
distribution of (fst c - fst c1, snd c - snd c1).
"""
import sys
sys.path.insert(0,'.')
from wfe_explore import translate, fmt, enum_ST
from valnorm import conv, nrm, lt_term, fmtb
from mine_proj import proj
from mine_e6 import NT

def main():
    ST=enum_ST(seed_max_v=4,oper_ns=(1,2,3,4),max_len=12,rounds=7)
    base=set()
    for M in ST:
        L=len(M)
        for i in range(L-1):
            a,u=M[i]
            k=i+1
            while k<L and M[k][0]>a:
                base.add((u,tuple(M[i+1:k+1])))
                k+=1
    seen=set(base); frontier=list(base)
    while frontier:
        nf=[]
        for (u,S) in frontier:
            c,rest=S[0],list(S[1:])
            i=0
            while i<len(rest) and rest[i][0]>c[0]: i+=1
            K,T=tuple(rest[:i]),tuple(rest[i:])
            for p in ((c[1],K) if K else None,(u,T) if T else None):
                if p and p not in seen:
                    seen.add(p); nf.append(p)
        frontier=nf
    neq=ndrop=sub_viol=tie=tie_viol=0
    dropdist={}
    for (u,S) in seen:
        c,rest=S[0],list(S[1:])
        i=0
        while i<len(rest) and rest[i][0]>c[0]: i+=1
        K,T=rest[:i],rest[i:]
        if not T: continue
        c1,rest1=T[0],T[1:]
        if c1[0]==c[0]: neq+=1
        else: ndrop+=1
        if c1[1]>c[1]:
            sub_viol+=1
            continue
        if c1[1]==c[1]:
            tie+=1
            i1=0
            while i1<len(rest1) and rest1[i1][0]>c1[0]: i1+=1
            K1=rest1[:i1]
            A=proj(c[1],NT(K))
            B1=proj(c1[1],NT(K1))
            if lt_term(A,B1): tie_viol+=1
        if c1[0]<c[0]:
            d=(c[0]-c1[0], c[1]-c1[1])
            dropdist[d]=dropdist.get(d,0)+1
    print(f'adjacent pairs: eq={neq} drop={ndrop}')
    print(f'subscript violations (snd c1 > snd c): {sub_viol}')
    print(f'ties: {tie}  tie-arg violations (olt A B1): {tie_viol}')
    print('drop (dlevel, dsub) dist:', dict(sorted(dropdist.items())[:12]))

if __name__=='__main__':
    main()
