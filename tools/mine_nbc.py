#!/usr/bin/env python3
"""No-boundary-crossing fact: on base pairs (u,S) with fire,
   every ancestor of j0 (in S's row0-forest) has its dominated run extending
   to the END of S; equivalently every column at position >= j0 is dominated
   by every ancestor of j0:
       forall a in ancestors(j0), forall l >= j0:  fst S[l] > fst S[a]
   Also: j0 itself: do all later columns satisfy fst > fst S[j0]?  (i.e. is
   msfx S a single tree = run of its head?)  -- separate count.
"""
import sys
sys.path.insert(0,'.')
from wfe_explore import translate, fmt, enum_ST
from valnorm import conv, nrm, lt_term, fmtb
from mine_proj import proj
from mine_e6 import NT
from mine_fire4 import msfx
from mine_fire3 import ancestors, j0

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
    nf=anc_bad=hd_single=hd_multi=0
    ex=[]
    for (u,S) in base:
        Sl=list(S)
        nt=NT(Sl)
        if proj(u,nt)==nt: continue
        nf+=1
        j=j0(Sl)
        anc=ancestors(Sl,j)
        ok=all(Sl[l][0]>Sl[a][0] for a in anc for l in range(j,len(Sl)))
        if not ok:
            anc_bad+=1
            if len(ex)<5: ex.append((u,Sl,j,anc))
        if all(Sl[l][0]>Sl[j][0] for l in range(j+1,len(Sl))): hd_single+=1
        else: hd_multi+=1
    print(f'fire base pairs={nf}  ancestor-run-to-end FAIL={anc_bad}')
    print(f'msfx single-tree={hd_single}  multi-tree={hd_multi}')
    for u,S,j,anc in ex:
        print(f' u={u} j0={j} anc={anc} S={"".join(f"({a},{b})" for a,b in S)}')

if __name__=='__main__':
    main()
