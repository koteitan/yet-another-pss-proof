#!/usr/bin/env python3
"""E6_lpl premise-weakening test.

Weak class WS: S' = M[j:k] contiguous, exists i<j: all of M[i+1:k] has
row0 > fst M[i]  (dominated context, NO forest-boundary condition),
and snd (hd S') = maxr1 S'  (head-max).

LPL claim: for every sub-piece C = S'[a:b] with a>0, C nonempty,
snd (hd C) = maxr1 S':   olt (NT C) (NT S').

Also report the dual (DOM-deep shape): with S'' = msfx-style head-max piece,
same claim — covered by the same enumeration.
"""
import sys
sys.path.insert(0,'.')
from wfe_explore import translate, fmt, enum_ST
from valnorm import conv, nrm, lt_term, fmtb
from mine_e6 import NT

def main():
    ST=enum_ST(seed_max_v=4,oper_ns=(1,2,3,4),max_len=12,rounds=7)
    seen=set()
    tot=viol=0
    ex=[]
    ntc={}
    def NTC(S):
        S=tuple(S)
        if S not in ntc: ntc[S]=NT(list(S))
        return ntc[S]
    for M in ST:
        L=len(M)
        for i in range(L-1):
            a,u=M[i]
            k=i+1
            while k<L and M[k][0]>a:
                k+=1
            # region M[i+1:k] dominated by M[i]; pieces S'=M[j:kk]
            for j in range(i+1,k):
                for kk in range(j+1,k+1):
                    Sp=tuple(M[j:kk])
                    m=max(c[1] for c in Sp)
                    if Sp[0][1]!=m: continue
                    if Sp in seen: continue
                    seen.add(Sp)
                    ntS=NTC(Sp)
                    for aa in range(1,len(Sp)):
                        for bb in range(aa+1,len(Sp)+1):
                            C=Sp[aa:bb]
                            if C[0][1]!=m: continue
                            tot+=1
                            if not lt_term(NTC(C),ntS):
                                viol+=1
                                if len(ex)<6: ex.append((Sp,aa,bb))
    print(f'head-max pieces={len(seen)}  (S,C) tests={tot}  LPL violations={viol}')
    for Sp,aa,bb in ex:
        print(f'  S={"".join(f"({x},{y})" for x,y in Sp)}  C=[{aa}:{bb}]')
        print(f'   NTS={fmtb(NTC(Sp))[:70]}')
        print(f'   NTC={fmtb(NTC(Sp[aa:bb]))[:70]}')

if __name__=='__main__':
    main()
