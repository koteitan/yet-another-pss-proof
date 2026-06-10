#!/usr/bin/env python3
"""Check the recursion-seam premises for projE_ii same-cut:
   T = msfx S must satisfy ST_snocokS_gen's premises against q:
     INV:  fst (hd T) <= fst q
     INV2: all x in T. fst (hd T) <= fst x   (head row0 minimal)
   on all same-cut both-fire segprov positions.
"""
import sys
sys.path.insert(0,'.')
from wfe_explore import translate, fmt, enum_ST
from valnorm import conv, nrm, lt_term, fmtb
from mine_proj import proj
from mine_e6 import NT
from mine_fire4 import msfx

def main():
    ST=enum_ST(seed_max_v=4,oper_ns=(1,2,3,4),max_len=13,rounds=7)
    n=inv_bad=inv2_bad=0
    ex=[]
    for M in ST:
        if len(M)<2: continue
        q=M[-1]
        for i in range(len(M)-1):
            pp=M[i]; S=list(M[i+1:-1])
            if not S: continue
            if not all(pp[0]<r[0] for r in S): continue
            if not pp[0]<q[0]: continue
            u=pp[1]
            x=NT(S); x2=NT(S+[q])
            if proj(u,x)==x or proj(u,x2)==x2: continue
            m=max(c[1] for c in S)
            if q[1]>m: continue     # q-cut, handled separately
            n+=1
            T=msfx(S)
            if not T[0][0]<=q[0]:
                inv_bad+=1
                if len(ex)<4: ex.append(('INV',M,i,T))
            if not all(T[0][0]<=x[0] for x in T):
                inv2_bad+=1
                if len(ex)<4: ex.append(('INV2',M,i,T))
    print(f'same-cut both-fire positions: {n}  INV-fail: {inv_bad}  INV2-fail: {inv2_bad}')
    for k,M,i,T in ex:
        print(f' {k}: i={i} M={"".join(f"({x},{y})" for x,y in M)}')
        print(f'    T={"".join(f"({x},{y})" for x,y in T)}')

if __name__=='__main__':
    main()
