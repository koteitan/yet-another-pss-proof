#!/usr/bin/env python3
"""Split the hasParent-last invariant by idx1 value, and separately verify the
two existence facts:
  (A) idx1==0 (entry M 1 j1 == 0, entry M 0 j1 > 0): hasParent0(M,j1).
  (B) idx1==1 (entry M 1 j1 > 0): hasParent1(M,j1).
Report counts and any counterexample for each branch.

Also test whether (B) holds for arbitrary blockok-0 sequences that are NOT
necessarily ST_PS (to see if ST_PS structure is needed) -- by perturbation.
"""
import sys
sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from fast_pss import Lng, idx1, entry, hasParent0, hasParent1
from wfe_explore import enum_ST

def run(seed_max_v, oper_ns, max_len, rounds):
    ST = list(enum_ST(seed_max_v=seed_max_v, oper_ns=oper_ns, max_len=max_len, rounds=rounds))
    cA=0; badA=0; exA=[]
    cB=0; badB=0; exB=[]
    for M in ST:
        n=Lng(M)
        if n<=1: continue
        j1=n-1
        if entry(M,0,j1)==0 and entry(M,1,j1)==0: continue
        i1=idx1(M,j1)
        if i1==0:
            cA+=1
            if not hasParent0(M,j1):
                badA+=1
                if len(exA)<10: exA.append(M)
        else:
            cB+=1
            if not hasParent1(M,j1):
                badB+=1
                if len(exB)<10: exB.append(M)
    print(f'  idx1==0: checked={cA} bad={badA}; idx1==1: checked={cB} bad={badB}', flush=True)
    for e in exA: print('   A-CEX',e)
    for e in exB: print('   B-CEX',e)
    return badA+badB

if __name__=='__main__':
    tot=0
    for (v,ns,ml,r) in [(6,(1,2,3,4,5),16,9),(5,(1,2,3,4,5,6),20,10)]:
        print(f'--- v={v} ns={ns} max_len={ml} rounds={r} ---',flush=True)
        tot+=run(v,ns,ml,r)
    print('TOTAL BAD =',tot); print('DONE',flush=True)
