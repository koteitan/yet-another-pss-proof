#!/usr/bin/env python3
"""Restrict head-anchored ProjFixesNrm to genuine NF (translate-image) terms and
their P-nodes, exactly as oV_nrm_of_psi_proj_onNrm's induction reaches them:
for every P a b c node in t = translate(M), obligation proj a (nrm b) == nrm b.
"""
import sys
sys.setrecursionlimit(100000)
sys.path.insert(0, '.')
from wfe_explore import Z, P, olt, translate, enum_ST
from audit_projfix_wf3 import Gterm, wf3, proj, nrm

def pnodes(t):
    """yield every P-node (a,b,c) reached by structural induction on t."""
    if t == (): return
    a,b,c = t
    yield (a,b,c)
    yield from pnodes(b)
    yield from pnodes(c)

def lead(t): return 0 if t==() else t[0]

def main():
    for rounds in (4,6,8):
        ST = enum_ST(seed_max_v=3, oper_ns=(1,2,3), max_len=11, rounds=rounds)
        total=viol=0; ex=[]
        for M in ST:
            t = translate(M)
            for (a,b,c) in pnodes(t):
                nb = nrm(b)
                total += 1
                if proj(a, nb) != nb:
                    viol += 1
                    if len(ex)<6: ex.append((M,a,b,nb,proj(a,nb)))
        print(f'rounds={rounds}  #NF={len(ST)}  P-node checks={total}  violations={viol}')
        for M,a,b,nb,p in ex:
            print(f'   VIOL a={a} nrm(b)={nb} lead={lead(nb)} proj={p}')
            print(f'        from M={M}')

if __name__ == '__main__':
    main()
