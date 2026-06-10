#!/usr/bin/env python3
"""Case-tree stats for ST_snoc_C on standard hosts:
at every (C)-position of the ST_snocok recursion, classify:
 (i)  both no-fire
 (ii) both fire
 (iii) only extended side fires
 (iv) only base side fires      <- conjecture: never on standard
Also for (ii): does the divergence recurse into the same first-max suffix?
"""
import sys
sys.path.insert(0,'.')
from wfe_explore import translate, fmt, enum_ST
from valnorm import conv, nrm, lt_term, fmtb
from mine_proj import G, proj

def trans(C): return nrm(conv(translate(list(C))))

def fires(u,b):
    return any(not lt_term(g,b) for g in G(u,b))

stats={}
def walk(C,q):
    if not C: return
    p,rest=C[0],C[1:]
    i=0
    while i<len(rest) and rest[i][0]>p[0]: i+=1
    T=rest[i:]
    if not T:
        if p[0]<q[0]:
            x,x2=trans(rest),trans(list(rest)+[q])
            f1,f2=fires(p[1],x),fires(p[1],x2)
            k=('nofire-nofire' if not f1 and not f2 else
               'fire-fire' if f1 and f2 else
               'ext-only-fires' if f2 else 'base-only-fires')
            stats[k]=stats.get(k,0)+1
            walk(rest,q)  # recurse deeper too (the suffix recursion analog)
    else:
        walk(T,q)

def main():
    ST=enum_ST(seed_max_v=4,oper_ns=(1,2,3,4),max_len=13,rounds=7)
    for M in ST:
        if len(M)<2: continue
        walk(list(M[:-1]),M[-1])
    print('case stats:',stats)

if __name__=='__main__':
    main()
