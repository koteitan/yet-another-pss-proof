#!/usr/bin/env python3
"""Test:
T1 (min-no-fire): for firing x, no corpus no-fire point z with x <= z < proj a x.
T2 (CRUX): proj a injective on full A_a = {nrm-args at subscript-a positions}.
T3: how often do A_a elements fire (per subscript)?
"""
import sys, itertools
sys.path.insert(0,'.')
from wfe_explore import translate, olt, maxsub, fmt, enum_ST
from valnorm import conv, nrm, lt_term, fmtb
from mine_proj import G, proj

def nofire(u,b):
    return all(lt_term(g,b) for g in G(u,b))

def main():
    ST=enum_ST(seed_max_v=4,oper_ns=(1,2,3,4),max_len=14,rounds=8)
    NF={translate(M) for M in ST}
    def sub3(t):
        if t==(): return
        a,b,c=t
        yield t; yield from sub3(b); yield from sub3(c)
    blocks=set()
    for w in NF:
        for s in sub3(w): blocks.add(s)
    ncache={}
    def N(w):
        if w not in ncache: ncache[w]=nrm(conv(w))
        return ncache[w]
    A={}
    for w in blocks:
        a,b,c=w
        A.setdefault(a,set()).add(N(b))
    print('|A_a| per a:', {a:len(s) for a,s in sorted(A.items())}, flush=True)

    # T2 full injectivity + collect projections
    for a in sorted(A):
        pr={}
        for x in A[a]:
            px=proj(a,x)
            pr.setdefault(px,[]).append(x)
        dup={k:v for k,v in pr.items() if len(v)>1}
        print(f'T2 a={a}: |A|={len(A[a])} |proj-image|={len(pr)} collisions={len(dup)}')
        for k,v in list(dup.items())[:3]:
            print('   px=',fmtb(k)[:60])
            for x in v[:3]: print('      x=',fmtb(x)[:60])

    # T3 firing rate
    for a in sorted(A):
        f=sum(1 for x in A[a] if proj(a,x)!=x)
        print(f'T3 a={a}: firing {f}/{len(A[a])}')

    # T1 min-no-fire approx: universe = all nrm-images + their projections
    U=set()
    for a in A:
        for x in A[a]:
            U.add(x); U.add(proj(a,x))
    U=sorted(U,key=str)
    print('universe',len(U),flush=True)
    for a in sorted(A):
        nofU=[z for z in U if nofire(a,z)]
        bad=0; ex=[]
        for x in A[a]:
            px=proj(a,x)
            if px==x: continue
            for z in nofU:
                if (lt_term(x,z) or x==z) and lt_term(z,px):
                    bad+=1
                    if len(ex)<3: ex.append((x,z,px))
                    break
        print(f'T1 a={a}: min-no-fire violations={bad}')
        for x,z,px in ex:
            print('   x =',fmtb(x)[:55]); print('   z =',fmtb(z)[:55]); print('   px=',fmtb(px)[:55])

if __name__=='__main__':
    main()
