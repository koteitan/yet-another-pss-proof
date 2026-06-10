#!/usr/bin/env python3
"""Define NTseq by the uniform recursion and verify NTseq(M) == nrm(translate M)
on the whole corpus (all standard forms), including no-fire cases.

NTseq([]) = Z
NTseq((x,y)#rest):
   split rest at first j with row0 <= x:  dom = rest[:j], tail = rest[j:]
   sfx = dom[i:] where i = first index attaining max row1 of dom  (dom=[] -> [])
   NTseq = P y (NTseq sfx) (NTseq tail)
(no ins/absorption, no proj iteration!)
"""
import sys
sys.path.insert(0,'.')
from wfe_explore import translate, fmt, enum_ST
from valnorm import conv, nrm, lt_term, fmtb

def NTseq(M):
    M=list(M)
    if not M: return ()
    (x,y)=M[0]; rest=M[1:]
    i=0
    while i<len(rest) and rest[i][0]>x: i+=1
    dom,tail=rest[:i],rest[i:]
    if dom:
        mx=max(c[1] for c in dom)
        k=next(j for j,c in enumerate(dom) if c[1]==mx)
        sfx=dom[k:]
    else:
        sfx=[]
    return (y, NTseq(sfx), NTseq(tail))

def to_list(t):
    out=[]
    while t!=():
        a,b,c=t
        out.append(('D',a,to_list(b)))
        t=c
    return tuple(out)

def main():
    ST=enum_ST(seed_max_v=4,oper_ns=(1,2,3,4),max_len=14,rounds=8)
    print('corpus',len(ST))
    ok=bad=0; ex=[]
    for M in ST:
        a=to_list(NTseq(list(M)))
        b=nrm(conv(translate(M)))
        if a==b: ok+=1
        else:
            bad+=1
            if len(ex)<5: ex.append((M,a,b))
    print(f'NTseq == nrm.translate : {ok} ok, {bad} mismatch')
    for M,a,b in ex:
        print(' M =',''.join(f'({x},{y})' for x,y in M))
        print(' NTseq =',fmtb(a)[:75])
        print(' nrm.tr=',fmtb(b)[:75])

if __name__=='__main__':
    main()
