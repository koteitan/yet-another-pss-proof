#!/usr/bin/env python3
"""E5: sequence-side characterization of proj.

For a standard host M and its translate t = translate(M): the depth-1 args
(b of P a b c at spine positions) correspond to segments of M.  Hypothesis:
proj a (nrm (arg)) = nrm (translate (suffix of the segment from some max-row1
column)).  We test the simplest global version: for the WHOLE term w=translate M
and each top-level arg b (subscript 0 positions): proj 0 (nrm b) vs
nrm(translate(suffix of the b-segment from its LAST maximal-row1 column)).
Report agreement statistics; refine if mismatch.
"""
import sys
sys.path.insert(0,'.')
from wfe_explore import translate, fmt, enum_ST
from valnorm import conv, nrm, lt_term, fmtb
from mine_proj import G, proj

def segments(M):
    """top-level decomposition of M: head column + dominated segment, like
    translate: returns list of (col, seg) for each top summand."""
    M=list(M)
    out=[]
    while M:
        x,y=M[0]
        rest=M[1:]
        i=0
        while i<len(rest) and rest[i][0]>x: i+=1
        out.append(((x,y), rest[:i]))
        M=rest[i:]
    return out

def shiftseq(seg):
    """segment as standalone: keep absolute row1 (subscripts absolute)."""
    return [tuple(c) for c in seg]

def trans_abs(seg):
    """translate but using absolute row1 as subscript and row0 relative structure."""
    seg=list(seg)
    if not seg: return ()
    (x,y)=seg[0]; rest=seg[1:]
    i=0
    while i<len(rest) and rest[i][0]>x: i+=1
    return (y, trans_abs(rest[:i]), trans_abs(rest[i:]))

def main():
    ST=enum_ST(seed_max_v=4,oper_ns=(1,2,3,4),max_len=13,rounds=7)
    NF=sorted({tuple(M) for M in ST},key=str)
    agree=mis=fire_cases=0
    ex=[]
    for M in NF:
        for (col,seg) in segments(M):
            a=col[1]
            if not seg: continue
            b=trans_abs(seg)
            nb=nrm(conv(b))
            pb=proj(a,nb)
            if pb==nb: continue
            fire_cases+=1
            # candidate: suffix from the LAST column attaining max row1
            r1=[c[1] for c in seg]
            mx=max(r1)
            # candidates: each suffix starting at a max-row1 column
            cands=[]
            for j,c in enumerate(seg):
                if c[1]==mx:
                    cands.append(nrm(conv(trans_abs(seg[j:]))))
            if any(pb==cd for cd in cands):
                agree+=1
            else:
                mis+=1
                if len(ex)<4: ex.append((M,col,seg,pb,cands))
    print(f'fire cases={fire_cases} suffix-agree={agree} mismatch={mis}')
    for M,col,seg,pb,cands in ex:
        print(' M  =',''.join(f'({x},{y})' for x,y in M))
        print(' col=',col,'seg=',''.join(f'({x},{y})' for x,y in seg))
        print(' pb =',fmtb(pb)[:70])
        for cd in cands[:3]: print(' cd =',fmtb(cd)[:70])

if __name__=='__main__':
    main()
