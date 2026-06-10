#!/usr/bin/env python3
"""E6: find a sequence-level recursion for NT(M) = nrm(translate(M)).

translate's recursion: M = (x,y) # rest, split rest at first j with row0 <= x:
  translate M = P y (translate dominated) (translate tail).
NT candidate recursion: same split, but the arg is projected:
  NT M = ins y (proj y (NT' dominated)) (NT tail)   where NT' handles the arg.
Since nrm(P a b c) = ins a (proj a (nrm b)) (nrm c) and translate is structural,
NT M = nrm(translate M) automatically satisfies this with NT' = NT(dominated).
So the real question is a CLOSED FORM for proj y (NT dominated) on sequences:
   proj y (NT seg) = NT (suffix of seg from its dominant max-row1 column)?
Verify: for all standard M and all (col, seg) in the recursive decomposition
(hereditarily!), proj col.row1 (NT seg) == NT(dom-suffix(seg)) where
dom-suffix = the suffix from the LAST max-row1 column j such that iterating
this rule terminates... empirical: try suffixes from each max-row1 column and
also iterate.  Goal: identify WHICH max-row1 column is chosen.
"""
import sys
sys.path.insert(0,'.')
from wfe_explore import translate, fmt, enum_ST
from valnorm import conv, nrm, lt_term, fmtb
from mine_proj import G, proj
from mine_e5 import segments, trans_abs

def NT(seg):
    return nrm(conv(trans_abs(seg))) if seg else ()

def decomp_all(seg, out):
    """hereditary (col, dominated-seg) pairs of the translate-recursion."""
    seg=list(seg)
    while seg:
        (x,y)=seg[0]; rest=seg[1:]
        i=0
        while i<len(rest) and rest[i][0]>x: i+=1
        dom=rest[:i]
        out.append(((x,y),dom))
        if dom: decomp_all(dom,out)
        seg=rest[i:]

def main():
    ST=enum_ST(seed_max_v=4,oper_ns=(1,2,3,4),max_len=13,rounds=7)
    NF=sorted({tuple(M) for M in ST},key=str)
    total=fire=agree_first=agree_last=agree_any=mis=0
    which={}
    ex=[]
    for M in NF:
        pairs=[]
        decomp_all(list(M),pairs)
        for (col,seg) in pairs:
            if not seg: continue
            a=col[1]
            nt=NT(seg)
            p=proj(a,nt)
            total+=1
            if p==nt: continue
            fire+=1
            r1=[c[1] for c in seg]
            mx=max(r1)
            idxs=[j for j,c in enumerate(seg) if c[1]==mx]
            hits=[j for j in idxs if NT(seg[j:])==p]
            if hits:
                agree_any+=1
                if hits[0]==idxs[0]: agree_first+=1
                if hits[-1]==idxs[-1] and idxs[-1] in hits: agree_last+=1
                which.setdefault((len(idxs),tuple(j in hits for j in range(len(idxs)))[:4]),0)
                which[(len(idxs),tuple(j in hits for j in range(len(idxs)))[:4])]+=1
            else:
                mis+=1
                if len(ex)<3: ex.append((M,col,seg,p))
    print(f'positions={total} fire={fire} agree_any={agree_any} mismatch={mis}')
    print(f'  of agreeing: first-max-col hit={agree_first}, last-max-col hit={agree_last}')
    print('  hit patterns (n_maxcols, which-hit):', dict(sorted(which.items())[:8]))
    for M,col,seg,p in ex:
        print(' M=',''.join(f'({x},{y})' for x,y in M))
        print(' col=',col,' seg=',''.join(f'({x},{y})' for x,y in seg))
        print(' p =',fmtb(p)[:70])

if __name__=='__main__':
    main()
