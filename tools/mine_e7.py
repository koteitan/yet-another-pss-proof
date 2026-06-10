#!/usr/bin/env python3
"""E7: classify the first-difference structure of NT(M[n]) vs NT(M) over all
expansion steps in the corpus, to derive the Isabelle case tree for
nrm_step_dec.

Classification at the first structural divergence walking both terms
simultaneously (head subscript / arg / tail):
  - 'sub':  head subscripts differ (smaller on M[n] side)
  - 'arg':  same subscript, args differ -> recurse; record depth
  - 'tail': same head, tails differ -> recurse; record breadth-position
Also record whether the divergence happens inside a region where the
suffix-discard (proj fire) acted on one side but not the other.
"""
import sys
sys.path.insert(0,'.')
from fast_pss import oper, Lng
from wfe_explore import translate, fmt, enum_ST
from valnorm import conv, nrm, lt_term, fmtb

def firstdiff(a,b,path=()):
    """a,b list-of-principals; returns (kind, path)."""
    i=0
    while i<len(a) and i<len(b):
        if a[i]==b[i]:
            i+=1; continue
        _,u,x=a[i]; _,v,y=b[i]
        if u!=v: return ('sub' if u<v else 'sub-REV', path+(i,))
        return firstdiff(x,y,path+(i,'arg'))
    if len(a)<len(b): return ('prefix',path+(i,))
    if len(a)>len(b): return ('prefix-REV',path+(i,))
    return ('equal',path)

def main():
    ST=enum_ST(seed_max_v=4,oper_ns=(1,2,3),max_len=13,rounds=6)
    stats={}; depth={}
    exREV=[]
    cnt=0
    for M in ST:
        if Lng(M)<=1: continue
        for n in (1,2,3):
            N=tuple(oper(list(M),n))
            a=nrm(conv(translate(N)))
            b=nrm(conv(translate(M)))
            kind,path=firstdiff(a,b)
            cnt+=1
            stats[kind]=stats.get(kind,0)+1
            d=sum(1 for p in path if p=='arg')
            depth[d]=depth.get(d,0)+1
            if 'REV' in kind or kind=='equal':
                if len(exREV)<4: exREV.append((M,n,kind,a,b))
    print('expansion pairs:',cnt)
    print('first-diff kinds:',stats)
    print('arg-depth dist:',dict(sorted(depth.items())))
    for M,n,kind,a,b in exREV:
        print(kind,'M=',''.join(f'({x},{y})' for x,y in M),'n=',n)
        print('  NT(M[n])=',fmtb(a)[:70]); print('  NT(M)  =',fmtb(b)[:70])

if __name__=='__main__':
    main()
