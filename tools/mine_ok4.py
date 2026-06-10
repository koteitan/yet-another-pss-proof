#!/usr/bin/env python3
"""Mine the per-position bound for escaping criticals at re-entry/stay args.

For every principal subterm position P f Y (within nrm-images of standard
blocks) with lead(Y) <= f  (re-entry or stay), collect criticals
g in {Y} u Gterm_0(Y) and find which candidate bounds always dominate them:
   B1: wrapper        P f Y Z
   B2: enclosing head (the whole principal containing this position chain)
Also: is (0,0)(1,1)(2,0)(3,1)(4,2) standard?
"""
import sys
sys.path.insert(0,'.')
from wfe_explore import translate, olt, maxsub, fmt, enum_ST
from valnorm import conv, nrm, lt_term, fmtb

def lead(b): return b[0][1] if b else None

def Gall(a):
    """all args of principals reachable anywhere (u=0 collection)."""
    out=[]
    for p in a:
        _,v,b=p
        out.append(b); out+=Gall(b)
    return out

def positions(t, ctx):
    """yield (f, Y, ctxhead) for principal positions; ctxhead = outermost
    enclosing principal (as term)."""
    for i,p in enumerate(t):
        _,f,Y=p
        head=(p,) if ctx is None else ctx
        yield f,Y,head
        yield from positions(Y, head)

def main():
    ST=enum_ST(seed_max_v=4,oper_ns=(1,2,3,4),max_len=14,rounds=8)
    print('corpus',len(ST))
    tgt=((0,0),(1,1),(2,0),(3,1),(4,2))
    print('(0,0)(1,1)(2,0)(3,1)(4,2) standard?', tuple(tgt) in ST)
    tgt2=((0,0),(1,1),(2,0),(3,1),(4,2),(5,0))
    print('... with (5,0):', tuple(tgt2) in ST)

    NF={translate(M) for M in ST}
    terms={nrm(conv(w)) for w in NF}
    # also raw converted blocks (pre-nrm) since the induction walks raw terms:
    raw={conv(w) for w in NF}

    for name,fam in [('nrm-images',terms),('raw',raw)]:
        viol1=viol2=tot=0; ex=[]
        for t in fam:
            for f,Y,head in positions(t,None):
                if Y and lead(Y) is not None and lead(Y)<=f:
                    wrapper=(('D',f,Y),)
                    for g in [Y]+Gall(Y):
                        if not g: continue
                        tot+=1
                        if not lt_term(g,wrapper):
                            viol1+=1
                            if len(ex)<4: ex.append((f,Y,g,head,'B1'))
                        if not lt_term(g,head):
                            viol2+=1
                            if len(ex)<4: ex.append((f,Y,g,head,'B2'))
        print(f'{name}: checks={tot} B1(wrapper)-viol={viol1} B2(head)-viol={viol2}')
        for f,Y,g,head,tag in ex[:4]:
            print(f'  {tag} f={f} Y={fmtb(Y)[:50]}')
            print(f'     g={fmtb(g)[:60]}')
            print(f'     head={fmtb(head)[:60]}')

if __name__=='__main__':
    main()
