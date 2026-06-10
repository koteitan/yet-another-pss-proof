#!/usr/bin/env python3
"""Mine the structural facts needed for the nrm_order_pres induction.

E1: does ins ever absorb on nrm-images of standard blocks?   (expect never)
E2: is proj a strictly monotone on nrm-args at subscript-a positions?
E3: explicit shape: proj a (nrm b) = spine-max core?
E4: candidate hereditary condition killing y_2:
    "every G_a-violation in a principal D_a(b) lies on the climb spine of b
     (reachable via first-arguments only), never inside a re-entry argument"
"""
import sys, itertools
sys.path.insert(0,'.')
from wfe_explore import translate, olt, maxsub, fmt, enum_ST
from valnorm import conv, nrm, lt_term, fmtb

def lead(t): return t[0][1] if t else None

def princ_lt(p,q):
    _,u,a=p; _,v,b=q
    if u!=v: return u<v
    return lt_term(a,b)

def G(u,a):
    out=[]
    for p in a:
        _,v,b=p
        if v>=u: out.append(b); out+=G(u,b)
    return out

def proj(u,b):
    while True:
        bad=[g for g in G(u,b) if not lt_term(g,b)]
        if not bad: return b
        m=bad[0]
        for h in bad[1:]:
            if lt_term(m,h): m=h
        b=m

# spine of a term (list rep): follow first principal's arg
def spineargs(b):
    """args reachable by following the FIRST principal's argument chain."""
    out=[]
    while b:
        _,v,arg=b[0]
        out.append(arg); b=arg
    return out

def subterms3(t):
    if t==(): return
    a,b,c=t
    yield t
    yield from subterms3(b); yield from subterms3(c)

def main():
    ST=enum_ST(seed_max_v=4,oper_ns=(1,2,3,4),max_len=14,rounds=8)
    NF={translate(M) for M in ST}
    blocks=set()
    for w in NF:
        for s in subterms3(w): blocks.add(s)
    blocks.discard(())
    print('corpus',len(ST),'blocks',len(blocks),flush=True)

    ncache={}
    def N(w):
        if w not in ncache: ncache[w]=nrm(conv(w))
        return ncache[w]

    # E1: absorption test: nrm(P a b c): does head of nrm c dominate (a, proj a nrm b)?
    absorb=0; ex1=[]
    for w in blocks:
        a,b,c=w
        if c==(): continue
        nc=N(c)
        if not nc: continue
        hb=proj(a,N(b))
        if princ_lt(('D',a,hb), nc[0]):
            absorb+=1
            if len(ex1)<3: ex1.append(w)
    print('E1 absorb-fires:',absorb)
    for w in ex1: print('   ',fmt(w))

    # E2: per subscript a, collect nrm-args at subscript-a positions; test proj-mono
    pos={}
    for w in blocks:
        a,b,c=w
        pos.setdefault(a,set()).add(N(b))
    for a in sorted(pos):
        xs=sorted(pos[a],key=str)
        if len(xs)>500: xs=xs[:500]
        viol=0; exx=[]
        for x,y in itertools.combinations(xs,2):
            if lt_term(x,y): lo,hi=x,y
            elif lt_term(y,x): lo,hi=y,x
            else: continue
            pl,ph=proj(a,lo),proj(a,hi)
            if not lt_term(pl,ph) and pl!=ph:
                viol+=1
                if len(exx)<2: exx.append((lo,hi,pl,ph))
            if pl==ph and lo!=hi:
                viol+=1
                if len(exx)<2: exx.append((lo,hi,pl,ph))
        print(f'E2 a={a}: args={len(xs)} proj-mono violations={viol}')
        for lo,hi,pl,ph in exx:
            print('   lo',fmtb(lo),' hi',fmtb(hi))
            print('   pl',fmtb(pl),' ph',fmtb(ph))

    # E3: proj = follow-spine-to-max? test: proj a (N b) vs explicit spine-max extraction
    def spinemax_core(u,b):
        # candidate explicit form: largest suffix-arg on the first-arg chain that
        # satisfies the G-condition... we just record agreement rate of a simple
        # candidate: the maximal element of {b} u spineargs under "last with subscript jump"
        return None
    # instead: measure how often proj fires at all, and the depth of projection
    fires=0; tot=0
    for w in blocks:
        a,b,c=w
        nb=N(b)
        tot+=1
        if proj(a,nb)!=nb: fires+=1
    print(f'E3 proj fires on {fires}/{tot} principal positions')

    # E4: violations located on climb spine only?
    bad4=0; ex4=[]
    for w in blocks:
        a,b,c=w
        nb=N(b)
        sp=set(map(tuple,spineargs(nb)))
        for g in G(a,nb):
            if not lt_term(g,nb):
                if tuple(g) not in sp:
                    bad4+=1
                    if len(ex4)<3: ex4.append((w,g))
    print('E4 off-spine G-violations:',bad4)
    for w,g in ex4:
        print('   w:',fmt(w))
        print('   g:',fmtb(g))
    # E4 on y2 for contrast:
    y1=((0,(1,(1,(),()),()),()))
    y1=(0,(1,(1,(),()),()),())
    y2=(0,(1,y1,()),())
    a,b,c=y2
    nb=nrm(conv(b))
    sp=set(map(tuple,spineargs(nb)))
    off=[g for g in G(a,nb) if not lt_term(g,nb) and tuple(g) not in sp]
    print('E4 y2 off-spine violations:',len(off),[fmtb(g) for g in off])

if __name__=='__main__':
    main()
