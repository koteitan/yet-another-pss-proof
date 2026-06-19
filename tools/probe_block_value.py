#!/usr/bin/env python3
"""Investigate the VALUE-side block monotonicity that would mirror seqlex_imp_olt:

  blockok d M  ==>  blockok d N  ==>  seqlex M N  ==>  oV(translate M) < oV(translate N)

oV value modelled by nrm(conv(translate .)) with lt_term = ordinal order (validated proxy).

Also: in the LEADING-COLUMN case (heads (d,y),(d,y') with y<y'), is it true that
oV(translate M) < psi_{y'}(oV(arg_zone N)) <= oV(translate N)?  i.e. does the whole
oV(M) stay below the leading principal of N?  And WHAT invariant on M's spine
(tail-zone row-1 subscripts) underlies it?

We hunt for the key sub-invariant:  for a blockok-d standard form M = (d,y)#r,
is every spine (tail-zone) principal's row-1 subscript <= y (the head's row-1)?
This is OT2 at the *value/translate* level.  If TRUE on NF, the subscript-jump
lemma applies and the leading case is green.
"""
import sys, itertools
sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from wfe_explore import translate, olt, fmt, enum_ST, maxsub
from valnorm import conv, nrm, lt_term, in_OT, fmtb

Z=()

def blockok(d, B):
    if not B: return True
    if B[0][0] != d: return False
    if any(p[0] < d for p in B): return False
    for j in range(len(B)-1):
        if B[j+1][0] > B[j][0]+1: return False
    return True

def seqlex(M,N):
    # column-lex: pairlt first differing, or prefix
    i=0
    while i<len(M) and i<len(N) and M[i]==N[i]: i+=1
    if i==len(M) and i==len(N): return False
    if i==len(M): return True   # M proper prefix of N
    if i==len(N): return False  # N proper prefix of M
    p,q=M[i],N[i]
    return p[0]<q[0] or (p[0]==q[0] and p[1]<q[1])

# spine (tail-zone chain) row-1 subscripts of a term, i.e. the chain via 3rd comp
def tail_subs(t):
    s=[]
    while t!=Z:
        a,b,c=t
        s.append(a)
        t=c
    return s

def main():
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4,5), max_len=16, rounds=7)
    seen=set(); NF=[]
    for M in ST:
        M=tuple(M)
        if M not in seen:
            seen.add(M); NF.append(M)
    print(f"#distinct ST_PS seqs: {len(NF)}")

    # INVARIANT TEST: for every standard form M (blockok 0), is the head row-1
    # >= every tail-zone subscript of translate(M)?  (OT2 at value level)
    # head row-1 = snd of first pair.  tail_subs of translate(M).
    inv_viol=0; inv_ex=[]
    for M in NF:
        if not M: continue
        if not blockok(0,list(M)): continue
        t=translate(M)
        a,b,c=t
        # the leading principal subscript is a (=snd first pair); tail-zone subs of c:
        ts=tail_subs(c)
        if any(s>a for s in ts):
            inv_viol+=1
            if len(inv_ex)<8: inv_ex.append((M,a,ts))
    print(f"\n[OT2-value] head-subscript >= all tail-zone subscripts: VIOL={inv_viol}")
    for M,a,ts in inv_ex:
        print(f"   M={''.join('(%d,%d)'%p for p in M)} head_sub={a} tailsubs={ts}")

    # Now the hereditary version: at EVERY subterm node P a b c of translate(M),
    # is a >= every tail-zone subscript of c?  (this is exactly hdle c (P a b Z)'s
    # subscript part = OT2 of wf3)
    def ot2_all(t):
        if t==Z: return True
        a,b,c=t
        if any(s>a for s in tail_subs(c)): return False
        return ot2_all(b) and ot2_all(c)
    h_viol=0; h_ex=[]
    for M in NF:
        t=translate(M)
        if not ot2_all(t):
            h_viol+=1
            if len(h_ex)<8: h_ex.append((M,t))
    print(f"\n[OT2-hereditary] every node: head-sub >= tail-zone subs: VIOL={h_viol}/{len(NF)}")
    for M,t in h_ex:
        print(f"   M={''.join('(%d,%d)'%p for p in M)} t={fmt(t)}")

    # VALUE block lemma direct test on pairs (cap)
    import random
    rng=random.Random(0)
    pool=NF if len(NF)<=1500 else rng.sample(NF,1500)
    key={M: nrm(conv(translate(M))) for M in pool}
    tested=0; viol=0; vex=[]
    for M,N in itertools.permutations(pool,2):
        if not (blockok(0,list(M)) and blockok(0,list(N))): continue
        if not seqlex(list(M),list(N)): continue
        tested+=1
        kM,kN=key[M],key[N]
        if kM==kN or lt_term(kN,kM):
            viol+=1
            if len(vex)<6: vex.append((M,N,kM,kN))
    print(f"\n[VALUE block lemma] blockok0 + seqlex ==> oV M < oV N : tested={tested} VIOL={viol}")
    for M,N,kM,kN in vex:
        print(f"   M={''.join('(%d,%d)'%p for p in M)}  N={''.join('(%d,%d)'%p for p in N)}")
        print(f"      oV: {fmtb(kM)} vs {fmtb(kN)}")

if __name__=="__main__":
    main()
