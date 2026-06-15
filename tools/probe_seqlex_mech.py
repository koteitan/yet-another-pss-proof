#!/usr/bin/env python3
"""Mechanism: HOW does seqlex first-diff drive olt(proj0 b)(proj0 f)?

proj0 b = chainAt b k (k=maxsub). The .b-chain of b realises leads [1..k]
(consecutive, inv2 spine). proj0 b = P k bx cx (the node at lead k).
Similarly proj0 f = P k fx fy.

olt(proj0 b)(proj0 f) at equal lead k = (olt bx fx) or (bx=fx & olt cx cy).
This is the comparison of the TAILS-at-the-spine-top.

Question: does the seqlex preimage structure tell us bx,cx vs fx,cy?
Let me instead test a DIRECTLY PROVABLE reformulation that avoids preimages:

CLAIM (term-level, no preimage): for firing NF args b,f, olt b f, eq maxsub:
  the comparison olt(proj0 b)(proj0 f) is DETERMINED by olt b f via descending
  BOTH .b-chains in lockstep to the lead-k node, and at each chain step the
  off-spine tails compare consistently with olt.

Test the LOCKSTEP chain comparison:
  define chainnodes(t) = [t, t.b, t.b.b, ..., proj0 t]  (leads 1,2,..,k for firing)
  Compare b and f node-by-node down the chain. At the FIRST chain index where the
  full subterms differ, does olt resolve, and does it propagate to proj0?

Actually the cleanest test for a LEAN proof: is there a node-wise invariant
  INV(i): olt (b-chain node i) (f-chain node i)  for all i from 0 to depth?
If olt b f and eq maxsub => olt holds at EVERY chain node (i=0 is olt b f,
i=depth is olt(proj0 b)(proj0 f))?  Test this monotone-down-the-chain claim.
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import translate, enum_ST, olt, maxsub
Z = ()
def lead(t): return 0 if t==Z else t[0]
def Gterm(u, t):
    if t == Z: return []
    a, b, c = t; out = []
    if u <= a: out.append(b); out += Gterm(u, b)
    out += Gterm(u, c); return out
def pfire(u, b): return any(not olt(g, b) for g in Gterm(u, b))
def proj(u, b):
    while True:
        bad = [g for g in Gterm(u, b) if not olt(g, b)]
        if not bad: return b
        m = bad[0]
        for h in bad[1:]:
            if olt(m, h): m = h
        b = m
def chainnodes(t):
    out=[]; cur=t
    while cur!=Z:
        out.append(cur); cur=cur[1]
    return out

def main():
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=14, rounds=8)
    NF = sorted({translate(list(M)) for M in ST}, key=str)
    args = sorted({t[1] for t in NF if t != Z and t[0] == 0}, key=str)
    fire = [b for b in args if pfire(0, b)]

    # chain nodes to proj0 (leads 1..k). depth = k. node i has lead i+1.
    # INV(i): olt (b-node-at-lead L)(f-node-at-lead L) for L=1..k.
    # i=0: lead-1 node = b,f themselves (firing args lead 1). olt b f given.
    # i=k-1: lead-k node = proj0 b, proj0 f. want olt.
    def nodeAtLead(t, L):
        cur=t
        while cur!=Z:
            if lead(cur)==L: return cur
            cur=cur[1]
        return None
    allhold=0; tot=0; firstfail=[]
    for b in fire:
        k=maxsub(b)
        for f in fire:
            if not olt(b,f) or maxsub(f)!=k: continue
            tot+=1
            ok=True
            for L in range(1,k+1):
                nb=nodeAtLead(b,L); nf=nodeAtLead(f,L)
                if nb is None or nf is None: ok=False; break
                if not olt(nb,nf): ok=False;
                if not olt(nb,nf):
                    if len(firstfail)<8: firstfail.append((L,k,nb,nf,b,f))
                    break
            if ok: allhold+=1
    print(f"eqmaxsub pairs {tot}: olt holds at EVERY spine node lead 1..k: {allhold}")
    for ff in firstfail[:8]: print("  FAIL at lead",ff[0],"of",ff[1])

    # If allhold < tot, the lockstep is NOT monotone; test instead: olt at lead k
    # (the proj nodes) directly, and whether it's the LAST node that matters.
    topok=0; toptot=0
    for b in fire:
        k=maxsub(b)
        for f in fire:
            if not olt(b,f) or maxsub(f)!=k: continue
            toptot+=1
            nb=nodeAtLead(b,k); nf=nodeAtLead(f,k)
            if olt(nb,nf): topok+=1
    print(f"olt at lead-k node (=proj0): {topok}/{toptot}")

if __name__ == '__main__':
    main()
