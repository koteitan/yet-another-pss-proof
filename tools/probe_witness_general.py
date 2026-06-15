#!/usr/bin/env python3
"""Find the GENERALIZED inductive lemma for the witness, provable by induction
on f's structure (not requiring b NF, only proj0 b's properties).

proj0 b = greatest critical of b, with lead(proj0 b) = maxsub b = k <= maxsub f.
We need h in Gterm0 f with olt(proj0 b) h.

Candidate GEN lemma (induction on f, f a firing NF arg = P1 f' d'):
  Let p = proj0 b (any term with lead p = k <= maxsub f, and p <o proj0 f known? no).
  Hmm need the right hypothesis on p that's preserved.

Test the CLEANEST general fact:
  GEN: for firing NF args b<o f:  olt (proj0 b) (proj0 f).   [the goal itself]
  Reformulate via greatest-critical map G*(t)=proj0 t.
  Is G* MONOTONE under olt on firing NF args, provable by:
    G*(P1 b' c') vs G*(P1 f' d'), olt b' f', by IH G*(b') <o G*(f')  [if b',f'
    were firing NF args -- but they're head args, lead>=1].

Test: are the head args b', f' THEMSELVES firing-NF-like so IH applies?
  - is P 0 b' Z (re-host at 0) in NF?  or is b' in the NF-arg class?
  - does olt b' f' + both 'fire' (pfire 0 b'? ) hold so the SAME lemma recurses?
Test pfire 0 b' for head args of firing b; and whether olt b' f' pairs both fire.

Also test the DIRECT monotone on greatest-critical restricted to the leading
chain: define lchain(t) = [t, t.b, t.b.b, ...]; proj0 t is the deepest lchain
node with lead = maxsub.  olt b f => the lchains 'align' so proj0 b <o proj0 f.
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import translate, enum_ST, olt, maxsub, spine
Z = ()
def le(s, t): return s == t or olt(s, t)
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

def main():
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=14, rounds=8)
    NF = sorted({translate(M) for M in ST}, key=str)
    args = sorted({t[1] for t in NF if t != Z and t[0] == 0}, key=str)
    fire = [b for b in args if pfire(0, b)]

    # Q1: are head args b' firing at level 0? (pfire 0 b')
    hp_fire=hp_nofire=0
    for b in fire:
        bp=b[1]
        if pfire(0,bp): hp_fire+=1
        else: hp_nofire+=1
    print(f"head args b' of firing b: pfire0 {hp_fire}, nofire {hp_nofire}")

    # Q2: head-arg pairs (b',f') from firing pairs olt b f: do they both fire?
    #     and is the SAME witness lemma applicable recursively at level... but
    #     b',f' are NOT head-0.  We need a DIFFERENT recursion.
    # Q3: KEY -- proj at level >0.  Since b'=P (a>=1) ..., the criticals of b'
    #     at level 0 are Gterm0 b'.  proj0 b' = greatest 0-critical of b'.
    #     M1 = proj0 b' if pfire0 b' else b'.
    #     The recursion: proj0(P1 b' c') dominated by crit of f=P1 f' d':
    #        need olt M1(b') (crit of f) and olt M2(c') (crit of f).
    # Test the LEADING-CHAIN alignment claim:
    #   lchain descent: proj0 b reached by repeatedly going to .b until lead<maxsub?
    #   Let's verify proj0 b == the FIRST lchain node g with: g is a violator
    #   (not olt g b) and maximal.  Already know on lchain.  Test depth.
    def lchain(t):
        out=[]; cur=t
        while cur!=Z:
            out.append(cur); cur=cur[1]
        return out
    depth_ok=0; tot=0
    for b in fire:
        tot+=1
        pb=proj(0,b)
        ch=lchain(b)
        # pb is one of ch
        # is pb the deepest node with lead == maxsub b?
        cands=[g for g in ch if lead(g)==maxsub(b)]
        if cands and pb==cands[-1]: depth_ok+=1  # deepest such
    print(f"proj0 b == deepest leading-chain node with lead==maxsub: {depth_ok}/{tot}")

    # Q4: the recursion on the WITNESS as descent of f's leading chain.
    #   witness h: descend f's lchain to the node with lead >= ... that dominates pb.
    #   Test: exists node fn in lchain(f) (which are all in Gterm0 f? NO - lchain
    #   nodes are the term itself & head args, head args ARE in Gterm0).
    #   Actually f' = f.b in Gterm0 f; f.b.b in Gterm0 f' subset Gterm0 f. etc.
    #   So lchain(f)[1:] (excluding f itself) subset Gterm0 f.
    #   witness = some lchain(f)[1:] node dominating pb?
    wit_lchain=0; tot2=0
    for b in fire:
        pb=proj(0,b)
        for f in fire:
            if not olt(b,f): continue
            tot2+=1
            ch=lchain(f)[1:]  # head-arg chain, subset Gterm0 f
            if any(olt(pb,n) for n in ch): wit_lchain+=1
    print(f"witness in f's leading-chain (head args): {wit_lchain}/{tot2}")

if __name__ == '__main__':
    main()
