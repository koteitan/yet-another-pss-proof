#!/usr/bin/env python3
"""Inductive structure of STRICTWIT.  b=P1 b' c', f=P1 f' d', olt b f => olt b' f'
(verified).  proj0 b = greatest critical = max_olt({b'} ∪ Gterm0 b' ∪ Gterm0 c').

The needed witness h in Gterm0 f with olt(proj0 b) h.  Gterm0 f =
{f'} ∪ Gterm0 f' ∪ Gterm0 d'.  Candidate witness: f' (head arg of f)?  W4 was
710967/824970 -- not always.  But maybe a SMARTER witness derived inductively.

Test the SHARP inductive lemma SE (strict embed of the greatest critical):
  SE: olt b f (firing NF args, both P1) =>
      olt (proj0 b) f'   OR   (proj0 b in Gterm0 f' and ... )
  Better, the FULL strict embedding that recurses:
  SE_full: for firing NF args b<o f, the greatest critical g*(b)=proj0 b
     satisfies olt g*(b) g*(f) directly (that IS the goal).

So instead test the LIFT: proj0 b vs f'.  We need olt(proj0 b)(proj0 f).
proj0 f = greatest critical of P1 f' d' = max({f'}∪Gterm0 f'∪Gterm0 d').
Since olt b' f' and proj0 b = g*(P1 b' c'):
  Hypoth HMONO: g*(P1 b' c') <o g* / structure of (P1 f' d').

Cleanest testable: is olt (proj0 b) (proj0 f)  EQUIVALENT to olt b f restricted,
and does proj0 b only depend on b' (not c')?  Test: proj0(P1 b' c') depends on c'?
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import translate, enum_ST, olt, maxsub, spine
Z = ()
def le(s, t): return s == t or olt(s, t)
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

    # Does proj0(P1 b' c') depend only on b' (ignore tail c')?
    # group firing args by b' and see if proj0 differs across c'
    from collections import defaultdict
    bymap=defaultdict(set)
    for b in fire:
        if b[0]!=1: continue
        _,bp,cp=b
        bymap[bp].add(proj(0,b))
    dep=sum(1 for k,v in bymap.items() if len(v)>1)
    print(f"distinct b' heads {len(bymap)}; b' with proj0 depending on tail c': {dep}")

    # The witness route that's cleanest in Lean:
    # h = proj0 (head arg b')??  no.  Let's test: for the GREATEST critical
    # g = proj0 b of b, is g a critical of b that lies on b's 'b-spine'
    # (the leading argument chain)?  i.e. is proj0 b reachable by repeatedly
    # taking .b ?  If so proj0 b is determined by the leading spine of b, and
    # olt b' f' lifts cleanly.
    # spine-arg chain criticals: g0=b, g_{i+1}=(g_i).b ; collect those with lead>=0
    def bspine_crit(t):
        out=[]
        cur=t
        while cur!=Z:
            a,bb,cc=cur
            out.append(cur)  # principal at this spine node
            cur=bb
        return out
    on_bspine=0; tot=0
    for b in fire:
        tot+=1
        pb=proj(0,b)
        # is pb a sub-principal on the leading .b chain of b?
        chain=[]
        cur=b
        while cur!=Z:
            chain.append(cur); cur=cur[1]
        if pb in chain: on_bspine+=1
    print(f"firing {tot}: proj0 b on leading .b-chain of b: {on_bspine}")

if __name__ == '__main__':
    main()
