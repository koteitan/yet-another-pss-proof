#!/usr/bin/env python3
"""DECISIVE: is the olt x b proof on the HARD class CONTROLLED by the BMOCF
<_M^Next ancestor chain -- i.e. would a structural induction on <_M^Next chains
actually close, or does the difficulty relocate?

A proof by structural induction on <_M^Next chains is TRACTABLE iff:
  the equal-lead arg-descent of olt x b mirrors a <_M^Next descent in the host
  matrix, so the IH (smaller chain) supplies olt x b at each level WITHOUT
  re-deriving the global head-0 fact.

We test the CONVERSE failure mode the lean project found (bypass #8-11): the
firing/non-firing and the olt are FOREST-POSITION dependent, i.e. two terms with
IDENTICAL local term-structure (same x, same b) can come from different host
positions with different ST_PS-membership.  If olt x b is *determined by the
pair (x,b) alone* (term-local), then NO global ancestor structure is needed and
the reframe is unnecessary; if it is NOT determined by (x,b) alone, then the
ancestor structure is load-bearing -- and we test if a SINGLE <=_M fact suffices
or the induction stays open.

Test T1 (term-locality of olt on the hard class): is olt x b a function of the
PAIR (x,b) only?  (It must be -- olt is a pure term function.)  -> trivially yes.
The REAL question (T2): is the *truth* of "x in Gterm 0 b => olt x b" derivable
from a term-local property of b alone, or does it require knowing b = translate
of an ST_PS block (the forest/ancestor info)?

T2: enumerate ALL b that appear as head-0 arguments in the corpus.  For each,
does H0clause-at-b (forall x in Gterm0 b, olt x b) hold?  Then find b that are
term-structurally legal (cnf, subs<=1) but are NOT translate-of-ST_PS and CHECK
whether the clause can FAIL there.  If it fails off-ST_PS, the ST_PS/ancestor
info is essential (=> ancestor reframe is on the right track but load-bearing);
if it holds for ALL cnf/subs<=1 b, the core would be term-local (contradicting
bypass #11).
"""
import sys, itertools
sys.path.insert(0, '.')
from fast_pss import diagSeq, Lng
from wfe_explore import translate, olt, maxsub
from wfe_explore import fmt as tfmt
from probe_bmocf_ancestor import enum_depth
from probe_bmocf_core import Gterm, lead

def cnf(t):
    """non-increasing spine of tops (hdle): each principal head >= next."""
    # tops chain via c
    while t != ():
        a, b, c = t
        if c != ():
            e, f, g = c
            # hdle (P a b _) (P e f _) must hold reversed: a >= e (head non-incr)
            if a < e: return False
            if a == e and olt(b, f): return False
        if not cnf(b): return False
        t = c
    return True

def subs_le1(t):
    if t == (): return True
    a, b, c = t
    return a <= 1 and subs_le1(b) and subs_le1(c)

def clause_holds(b):
    for x in Gterm(0, b):
        if not olt(x, b): return False
    return True

def all_subterms(t):
    if t == (): return
    yield t
    a, b, c = t
    yield from all_subterms(b); yield from all_subterms(c)

def main():
    for rounds in (5, 6):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        frag = [M for M in seen if Lng(M) <= 18 and all(c[1] <= 1 for c in M)]
        md = max(seen.values())

        # collect all head-0 arguments b (subs<=1) appearing in translate-images
        legal_b = set()    # b that are translate-derived (in corpus)
        for M in frag:
            t = translate(M)
            for st in all_subterms(t):
                a, bb, cc = st
                if a == 0:
                    legal_b.add(bb)
        legal_b.discard(())

        # T2a: do all translate-derived b satisfy the clause? (should: core true)
        bad_legal = [b for b in legal_b if not clause_holds(b)]

        # T2b: enumerate cnf/subs<=1 terms NOT necessarily translate-derived and
        # find clause failures -> shows the clause is NOT term-local (needs ST_PS).
        # Build a small universe of cnf subs<=1 terms by closing legal_b's
        # subterms under re-assembly P 0 b Z and P 1 b Z and sums.
        universe = set()
        atoms = set()
        for b in legal_b:
            for st in all_subterms(b):
                atoms.add(st)
        atoms.add(())
        atoms = list(atoms)[:60]
        for b in atoms:
            for a in (0, 1):
                cand = (a, b, ())
                if cnf(cand) and subs_le1(cand):
                    universe.add(cand)
        # also P 0 b (P 0 b' Z) small sums
        for b in atoms[:30]:
            for b2 in atoms[:30]:
                cand = (0, b, (0, b2, ()))
                if cnf(cand) and subs_le1(cand):
                    universe.add(cand)
        offST_fail = [u for u in universe
                      if u not in legal_b and not clause_holds(u)]
        # confirm these are cnf/subs<=1 (term-structurally legal) yet clause-FALSE
        print(f'[closure+{rounds}] maxdepth={md} frag={len(frag)} legal_b={len(legal_b)}')
        print(f'  T2a translate-derived b violating clause: {len(bad_legal)} '
              f'(expect 0 -> core true)')
        print(f'  T2b cnf/subs<=1 terms NOT translate-derived w/ clause FALSE: '
              f'{len(offST_fail)} / universe {len(universe)}')
        for u in offST_fail[:6]:
            bad = [x for x in Gterm(0, u[1]) if not olt(x, u[1])]
            print('     offST-FAIL b=', tfmt(u[1])[:46],
                  ' violating x=', tfmt(bad[0])[:30] if bad else '?')
        if offST_fail:
            print('  => clause is NOT term-local: forest/ST_PS(ancestor) info is '
                  'LOAD-BEARING.')
        else:
            print('  => no off-ST failure found in this universe (inconclusive '
                  'for term-locality here).')

if __name__ == '__main__':
    main()
