#!/usr/bin/env python3
"""A_u-CLOSURE probe for the domination clause (the W_u least-fixpoint route).

CONTEXT (2026-07-24). pss-proof produced a SYNTACTIC (ordinal-free) WF proof of
Buchholz OT_B (`OTB-well-founded-syntactic`), whose engine is
    Bachmann cofinality  +  the iterated inductive set W_u (least fixpoint of A_u),
    A_u(X) ∋ c  iff  c=0  ∨  (dom c ∈ {{0},ℕ} ∧ ∀n, c[n] ∈ X)
                          ∨  (∃m<u, dom c = T_m ∧ ∀z∈W_m, c[z] ∈ X)
and whose least-fixpoint induction is  A_u(Y) ⊆ Y  ⟹  W_u ⊆ Y.

In Buchholz's system the coefficient-DOMINATION clause is FREE (it is the
*definition* of isOT_BT).  Transplanted to PSS it is NOT free: it is exactly our
open residual `H0clause` (Face 1).  BUT: every induction axis this campaign
exhausted (term-local / column-local / forest-LEVEL / row-1 / oper-derivation /
per-level / forest-ancestor) is a STRUCTURAL induction.  The W_u least-fixpoint
induction is NOT structural — it descends along the FUNDAMENTAL SEQUENCE
(`oper`, PSS's M[n]) and never visits the intermediate nodes where every
structural carrier died.

THE DECIDING QUESTION (this probe): is the domination clause `A_u`-CLOSED?
    (∀n, H0clause(translate(M[n])))  ⟹  H0clause(translate M)   ?
If YES, the W_u least-fixpoint induction PROVES the clause and the wall dissolves.
If NO, we need a stronger carried invariant (the counterexamples say which).

NOTE the direction: round-8 measured the FORWARD transport H0(M) → H0(M[n])
(0-viol) — the wrong direction for A_u.  This is the BACKWARD/upward one, untested.

On ST_PS hosts H0clause is TRUE everywhere, so the test is vacuous there; the
probe therefore runs on the ambient `steps1` class (row-0 rises by ≤1, row-1 ≤ 1),
where the clause genuinely fails on 25887 instances (memory h0clause round 4) —
that is where A_u-closure can actually be violated.
"""
import sys
sys.path.insert(0, '.')
from fast_pss import oper, Lng
from wfe_explore import translate
from probe_bmocf_core import H0clause


def gen_steps1(maxlen, maxr0, r1vals=(0, 1)):
    """all sequences starting (0,0): row-0 rises by at most +1 and stays >=0,
    row-1 in r1vals.  This is the ambient class of the residual."""
    out = []
    def rec(seq):
        if len(seq) >= 2:
            out.append(tuple(seq))
        if len(seq) >= maxlen:
            return
        prev0 = seq[-1][0]
        for r0 in range(0, min(prev0 + 1, maxr0) + 1):
            for r1 in r1vals:
                seq.append((r0, r1))
                rec(seq)
                seq.pop()
    rec([(0, 0)])
    return out


def D(M):
    """the domination clause on translate M (exact lean H0clause)."""
    ok, _ = H0clause(translate(list(M)))
    return ok


def run(maxlen, maxr0, N):
    hosts = gen_steps1(maxlen, maxr0)
    nTot = 0            # hosts examined
    nFalse = 0          # hosts where the clause itself fails
    nAllChildOk = 0     # hosts where every M[n] (n<=N) satisfies the clause
    nViol = 0           # A_u-closure VIOLATIONS: all children ok but parent not
    exs = []
    for M in hosts:
        nTot += 1
        dM = D(M)
        if not dM:
            nFalse += 1
        childOk = True
        for n in range(0, N + 1):
            try:
                Mn = oper(list(M), n)
            except Exception:
                continue
            if not Mn:
                continue
            if not D(Mn):
                childOk = False
                break
        if childOk:
            nAllChildOk += 1
            if not dM:
                nViol += 1
                if len(exs) < 8:
                    exs.append(M)
    print(f"[len<={maxlen} r0<={maxr0} n<={N}] hosts={nTot} clause-FALSE={nFalse} "
          f"all-children-ok={nAllChildOk}  ***A_u-CLOSURE VIOLATIONS={nViol}***")
    for e in exs:
        print("   viol host:", e)
    return nViol


if __name__ == '__main__':
    for maxlen, maxr0, N in [(5, 3, 4), (6, 3, 5), (7, 4, 5)]:
        run(maxlen, maxr0, N)
