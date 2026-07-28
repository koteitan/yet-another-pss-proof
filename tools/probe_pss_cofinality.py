#!/usr/bin/env python3
"""PSS BACHMANN COFINALITY probe — the load-bearing statement of the W_u transplant.

The syntactic well-foundedness proof of Buchholz 1987 §2 runs on
    Bachmann cofinality  +  W_u least-fixpoint induction.
Transplanted to PSS (no Buchholz translation, no ordinals), the cofinality
statement is, for standard forms M, N and PSS's own fundamental sequence
`oper` (= M[n]):

    translate N  <o  translate M     ==>    exists n,  translate N  <=o  translate (M[n]).

("every strictly smaller standard form is bounded by some expansion of M")

This is a DIFFERENT statement from our open residual `H0clause` (coefficient
domination): it never mentions Gterm.  If it is TRUE and provable from ST_PS
structure directly, the W_u induction delivers WF(olt on standard forms) and the
H0clause wall is bypassed entirely.

This probe measures its TRUTH on the ST_PS fragment (row1<=1) at closure depth.
"""
import sys
sys.path.insert(0, '.')
from fast_pss import oper, Lng
from wfe_explore import translate, olt
from probe_bmocf_ancestor import enum_depth


def ole(s, t):
    return s == t or olt(s, t)


def run(rounds, maxlen, N, cap_hosts=None, cap_pairs=200000):
    hosts = [tuple(M) for M in enum_depth(2, (1, 2, 3), maxlen, rounds)
             if len(M) >= 2 and all(p[1] <= 1 for p in M) and M[0] == (0, 0)]
    hosts = sorted(set(hosts))
    if cap_hosts:
        hosts = hosts[:cap_hosts]
    tr = {M: translate(list(M)) for M in hosts}
    # expansions of each host
    exp = {}
    for M in hosts:
        seq = []
        for n in range(0, N + 1):
            try:
                Mn = oper(list(M), n)
            except Exception:
                continue
            seq.append(translate(list(Mn)))
        exp[M] = seq

    nPair = 0
    nViol = 0
    exs = []
    for M in hosts:
        tM = tr[M]
        for Nn in hosts:
            tN = tr[Nn]
            if not olt(tN, tM):
                continue
            nPair += 1
            if nPair > cap_pairs:
                break
            if not any(ole(tN, tMn) for tMn in exp[M]):
                nViol += 1
                if len(exs) < 6:
                    exs.append((M, Nn))
        if nPair > cap_pairs:
            break
    print(f"[+{rounds} len<={maxlen} n<={N}] hosts={len(hosts)} pairs(N<M)={nPair} "
          f"***COFINALITY VIOLATIONS={nViol}***")
    for e in exs:
        print("   viol (M, N):", e[0], "|", e[1])
    return nViol


if __name__ == '__main__':
    for rounds, maxlen, N in [(5, 9, 8), (6, 10, 10), (7, 11, 12)]:
        run(rounds, maxlen, N)
