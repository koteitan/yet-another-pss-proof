#!/usr/bin/env python3
"""CopyCrux verification — the single residual of PSS Bachmann cofinality.

`YAPSS/Cofinality.lean` reduces `pss_cofinality` to `CopyCrux` (all other branches
GREEN).  The reduction direction is `CopyCrux ⟹ cofinality`, so CopyCrux may be
STRICTLY STRONGER than cofinality and could be FALSE even though cofinality is
0-viol.  This probe checks CopyCrux itself.

    CopyCrux :
      ST_PS ((G ++ (v0,w0)::R) ++ [lp])  →  ST_PS ((G ++ (v0,w0)::R) ++ q::S) →
      (∀x∈R, v0 < x.1) → v0 < lp.1 →
      ((d0=0 ∧ lp.2=0) ∨ (0<d0 ∧ w0<lp.2 ∧ lp.1=v0+d0)) → pairlt q lp →
      ∃ m ≥ 1,  sle (q::S)  (shiftr0 d0 (copies d0 ((v0,w0)::R) m))

with `shiftr0 d = map (p ↦ (p.1+d, p.2))`, `copies d blk n = concat_{k<n} shiftr0 (k*d) blk`,
`pairlt p q = p.1<q.1 ∨ (p.1=q.1 ∧ p.2<q.2)`, `seqlex` the column-lex order,
`sle A B = (A=B ∨ seqlex A B)`.
"""
import sys
sys.path.insert(0, '.')
from probe_bmocf_ancestor import enum_depth
from probe_arch_global_inv import oper_decomp


def pairlt(p, q):
    return p[0] < q[0] or (p[0] == q[0] and p[1] < q[1])


def seqlex(A, B):
    if not A:
        return len(B) > 0
    if not B:
        return False
    if pairlt(A[0], B[0]):
        return True
    if A[0] == B[0]:
        return seqlex(A[1:], B[1:])
    return False


def sle(A, B):
    return list(A) == list(B) or seqlex(list(A), list(B))


def shiftr0(d, M):
    return [(p[0] + d, p[1]) for p in M]


def copies(d, blk, n):
    out = []
    for k in range(n):
        out += shiftr0(k * d, blk)
    return out


def run(rounds, maxlen, MMAX):
    hosts = [tuple(M) for M in enum_depth(2, (1, 2, 3), maxlen, rounds)
             if len(M) >= 2 and all(p[1] <= 1 for p in M) and M[0] == (0, 0)]
    hosts = sorted(set(hosts))
    hostset = set(hosts)
    nInst = 0
    nViol = 0
    exs = []
    for M in hosts:
        dec = oper_decomp(list(M))
        if dec is None:
            continue
        G, blk, d0, lp = dec
        if not blk:
            continue
        v0, w0 = blk[0]
        R = blk[1:]
        # hypotheses of CopyCrux on the host side
        if not all(v0 < x[0] for x in R):
            continue
        if not (v0 < lp[0]):
            continue
        disj = (d0 == 0 and lp[1] == 0) or (0 < d0 and w0 < lp[1] and lp[0] == v0 + d0)
        if not disj:
            continue
        pref = list(G) + list(blk)
        # every ST_PS N sharing the prefix and continuing below lp
        for N in hosts:
            Nl = list(N)
            if len(Nl) <= len(pref) or Nl[:len(pref)] != pref:
                continue
            q = Nl[len(pref)]
            S = Nl[len(pref) + 1:]
            if not pairlt(q, lp):
                continue
            nInst += 1
            ok = any(sle([q] + S, shiftr0(d0, copies(d0, blk, m)))
                     for m in range(1, MMAX + 1))
            if not ok:
                nViol += 1
                if len(exs) < 6:
                    exs.append((M, N, tuple(blk), d0, lp, q))
    print(f"[+{rounds} len<={maxlen} m<={MMAX}] instances={nInst}  ***CopyCrux VIOLATIONS={nViol}***")
    for e in exs:
        print("   viol: M=", e[0], " N=", e[1], " blk=", e[2], " d0=", e[3], " lp=", e[4], " q=", e[5])
    return nViol


if __name__ == '__main__':
    for rounds, maxlen, MMAX in [(5, 9, 10), (6, 10, 12), (7, 11, 14)]:
        run(rounds, maxlen, MMAX)
