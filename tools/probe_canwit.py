#!/usr/bin/env python3
"""
Probe the canonical_witness_in_Cset_c residue empirically.

For every (alpha, v, xi, w) with
  xi in Cset_c(alpha,v), xi < alpha, NOT acanon(w,xi), v <= w,
we search for a CANONICAL delta in  alpha INTER Cset_c(alpha,v)  with
  psi(delta,w) = psi(xi,w).

Goal: identify the STRUCTURE of the witness delta:
  - is delta == the value c = psi(xi,w) itself ?
  - is delta == wit(xi,w) (least witness) ?
  - is delta canonical-and-in-closure but neither?
and report whether such a delta ALWAYS exists (the residue is then TRUE),
plus the smallest such delta and its relation to xi and c.
"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/ya-pss/git/.claude/worktrees/agent-aa427cfe3b19bad3a/tools')
from cset_remark_check import (Cset, psi, acanon, lt, le, eq, to_str, cmp_key,
                               Om, warm_psi, nat, OMEGA, ONE, TWO, W2, WW, ZERO,
                               oadd, SMALL)

def Cset_c(arg, v):
    return Cset(arg, v, canonical=True)

def least_wit(xival, w):
    """least delta in SMALL with psi(delta,w)=psi(xival,w)."""
    target = psi(xival, w)
    cands = sorted([d for d in SMALL], key=cmp_key())
    for d in cands:
        p = psi(d, w)
        if p is not None and eq(p, target):
            return d
    return None

def main():
    first = [nat(n) for n in range(0, 10)]
    extras = [OMEGA, oadd(OMEGA, ONE), oadd(OMEGA, nat(2)), ((ONE, 2),),
              oadd(((ONE, 2),), ONE), W2, oadd(W2, OMEGA), WW]
    args = []
    seen = set()
    for a in first + extras:
        if a not in seen:
            seen.add(a); args.append(a)
    args.sort(key=cmp_key())
    warm_psi(args)

    total_residue = 0
    have_witness = 0
    no_witness = []
    # structure tallies
    delta_is_value = 0     # delta == c = psi(xi,w)
    delta_is_leastwit = 0
    delta_eq_xi = 0
    examples = []

    for v in (0, 1, 2):
        for alpha in args:
            Sc = Cset_c(alpha, v)
            for xi in sorted(Sc, key=cmp_key()):
                if not lt(xi, alpha):
                    continue
                for w in (0, 1, 2):
                    if w < v:
                        continue
                    if acanon(w, xi):
                        continue
                    c = psi(xi, w)
                    if c is None or not lt(c, NABLA_GUARD):
                        continue
                    # residue case hit.
                    total_residue += 1
                    # search canonical delta in alpha INTER Sc with psi(delta,w)=c
                    found_delta = None
                    for delta in sorted(Sc, key=cmp_key()):
                        if not lt(delta, alpha):
                            continue
                        if not acanon(w, delta):
                            continue
                        pd = psi(delta, w)
                        if pd is not None and eq(pd, c):
                            found_delta = delta
                            break
                    if found_delta is not None:
                        have_witness += 1
                        if eq(found_delta, c):
                            delta_is_value += 1
                        lw = least_wit(xi, w)
                        if lw is not None and eq(found_delta, lw):
                            delta_is_leastwit += 1
                        if eq(found_delta, xi):
                            delta_eq_xi += 1
                        if len(examples) < 25:
                            examples.append((to_str(alpha), v, to_str(xi), w,
                                             to_str(c), to_str(found_delta),
                                             eq(found_delta, c),
                                             le(found_delta, xi),
                                             acanon(w, c) if c is not None else None))
                    else:
                        no_witness.append((to_str(alpha), v, to_str(xi), w, to_str(c)))

    print("=== canonical_witness_in_Cset_c residue probe ===")
    print(f"residue cases (xi<alpha in Cset_c, !acanon(w,xi), v<=w): {total_residue}")
    print(f"  have canonical witness delta in alpha INTER Cset_c: {have_witness}")
    print(f"  NO witness (residue would be FALSE): {len(no_witness)}")
    if no_witness:
        print("  COUNTEREXAMPLES:")
        for ce in no_witness[:30]:
            print(f"    alpha={ce[0]}, v={ce[1]}, xi={ce[2]}, w={ce[3]}, c=psi(xi,w)={ce[4]}")
    print()
    print("=== structure of the smallest witness delta ===")
    print(f"  delta == c (the value itself):     {delta_is_value} / {have_witness}")
    print(f"  delta == least witness:            {delta_is_leastwit} / {have_witness}")
    print(f"  delta == xi:                       {delta_eq_xi} / {have_witness}")
    print()
    print("=== examples (alpha,v,xi,w,c,delta, delta==c, delta<=xi, acanon(w,c)) ===")
    for ex in examples:
        print("   ", ex)

NABLA_GUARD = ((W2, 1),)  # = NABLA

if __name__ == "__main__":
    main()
