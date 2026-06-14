#!/usr/bin/env python3
"""
Empirical check of Buchholz's "Remark": the closure operators Cset and Cset_c
(canonical variant) produce the SAME set, in a finite CNF model of Buchholz's
psi / C collapsing functions.

No external libraries. Self-contained.

ORDINAL MODEL
=============
Ordinals are Cantor normal forms (CNF) in base omega, represented as tuples of
(exponent, coefficient) pairs:

    a = w^e0 * c0 + w^e1 * c1 + ... + w^ek * ck

with e0 > e1 > ... > ek (exponents strictly DESCENDING) and each ci >= 1.
The empty tuple () is the ordinal 0. Exponents are THEMSELVES CNFs (recursive).

We represent a CNF as a Python tuple of pairs:  ((e0, c0), (e1, c1), ...).
Each ei is again such a tuple. () == 0.
"""

import sys
from functools import lru_cache

# ----------------------------------------------------------------------------
# Basic ordinal constants
# ----------------------------------------------------------------------------
ZERO  = ()                       # 0
ONE   = ((ZERO, 1),)             # w^0 * 1 = 1
TWO   = ((ZERO, 2),)             # 2
OMEGA = ((ONE, 1),)              # w^1 = omega
# omega^2 = w^2:
W2    = ((TWO, 1),)              # w^(2)  (exponent is the ordinal 2)
# omega^omega:
WW    = ((OMEGA, 1),)            # w^omega


def nat(n):
    """natural number n>=0 as a CNF."""
    if n == 0:
        return ZERO
    return ((ZERO, n),)


# ----------------------------------------------------------------------------
# Comparison
# ----------------------------------------------------------------------------
_cmp_memo = {}

def cmp(a, b):
    """Lexicographic comparison of CNF ordinals. Returns -1,0,1. Memoized."""
    if a is b:
        return 0
    key = (a, b)
    r = _cmp_memo.get(key)
    if r is not None:
        return r
    # Compare term by term: leading (exp,coeff).
    res = 0
    i = 0
    la, lb = len(a), len(b)
    while i < la and i < lb:
        ea, ca = a[i]
        eb, cb = b[i]
        c = cmp(ea, eb)
        if c != 0:
            res = c
            break
        if ca != cb:
            res = -1 if ca < cb else 1
            break
        i += 1
    else:
        # One is a prefix of the other: longer (with equal prefix) is larger.
        res = 0 if la == lb else (-1 if la < lb else 1)
    _cmp_memo[key] = res
    return res


def lt(a, b):
    return cmp(a, b) < 0


def le(a, b):
    return cmp(a, b) <= 0


def eq(a, b):
    return cmp(a, b) == 0


# ----------------------------------------------------------------------------
# Ordinal addition
# ----------------------------------------------------------------------------
_oadd_memo = {}

def oadd(a, b):
    """
    Ordinal addition a + b, in CNF.
    Rule: drop every term of a whose exponent is < the leading exponent of b.
    If a has a term with exponent EQUAL to b's leading exponent, the
    coefficients add (and that term merges with b's leading term).
    """
    if not b:
        return a
    if not a:
        return b
    key = (a, b)
    r = _oadd_memo.get(key)
    if r is not None:
        return r
    eb0 = b[0][0]          # leading exponent of b
    # Keep terms of a with exponent > eb0; handle exponent == eb0 specially.
    kept = []
    merged_coeff = None
    for (e, c) in a:
        k = cmp(e, eb0)
        if k > 0:
            kept.append((e, c))
        elif k == 0:
            merged_coeff = c   # coefficients add with b's leading term
            break              # remaining terms of a have exponent < eb0: dropped
        else:
            break              # exponent < eb0: this and all later dropped
    result = list(kept)
    if merged_coeff is not None:
        # merge: w^eb0 * (merged_coeff + b[0][1]) followed by tail of b
        result.append((eb0, merged_coeff + b[0][1]))
        result.extend(b[1:])
    else:
        result.extend(b)
    out = tuple(result)
    _oadd_memo[key] = out
    return out


# ----------------------------------------------------------------------------
# Readable string
# ----------------------------------------------------------------------------
def to_str(a):
    if not a:
        return "0"
    parts = []
    for (e, c) in a:
        if not e:                       # exponent 0 -> just the coefficient
            parts.append(str(c))
        elif eq(e, ONE):
            base = "w"
            parts.append(base if c == 1 else f"{base}*{c}")
        else:
            es = to_str(e)
            # parenthesize compound exponents
            if len(e) > 1 or e[0][1] != 1 or e[0][0]:
                es = f"({es})"
            base = f"w^{es}"
            parts.append(base if c == 1 else f"{base}*{c}")
    return " + ".join(parts)


# ----------------------------------------------------------------------------
# Om(v) markers (additively principal, "closed" ordinals)
# ----------------------------------------------------------------------------
def Om(v):
    """
    Om(0) = 1
    Om(1) = omega
    Om(2) = omega^omega
    """
    if v == 0:
        return ONE
    if v == 1:
        return OMEGA
    if v == 2:
        return WW
    raise ValueError(v)


# Bound NABLA: keep ordinals strictly below this.  w^(w^2) is plenty.
NABLA = ((W2, 1),)   # w^(w^2)


# ----------------------------------------------------------------------------
# Universe of "small" CNFs to draw from when enumerating / building exponents
# and principal candidates.  Bounded coefficients & exponents.
# ----------------------------------------------------------------------------
COEFF_MAX = 6

def _gen_small_cnfs():
    """
    Generate a small finite set of CNF ordinals < NABLA to serve as the
    candidate universe (used as exponents and as principal-candidate exponents).
    We build them from a small pool of exponents.
    """
    # exponents pool: 0, 1, 2, 3, omega, w*2, w^2
    exp_pool = [ZERO, ONE, TWO, nat(3), OMEGA, ((ONE, 2),), W2]
    cnfs = set()
    cnfs.add(ZERO)
    # single-term ordinals w^e * c
    singles = []
    for e in exp_pool:
        for c in range(1, COEFF_MAX + 1):
            o = ((e, c),)
            if lt(o, NABLA):
                singles.append(o)
                cnfs.add(o)
    # two-term ordinals w^e1*c1 + w^e2*c2 with e1>e2
    sk = sorted(set(exp_pool), key=lambda e: tuple())  # placeholder
    exps_sorted = sorted(set(exp_pool), key=cmp_key())
    for i in range(len(exps_sorted)):
        for j in range(i):  # e1 = exps_sorted[i] > e2 = exps_sorted[j]
            e1 = exps_sorted[i]
            e2 = exps_sorted[j]
            for c1 in range(1, COEFF_MAX + 1):
                for c2 in range(1, COEFF_MAX + 1):
                    o = ((e1, c1), (e2, c2))
                    if lt(o, NABLA):
                        cnfs.add(o)
    return cnfs


import functools
def cmp_key():
    return functools.cmp_to_key(cmp)


# Candidate principal ordinals (w^e, single term coeff 1) used by psi.
def _principal_candidates():
    exp_pool = [ZERO, ONE, TWO, nat(3), nat(4), nat(5), nat(6), nat(7),
                ((ONE, 2),), ((ONE, 3),),
                ((TWO, 1),), ((TWO, 2),), ((TWO, 3),),
                ((TWO, 1), (ONE, 1)), ((TWO, 1), (ZERO, 1)),
                ((nat(3), 1),), W2, ((OMEGA, 1),)]
    cands = []
    seen = set()
    for e in exp_pool:
        o = ((e, 1),)
        if lt(o, NABLA) and o not in seen:
            seen.add(o)
            cands.append(o)
    cands.sort(key=cmp_key())
    return cands

PRINCIPAL_CANDS = _principal_candidates()
SMALL = _gen_small_cnfs()

# The closure under oadd is genuinely INFINITE on the full ordinals below NABLA
# (coefficients of nat(n) grow without bound, all still < NABLA = w^(w^2)).
# For a FINITE empirical model we cap the universe to a fixed finite set
# ALLOWED = SMALL union the principal candidates, and only keep oadd / psi
# results that land inside ALLOWED.  ALLOWED is itself essentially closed
# (it contains all small CNFs with coeff <= COEFF_MAX and the principal
# markers), so this is a faithful finite fragment of Buchholz's C-sets.
ALLOWED = set(SMALL) | set(PRINCIPAL_CANDS)


# ----------------------------------------------------------------------------
# Closure Cset and psi
# ----------------------------------------------------------------------------
# psi memo keyed by (arg, v)
_psi_memo = {}
# Cset memo keyed by (arg, v, canonical)
_cset_memo = {}


def _enum_below(bound):
    """All CNFs in SMALL with value in [0, bound)."""
    return [o for o in SMALL if lt(o, bound)]


def Cset(arg, v, canonical):
    key = (arg, v, canonical)
    if key in _cset_memo:
        return _cset_memo[key]

    omv = Om(v)
    X = set()
    # (C1) all ordinals in [0, Om(v))
    for o in SMALL:
        if lt(o, omv):
            X.add(o)
    X.add(ZERO)

    # 'frontier' = elements added since they were last combined under oadd.
    frontier = set(X)
    psi_done = set()   # xi for which we've already fired (C3)

    for _ in range(200):
        added = False

        # (C2) closed under oadd. Only combine the frontier with everything
        # (and frontier with frontier); previously-combined pairs are skipped.
        if frontier:
            newly = set()
            allX = list(X)
            fl = list(frontier)
            for a in fl:
                for b in allX:
                    s = oadd(a, b)
                    if s not in X and s in ALLOWED:
                        newly.add(s)
                    s2 = oadd(b, a)
                    if s2 not in X and s2 in ALLOWED:
                        newly.add(s2)
            frontier = newly
            if newly:
                X |= newly
                added = True

        # (C3) for xi in X with xi < arg, every subscript u in {0,1,2}:
        #      add psi(xi,u) -- canonical: only when acanon(u,xi).
        c3_new = set()
        for xi in X:
            if xi in psi_done or not lt(xi, arg):
                continue
            psi_done.add(xi)
            for u in (0, 1, 2):
                if canonical and not acanon(u, xi):
                    continue
                p = psi(xi, u)
                if p is not None and p not in X and lt(p, NABLA):
                    c3_new.add(p)
        if c3_new:
            X |= c3_new
            frontier |= c3_new
            added = True

        if not added:
            break

    _cset_memo[key] = X
    return X


def acanon(u, d):
    """d is in Cset(d, u, canonical=False)  (d in its own closure at band u)."""
    return d in Cset(d, u, canonical=False)


def psi(arg, v):
    key = (arg, v)
    if key in _psi_memo:
        return _psi_memo[key]
    # psi(arg,v) = least principal g with Om(v) <= g, g not in Cset(arg,v,False).
    S = Cset(arg, v, canonical=False)
    result = None
    # candidate set: principal ordinals; for v==0 also allow g=1 (=Om(0)).
    cands = [g for g in PRINCIPAL_CANDS if le(Om(v), g)]
    for g in cands:
        if g not in S:
            result = g
            break
    _psi_memo[key] = result
    return result


# ----------------------------------------------------------------------------
# Compute psi in increasing arg order so recursion on smaller args is resolved.
# (Cset(arg) only calls psi(xi,..) for xi<arg, so a single increasing pass with
# memoization converges; the memo + iterative fixpoint handle the rest.)
# ----------------------------------------------------------------------------
def warm_psi(args):
    ordered = sorted(set(args), key=cmp_key())
    for a in ordered:
        for v in (0, 1, 2):
            psi(a, v)


# ----------------------------------------------------------------------------
# oadd / cmp sanity asserts
# ----------------------------------------------------------------------------
def _self_test():
    # omega + 1 = w^1 + w^0  = ((one,1),(zero,1))
    assert oadd(OMEGA, ONE) == ((ONE, 1), (ZERO, 1)), to_str(oadd(OMEGA, ONE))
    # 1 + omega = omega
    assert eq(oadd(ONE, OMEGA), OMEGA), to_str(oadd(ONE, OMEGA))
    # omega^2 + omega = w^2 + w^1
    assert oadd(W2, OMEGA) == ((TWO, 1), (ONE, 1)), to_str(oadd(W2, OMEGA))
    # comparison sanity
    assert lt(ONE, OMEGA)
    assert lt(OMEGA, W2)
    assert lt(W2, WW)
    assert lt(WW, NABLA)
    assert lt(nat(2), OMEGA)
    assert eq(oadd(ZERO, OMEGA), OMEGA)
    assert eq(oadd(OMEGA, ZERO), OMEGA)
    # omega + omega = w*2
    assert oadd(OMEGA, OMEGA) == ((ONE, 2),), to_str(oadd(OMEGA, OMEGA))
    print("oadd / cmp self-tests: PASS")


# ----------------------------------------------------------------------------
# Main: run the Remark check.
# ----------------------------------------------------------------------------
def main():
    _self_test()

    # Build the list of test args: first ~15 ordinals in increasing order,
    # plus a few principal ones.
    first_ordinals = [nat(n) for n in range(0, 8)]      # 0..7
    extras = [OMEGA, oadd(OMEGA, ONE), oadd(OMEGA, nat(2)),
              ((ONE, 2),),            # omega*2
              oadd(((ONE, 2),), ONE), # omega*2 + 1
              W2, oadd(W2, OMEGA), WW]
    args = []
    seen = set()
    for a in first_ordinals + extras:
        if a not in seen:
            seen.add(a)
            args.append(a)
    args.sort(key=cmp_key())

    warm_psi(args)

    # psi table
    print()
    print("=== psi table ===")
    print(f"{'arg':<18} {'psi(.,0)':<14} {'psi(.,1)':<16} {'psi(.,2)':<18}")
    for a in args:
        row = [to_str(a)]
        for v in (0, 1, 2):
            p = psi(a, v)
            row.append("None" if p is None else to_str(p))
        print(f"{row[0]:<18} {row[1]:<14} {row[2]:<16} {row[3]:<18}")

    # Remark check
    print()
    print("=== Cset vs Cset_c (canonical) Remark check ===")
    total = 0
    matching = 0
    mismatching = 0
    mismatch_details = []
    high_subscript_seen = False
    high_subscript_caused_mismatch = False
    # Counters describing how often the canonical filter (acanon) skips a
    # generator, and whether the skipped generators were "contributing".
    canon_skips = 0            # (xi,u) with xi<arg in S, u>=v, acanon False
    canon_skips_psi_defined = 0  # ... and psi(xi,u) is defined (would-be element)
    canon_skip_examples = []

    for v in (0, 1, 2):
        for arg in args:
            total += 1
            S = Cset(arg, v, canonical=False)
            Sc = Cset(arg, v, canonical=True)
            if S == Sc:
                matching += 1
            else:
                mismatching += 1
                extra = S - Sc          # in S but not Sc
                missing = Sc - S        # in Sc but not S (should be empty normally)
                detail = {
                    'arg': arg, 'v': v,
                    'extra': sorted(extra, key=cmp_key()),
                    'missing': sorted(missing, key=cmp_key()),
                }
                mismatch_details.append(detail)

            # Analyze the non-canonical high-subscript generator case across the
            # full (non-canonical) closure regardless of match, to detect whether
            # the central proof case ever occurs.
            for xi in S:
                if lt(xi, arg):
                    for u in (0, 1, 2):
                        if u >= v and not acanon(u, xi):
                            canon_skips += 1
                            p = psi(xi, u)
                            if p is not None and lt(p, NABLA):
                                canon_skips_psi_defined += 1
                                high_subscript_seen = True
                                if len(canon_skip_examples) < 8:
                                    canon_skip_examples.append(
                                        (to_str(arg), v, to_str(xi), u,
                                         to_str(p), p in S))
                                # Did this generator produce an element that is
                                # in S\Sc (i.e. canonical would not add it)?
                                if S != Sc and p in (S - Sc):
                                    high_subscript_caused_mismatch = True

    # Report mismatches in detail
    if mismatch_details:
        print(f"\n{len(mismatch_details)} MISMATCH(es):")
        for d in mismatch_details:
            print(f"\n  arg={to_str(d['arg'])}, v={d['v']}")
            if d['extra']:
                print(f"    in S\\Sc (extra in non-canonical): "
                      f"{[to_str(x) for x in d['extra']]}")
                for x in d['extra']:
                    # is x = psi(xi,u) for some xi in S, xi<arg, !acanon(u,xi), u>=v?
                    S = Cset(d['arg'], d['v'], canonical=False)
                    found = []
                    for xi in S:
                        if lt(xi, d['arg']):
                            for u in (0, 1, 2):
                                if psi(xi, u) is not None and eq(psi(xi, u), x):
                                    flag = (u >= d['v']) and (not acanon(u, xi))
                                    found.append((to_str(xi), u, acanon(u, xi),
                                                  u >= d['v'], flag))
                    print(f"      {to_str(x)} generated by (xi,u,acanon,u>=v,"
                          f"noncanon-high): {found}")
            if d['missing']:
                print(f"    in Sc\\S (extra in canonical, unexpected): "
                      f"{[to_str(x) for x in d['missing']]}")
    else:
        print("\nAll tested (arg,v) pairs: Cset == Cset_c  (MATCH).")

    print()
    print("=== Analysis of non-canonical high-subscript (u>=v) generator case ===")
    print(f"  Did the case ever occur (some xi<arg in S, u>=v, !acanon(u,xi), "
          f"psi defined)? {high_subscript_seen}")
    print(f"  Did it ever cause a Cset != Cset_c mismatch? "
          f"{high_subscript_caused_mismatch}")
    print(f"  Generators skipped by canonical filter (xi<arg in S, u>=v, "
          f"acanon False): {canon_skips}")
    print(f"    ... of which psi(xi,u) was DEFINED (would-be contributing): "
          f"{canon_skips_psi_defined}")
    if canon_skip_examples:
        print("    examples (arg, v, xi, u, psi(xi,u), psi-already-in-S):")
        for ex in canon_skip_examples:
            print(f"      arg={ex[0]}, v={ex[1]}, xi={ex[2]}, u={ex[3]}, "
                  f"psi={ex[4]}, already_in_S={ex[5]}")

    print()
    print("=== SUMMARY ===")
    print(f"  total (arg,v) pairs tested: {total}")
    print(f"  matching   (Cset == Cset_c): {matching}")
    print(f"  mismatching (Cset != Cset_c): {mismatching}")


if __name__ == "__main__":
    main()
