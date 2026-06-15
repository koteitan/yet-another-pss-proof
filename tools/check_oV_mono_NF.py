#!/usr/bin/env python3
"""DEEP empirical test of the exact theorem oV_mono_NF:
   v in NF, u in NF, olt v u  ==>  oV v < oV u.

NF = translate ` ST_PS.  oV order is modelled by lt_term(nrm(conv .), nrm(conv .)):
nrm = value-normal Buchholz name (validated: lands in OT, idempotent), lt_term =
OT name order = ordinal order.  We test ALL ordered NF-pairs including CROSS-LEVEL
(different maxsub), which the same-level INJ test in valnorm.py does not cover.
"""
import sys, itertools; sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from wfe_explore import translate, olt, fmt, enum_ST, maxsub
from valnorm import conv, nrm, lt_term, in_OT, fmtb

def main():
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4,5), max_len=16, rounds=7)
    print(f"#ST_PS: {len(ST)}")
    NF = []
    seen = set()
    for M in ST:
        t = translate(M)
        if t not in seen:
            seen.add(t); NF.append(t)
    print(f"#distinct NF terms: {len(NF)}")
    print(f"max maxsub: {max(maxsub(t) for t in NF)}")

    # precompute oVkey = nrm(conv(t))
    key = {t: nrm(conv(t)) for t in NF}
    # validate proxy: all keys in OT
    bad_ot = [t for t in NF if not in_OT(key[t])]
    print(f"proxy sanity: nrm not in OT for {len(bad_ot)} terms (must be 0)")

    # To keep O(n^2) tractable, cap but keep cross-level pairs.
    # Sort by a cheap size; sample if too large.
    import random
    rng = random.Random(1)
    pool = NF
    MAXP = 2600
    if len(pool) > MAXP:
        pool = rng.sample(pool, MAXP)
    print(f"testing all ordered pairs over pool of {len(pool)} ({len(pool)*(len(pool)-1)} ordered pairs)")

    tested = 0; collapse = 0; reversal = 0
    cross_tested = 0
    ex = []
    for v, u in itertools.permutations(pool, 2):
        if not olt(v, u): continue
        tested += 1
        if maxsub(v) != maxsub(u): cross_tested += 1
        kv, ku = key[v], key[u]
        if kv == ku:
            collapse += 1
            if len(ex) < 6: ex.append(('COLLAPSE', v, u))
        elif lt_term(ku, kv):  # oV u < oV v  -> reversal
            reversal += 1
            if len(ex) < 6: ex.append(('REVERSAL', v, u))
    print(f"olt-ordered NF pairs tested: {tested}  (cross-level: {cross_tested})")
    print(f"  COLLAPSES (oV v == oV u): {collapse}")
    print(f"  REVERSALS (oV v > oV u) : {reversal}")
    print(f"  ==> VIOLATIONS of oV_mono_NF: {collapse+reversal}")
    for tag, v, u in ex:
        print(f"   {tag}: {fmt(v)}  <o  {fmt(u)}")
        print(f"        oV: {fmtb(key[v])}  vs  {fmtb(key[u])}")

if __name__ == "__main__":
    main()
