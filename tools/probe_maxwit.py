#!/usr/bin/env python3
"""
Investigate the MAXIMAL-witness / canonical-rep structure of psi values,
and the key facts needed for canonical_witness_in_Cset_c.

For the residue we need: given non-canonical xi (xi<alpha, in Cset_c(alpha,v)),
find canonical delta in alpha INTER Cset_c with psi(delta,w)=psi(xi,w).

Since the model's non-canonical xi are all >= Om(2) with psi=None, we instead
test the underlying MATHEMATICAL CLAIMS abstractly on ALL ordinals where psi is
defined:

  (M1) For every xi with psi(xi,w) defined, there is a CANONICAL delta
       with psi(delta,w)=psi(xi,w) and delta = wit_max = the LARGEST such delta
       that is <= some bound. Is the canonical rep = the value c itself when
       acanon(w,c)? Test: is c = psi(xi,w) ALWAYS such that the *least delta*
       with psi(delta,w)=c is canonical?

  (M2) Key: canonical_arg existence. For value c=psi(xi,w), define
       D = { delta : psi(delta,w)=c }. Find min(D) and max(D within SMALL).
       Report acanon(w, min D), acanon(w, max D).
"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/ya-pss/git/.claude/worktrees/agent-aa427cfe3b19bad3a/tools')
from cset_remark_check import (Cset, psi, acanon, lt, le, eq, to_str, cmp_key,
                               Om, warm_psi, nat, OMEGA, ONE, TWO, W2, WW, ZERO,
                               oadd, SMALL, PRINCIPAL_CANDS)

def main():
    allargs = sorted(SMALL, key=cmp_key())
    warm_psi(allargs)

    print("=== For each value c=psi(xi,w): structure of witness set D={d: psi(d,w)=c} ===")
    print("    cols: w, c, |D|, minD, acanon(w,minD), maxD, acanon(w,maxD), c==minD")
    seen_vals = set()
    n_mincanon=0; n_maxcanon=0; n_total=0; n_c_eq_min=0
    for w in (0,1,2):
        for xi in allargs:
            c = psi(xi, w)
            if c is None: continue
            keyv=(w,c)
            if keyv in seen_vals: continue
            seen_vals.add(keyv)
            D = [d for d in allargs if (psi(d,w) is not None and eq(psi(d,w),c))]
            if not D: continue
            n_total+=1
            minD=D[0]; maxD=D[-1]
            ac_min=acanon(w,minD); ac_max=acanon(w,maxD)
            if ac_min: n_mincanon+=1
            if ac_max: n_maxcanon+=1
            cem = eq(c,minD)
            if cem: n_c_eq_min+=1
            if n_total<=40:
                print(f"  w={w} c={to_str(c):<12} |D|={len(D):<3} minD={to_str(minD):<10} "
                      f"acMin={ac_min} maxD={to_str(maxD):<10} acMax={ac_max} c==minD={cem}")
    print()
    print(f"distinct values tested: {n_total}")
    print(f"  least witness canonical: {n_mincanon}/{n_total}")
    print(f"  max  witness canonical: {n_maxcanon}/{n_total}")
    print(f"  c == least witness:     {n_c_eq_min}/{n_total}")

    # KEY TEST: is the canonical witness ALWAYS <= xi for the value c=psi(xi,w)?
    # i.e. does a canonical delta <= xi with psi(delta,w)=c always exist?
    print()
    print("=== canonical witness <= xi existence (the residue, ignoring closure-membership) ===")
    nres=0; nok=0; bad=[]
    for w in (0,1,2):
        for xi in allargs:
            if acanon(w,xi):   # only non-canonical xi
                continue
            c = psi(xi, w)
            if c is None: continue
            nres+=1
            # canonical delta <= xi with psi(delta,w)=c ?
            ok=False
            for d in allargs:
                if not le(d,xi): continue
                if acanon(w,d) and psi(d,w) is not None and eq(psi(d,w),c):
                    ok=True; break
            if ok: nok+=1
            else: bad.append((w,to_str(xi),to_str(c)))
    print(f"non-canonical (xi,w) with psi defined: {nres}; canonical delta<=xi exists: {nok}")
    if bad:
        print(f"  NO canonical delta<=xi in {len(bad)} cases:")
        for b in bad[:20]:
            print("   ", b)

if __name__=="__main__":
    main()
