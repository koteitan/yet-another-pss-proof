#!/usr/bin/env python3
"""
Test the noncanon_strict_descent candidates:

Given non-canonical xi (acanon(w,xi)=False) with c=psi(xi,w) defined:
  (B) is psi(c, w) == c ?   (value is a psi-fixpoint)
  (B') is psi(c, w) == psi(xi,w) == c ?  (so eta=c reproduces the value)
  is c < xi (strict) or c == xi (fixpoint) ?
  if c==xi: is xi then "canonical"? (contradiction expected)
Also: among ordinals delta < xi, which reproduce psi(delta,w)=c, and is the
LEAST such < xi ?  (strict descent target candidates)
"""
import sys
sys.path.insert(0, '/home/koteitan/proofs/ya-pss/git/.claude/worktrees/agent-aa427cfe3b19bad3a/tools')
from cset_remark_check import (Cset, psi, acanon, lt, le, eq, to_str, cmp_key,
                               Om, warm_psi, nat, OMEGA, ONE, TWO, W2, WW, ZERO,
                               oadd, SMALL)

def main():
    allargs = sorted(SMALL, key=cmp_key())
    warm_psi(allargs)
    n=0; bfix=0; cstrict=0; cfix=0; cval_fix=0
    bad_b=[]
    for w in (0,1,2):
        for xi in allargs:
            if acanon(w,xi): continue
            c = psi(xi, w)
            if c is None: continue
            n+=1
            # c < xi or c == xi?
            if eq(c, xi): cfix+=1
            elif lt(c, xi): cstrict+=1
            # psi(c,w) ?
            pc = psi(c, w)
            if pc is not None and eq(pc, c): bfix+=1
            if pc is not None and eq(pc, c) and eq(c, psi(xi,w)): cval_fix+=1
            else:
                bad_b.append((w,to_str(xi),to_str(c),to_str(pc) if pc else None))
    print(f"non-canonical (xi,w) with psi defined: {n}")
    print(f"  c == xi (psi-fixpoint argument): {cfix}")
    print(f"  c <  xi (strict):                {cstrict}")
    print(f"  psi(c,w) == c (value is fixpoint): {bfix}")
    print(f"  eta=c reproduces value (psi(c,w)==c==psi(xi,w)): {cval_fix}")
    if bad_b:
        print(f"  psi(c,w) != c in {len(bad_b)} cases (sample):")
        for b in bad_b[:20]:
            print("   ", b)

if __name__=="__main__":
    main()
