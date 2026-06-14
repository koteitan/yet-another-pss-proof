#!/usr/bin/env python3
"""Why is the residue set empty?  Examine non-canonical members of Cset_c."""
import sys
sys.path.insert(0, '/home/koteitan/proofs/ya-pss/git/.claude/worktrees/agent-aa427cfe3b19bad3a/tools')
from cset_remark_check import (Cset, psi, acanon, lt, le, eq, to_str, cmp_key,
                               Om, warm_psi, nat, OMEGA, ONE, TWO, W2, WW, ZERO,
                               oadd, SMALL)

def Cset_c(arg, v):
    return Cset(arg, v, canonical=True)

def main():
    first = [nat(n) for n in range(0, 10)]
    extras = [OMEGA, oadd(OMEGA, ONE), oadd(OMEGA, nat(2)), ((ONE, 2),),
              oadd(((ONE, 2),), ONE), W2, oadd(W2, OMEGA), WW]
    args = []; seen=set()
    for a in first + extras:
        if a not in seen: seen.add(a); args.append(a)
    args.sort(key=cmp_key()); warm_psi(args)

    # For each (alpha,v): list members xi<alpha that are non-canonical at some w>=v
    print("=== non-canonical members of Cset_c(alpha,v) with xi<alpha ===")
    cnt_noncanon_member = 0
    for v in (0,1,2):
        for alpha in args:
            Sc = Cset_c(alpha, v)
            for xi in sorted(Sc, key=cmp_key()):
                if not lt(xi, alpha): continue
                for w in (0,1,2):
                    if w < v: continue
                    if not acanon(w, xi):
                        cnt_noncanon_member += 1
                        if cnt_noncanon_member <= 40:
                            print(f"  alpha={to_str(alpha)} v={v}: xi={to_str(xi)} NOT acanon(w={w}); "
                                  f"psi(xi,w)={to_str(psi(xi,w)) if psi(xi,w) else None}")
    print(f"total non-canonical (xi<alpha, w>=v) member instances: {cnt_noncanon_member}")

    # Separately: are there ANY ordinals xi that are non-canonical at some w with v<=w?
    print()
    print("=== global: which xi in SMALL are non-canonical at w in {0,1,2}? ===")
    cnt=0
    for xi in sorted(SMALL, key=cmp_key()):
        for w in (0,1,2):
            if not acanon(w, xi):
                cnt+=1
                if cnt<=40:
                    print(f"  xi={to_str(xi)}  NOT acanon(w={w}); psi(xi,w)={to_str(psi(xi,w)) if psi(xi,w) else None}")
    print(f"total (xi,w) non-canonical instances in SMALL: {cnt}")

if __name__ == "__main__":
    main()
