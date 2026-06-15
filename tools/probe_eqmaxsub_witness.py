#!/usr/bin/env python3
"""Soundness gate for proj0_bothfire_eqmaxsub_NF (Lean Three encoding).

The residual: head-0 NF args b,f with olt b f, both pfire 0, maxsub b = maxsub f
  ==> olt (proj 0 b) (proj 0 f).

We KNOW lead(proj0 b)=maxsub b = maxsub f = lead(proj0 f) = k, so both proj
results are P k _ _ ; the comparison reduces to their .b (head arg) and .c.

This probe explores, on the eqmaxsub firing pairs at deep closure:
  (0) the residual itself (olt (proj0 b)(proj0 f))  -- the target
  (1) structure of proj0 b vs proj0 f : leads tie (k=k); compare args/tails
  (2) WITNESS candidates g' in Gterm 0 f, not olt g' f, with olt (proj0 b) g'
      and whether proj0 f itself is such a witness (g' = proj0 f)
  (3) does proj0 b strictly dominate proj0-arg of f? i.e. compare (proj0 b).b
  (4) candidate invariant: olt (proj0 b) (proj0 f) reduces to recursion on .b
      proj0 b = P k b1 c1, proj0 f = P k f1 d1; olt iff (olt b1 f1) or
      (b1=f1 and olt c1 d1).  Check whether b1,f1 themselves satisfy a clean
      relation (e.g. olt b1 f1 OR (b1=f1)).
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import translate, enum_ST, olt, maxsub, spine
Z = ()

def le(s, t): return s == t or olt(s, t)
def Gterm(u, t):
    if t == Z: return []
    a, b, c = t; out = []
    if u <= a: out.append(b); out += Gterm(u, b)
    out += Gterm(u, c); return out
def pfire(u, b): return any(not olt(g, b) for g in Gterm(u, b))
def proj(u, b):
    while True:
        bad = [g for g in Gterm(u, b) if not olt(g, b)]
        if not bad: return b
        m = bad[0]
        for h in bad[1:]:
            if olt(m, h): m = h
        b = m
def lead(t): return 0 if t == Z else t[0]

def main(seed=4, ns=(1,2,3,4), maxlen=14, rounds=8):
    ST = enum_ST(seed_max_v=seed, oper_ns=ns, max_len=maxlen, rounds=rounds)
    NF = sorted({translate(M) for M in ST}, key=str)
    args = sorted({t[1] for t in NF if t != Z and t[0] == 0}, key=str)
    print(f"NF terms {len(NF)}, distinct head-0 args {len(args)}")
    fire = [b for b in args if pfire(0, b)]
    print(f"firing args {len(fire)}")

    tot = res_bad = 0
    wit_is_projf = wit_diff = wit_none = 0
    argrel = {'olt_b1_f1': 0, 'b1_eq_f1': 0, 'rev': 0, 'other': 0}
    examples_bad = []
    for b in fire:
        pb = proj(0, b)
        for f in fire:
            if not olt(b, f): continue
            if maxsub(b) != maxsub(f): continue
            tot += 1
            pf = proj(0, f)
            ok = olt(pb, pf)
            if not ok:
                res_bad += 1
                if len(examples_bad) < 6: examples_bad.append((b, f, pb, pf))
                continue
            # witness analysis: find g' in Gterm0 f, not olt g' f, olt pb g'
            cands = [gp for gp in Gterm(0, f) if (not olt(gp, f)) and olt(pb, gp)]
            if any(gp == pf for gp in cands): wit_is_projf += 1
            elif cands: wit_diff += 1
            else: wit_none += 1
            # arg-level relation of the proj results (both P k _ _)
            if pb != Z and pf != Z:
                _, b1, c1 = pb; _, f1, d1 = pf
                if olt(b1, f1): argrel['olt_b1_f1'] += 1
                elif b1 == f1: argrel['b1_eq_f1'] += 1
                elif olt(f1, b1): argrel['rev'] += 1
                else: argrel['other'] += 1
    print(f"\n=== eqmaxsub firing pairs (olt b f): {tot}")
    print(f"RESIDUAL olt(proj0 b)(proj0 f) violations: {res_bad}")
    for e in examples_bad: print("   RES VIOL", e)
    print(f"\nwitness g' in Gterm0 f (not olt g' f, olt pb g'):")
    print(f"  proj0 f IS a witness: {wit_is_projf}")
    print(f"  only a DIFFERENT critical: {wit_diff}")
    print(f"  NO witness found: {wit_none}")
    print(f"\nproj-result head-arg relation (pb=P k b1 _, pf=P k f1 _):")
    print(f"  {argrel}")

if __name__ == '__main__':
    main()
