#!/usr/bin/env python3
"""probe_m3_collapse_case.py -- verify the COLLAPSE case of the M3 singleton step.

For P a b Z with maxsub b > a (b IS a critical subterm, the psi_0 collapse), the
arg b sits at cr_inv b = cr_inv(P a b Z) - 1 = n-1 (lower stratum).  The Towsner
Lemma 3.10 'ϑ-accessibility' gives Acc(P a b Z) from b's accessibility at the
lower stratum.  We need: the ARGDROP predecessors P a b' Z (b'<o b) have b' ALSO
accessible -- but via WHAT?

Two sub-cases of the singleton step P a b Z:
  (NONCOLLAPSE) maxsub b <= a: b NOT critical; cr_inv(P a b Z)=cr_inv... b has
      cr <= cr(P a b Z); arg-accessibility on b within SAME stratum n.  ARGDROP
      preds P a b' Z with b'<o b: b' accessible by the M2-style induction on b.
  (COLLAPSE) maxsub b > a: b critical, b in critSub(P a b Z), cr_inv b = n-1.
      For P a b Z in Mn n, need b in AccBelow n (i.e. b in Accn(n-1)), the LOWER-
      stratum IH.  The ARGDROP preds P a b' Z (b'<o b): is b' ALSO at stratum
      <= n-1 (so the SAME lower-stratum accessibility of b covers them)?

KEY CHECK: for COLLAPSE P a b Z (maxsub b > a), do all ARGDROP predecessors
P a b' Z (b'<o b, in Mn n) have cr_inv b' <= cr_inv b = n-1?  i.e. the arg-drop
stays within b's (lower) stratum, so Acc b (lower-stratum IH) suffices.

Also: in the NONCOLLAPSE case, the arg-accessibility induction on b is within
stratum n and needs b accessible -- but b is the ARG, cr_inv b <= n.  If cr_inv
b < n it's lower-stratum IH; if cr_inv b == n we recurse (M2-style strong arg
induction).  Check that the NONCOLLAPSE arg b with cr_inv b == n is handled
(its own preds are arg-drops too -> well-founded on tsize).
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import translate, olt, maxsub
from probe_bmocf_ancestor import enum_depth

Z = ()

def cr_inv(t):
    if t == (): return 0
    a, b, c = t
    inv = 1 if (b != () and maxsub(b) > a) else 0
    return max(inv + cr_inv(b), cr_inv(c))

def critSub(t):
    out = []
    def rec(t):
        if t == (): return
        a, b, c = t
        if b != () and maxsub(b) > a:
            out.append(b)
        rec(b); rec(c)
    rec(t); return out

def summands(t):
    if t == (): return []
    a, b, c = t
    return [(a, b, ())] + summands(c)

def in_Mn(s, n):
    if cr_inv(s) > n:
        return False
    return all(cr_inv(bb) < n for bb in critSub(s))

def main():
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 30, rounds)
        NF = set(translate(M) for M in seen)
        NF.discard(Z)
        NFl = list(NF)
        md = max(seen.values())
        sing = [t for t in NF if t[2] == Z and t != Z]

        # collapse vs noncollapse singles
        n_collapse = n_noncollapse = 0
        # COLLAPSE: argdrop preds P a b' Z have cr b' <= cr b (= n-1)?
        col_argdrop = col_argdrop_within = 0
        col_ex = []
        # NONCOLLAPSE: argdrop preds have cr b' <= cr b? (stays in stratum)
        ncol_argdrop = ncol_argdrop_within = 0

        for t in sing:
            n = cr_inv(t)
            a, b, _ = t
            collapse = (b != Z and maxsub(b) > a)
            if collapse: n_collapse += 1
            else: n_noncollapse += 1
            crb = cr_inv(b)
            for v in NFl:
                if v == t or not olt(v, t):
                    continue
                for s in summands(v):
                    sa, sb, _ = s
                    if cr_inv(s) < n or not in_Mn(s, n):
                        continue
                    if not olt(s, t):
                        continue
                    if sa == a and olt(sb, b):   # ARGDROP
                        if collapse:
                            col_argdrop += 1
                            if cr_inv(sb) <= crb:
                                col_argdrop_within += 1
                            elif len(col_ex) < 6:
                                col_ex.append((t, s, n, crb, cr_inv(sb)))
                        else:
                            ncol_argdrop += 1
                            if cr_inv(sb) <= crb:
                                ncol_argdrop_within += 1

        print(f'[closure+{rounds}] maxdepth={md} singles={len(sing)} '
              f'(collapse={n_collapse} noncollapse={n_noncollapse})')
        print(f'  COLLAPSE   argdrop preds: {col_argdrop}  '
              f'with cr(b\')<=cr(b)=n-1: {col_argdrop_within}')
        for t, s, n, crb, crsb in col_ex[:4]:
            from wfe_explore import fmt as tf
            print(f'     OUT t={tf(t)[:28]} pred={tf(s)[:28]} n={n} crb={crb} crsb={crsb}')
        print(f'  NONCOLLAPSE argdrop preds: {ncol_argdrop}  '
              f'with cr(b\')<=cr(b): {ncol_argdrop_within}')

if __name__ == '__main__':
    main()
