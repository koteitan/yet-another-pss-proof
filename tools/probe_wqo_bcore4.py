#!/usr/bin/env python3
"""probe_wqo_bcore4.py -- maximally charitable final test for the architect route.

bcore3 killed the right-then-left grow chain (per-step olt flips 15%).  Two last
charitable questions:

 (Q1) GROW-RIGHT-ONLY (the genuine ASCENDING-COPY / copy-domination direction,
   architect i_0=max{i|(i,0)<=_M(i,j1)}): extend the infix only to the RIGHT
   (adding later ascending copies, which dominate earlier ones).  Is the per-step
   olt monotone for the right-grow segment?  (The left-grow = prepending the green
   prefix is what flipped; maybe copy-domination only claims the right segment.)

 (Q2) EXISTENTIAL best-case: over ALL single-column-insertion orders from K to B
   (K subset ... subset B by adding one of B's columns at a time, in ANY order
   keeping a contiguous... -- we relax to ANY column subset that stays a valid
   translate), is there ANY fully-olt-monotone chain K=C0 <o C1 <o ... <o B?
   We bound the search (small gaps) and report the fraction of witnesses for which
   SOME monotone insertion chain exists.  If even the existential fails, NO
   generation induction (however clever the i_0 path) can be monotone -> route dead.

If grow-right is also non-monotone AND the existential frequently fails, the
"<=_e-generation is richer" thesis is decisively false: the failure is intrinsic
to the lead-0/lead-1 head polarity, not to the chain ORDER.
"""
import sys
sys.path.insert(0, '.')
from fast_pss import Lng, entry, diagSeq, oper
from wfe_explore import translate, olt
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt
from probe_bmocf_ancestor import enum_depth
from itertools import permutations

Z = ()
def lead(t): return t[0] if t else -1
def Gterm(u, t):
    if t == (): return []
    a, b, c = t
    out = []
    if u <= a:
        out.append(b); out += Gterm(u, b)
    out += Gterm(u, c)
    return out
def find_infix(B, x):
    n = len(B); cands = []
    for i in range(n):
        for j in range(i+1, n+1):
            if translate(tuple(B[i:j])) == x:
                cands.append((i, j))
    if not cands: return None
    cands.sort(key=lambda ij: (-(ij[1]-ij[0]), ij[0]))
    return cands[0]

def main():
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 30, rounds)
        hosts = [M for M in seen if Lng(M) <= 20 and all(c[1] <= 1 for c in M)
                 and M and M[0] == (0, 0)]
        md = max(seen.values())

        # Q1 grow-right-only monotonicity
        gr_first_chk = gr_first_bad = 0
        gr_inner_chk = gr_inner_bad = 0
        gr_chains = gr_mono = 0
        # Q2 existential monotone insertion chain (bounded search)
        ex_total = ex_has_mono = ex_searched = 0

        for B0 in hosts:
            B = tuple(B0[1:])
            tB = translate(B)
            if tB == Z: continue
            n = len(B)
            G0 = set(Gterm(0, tB))
            for x in G0:
                if x == tB: continue
                ij = find_infix(B, x)
                if ij is None: continue
                i, j = ij
                K = tuple(B[i:j]); tK = translate(K)

                # ---- Q1 grow RIGHT only: [i:j] -> [i:j+1] -> ... -> [i:n] ----
                # (then the result [i:n] is a SUFFIX; we stop at right boundary =n,
                # not prepending the prefix; this isolates the ascending-copy dir.)
                hi = j; prev = tK; mono = True; first = True
                while hi < n:
                    hi += 1
                    cur = translate(tuple(B[i:hi]))
                    if cur == Z or cur == prev:
                        prev = cur; first = False; continue
                    ok = olt(prev, cur)
                    if first:
                        gr_first_chk += 1
                        if not ok: gr_first_bad += 1
                        first = False
                    else:
                        gr_inner_chk += 1
                        if not ok: gr_inner_bad += 1; mono = False
                    prev = cur
                gr_chains += 1
                if mono: gr_mono += 1

                # ---- Q2 existential monotone insertion (only when gap small) ----
                # columns of B not in the infix K = positions [0:i] + [j:n].
                missing = list(range(0, i)) + list(range(j, n))
                if 0 < len(missing) <= 6:
                    ex_total += 1; ex_searched += 1
                    # try all orders of inserting the missing columns; the partial
                    # block at each stage = B restricted to (K's cols) U (inserted),
                    # kept in original B-column order (contiguity not required; we
                    # take the sub-list of B at the selected indices).
                    base = set(range(i, j))
                    found = False
                    for perm in permutations(missing):
                        cols = set(base)
                        prevt = tK; good = True
                        for c in perm:
                            cols.add(c)
                            sub = tuple(B[k] for k in sorted(cols))
                            ct = translate(sub)
                            if ct == prevt:
                                continue
                            if not olt(prevt, ct):
                                good = False; break
                            prevt = ct
                        if good:
                            found = True; break
                    if found: ex_has_mono += 1
                elif len(missing) == 0:
                    pass  # K==B, skip
                else:
                    ex_total += 1  # too big to search; counts as "unknown"

        print(f'[closure+{rounds}] maxdepth={md} hosts={len(hosts)}')
        print(f'  Q1 GROW-RIGHT-ONLY (ascending-copy dir) per-step olt:')
        print(f'     first chk={gr_first_chk} VIOL={gr_first_bad}   '
              f'inner chk={gr_inner_chk} VIOL={gr_inner_bad}   '
              f'fully-mono chains={gr_mono}/{gr_chains}')
        print(f'  Q2 EXISTENTIAL monotone insertion chain (bounded search):')
        print(f'     searched={ex_searched} of total={ex_total};  HAS-mono-chain={ex_has_mono}'
              f'  (no-mono-chain={ex_searched-ex_has_mono})')

if __name__ == '__main__':
    main()
