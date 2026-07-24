#!/usr/bin/env python3
"""CRUX v3 -- the FAITHFUL core statement.

Host H in ST_PS (all start with (0,0)).  B := H[1:] (the descendant block).
Then (0,0)::B = H in ST_PS.  Core:
    for every SubBlock K of B:  olt (translate K) (translate B).
(SubBlock = reflexive-transitive takeWhile/dropWhile sub-block relation.)
Restrict to the row1<=1 fragment of B, matching PROOF-STATUS's whole-image claim.

TASK 5: re-confirm 0 violations at closure+5/+6.
CRUX:    split each (B,K) by lead(translate K) vs lead(translate B):
            lead K <  lead B : auto olt (EASY / local)
            lead K == lead B : the HARD residual (head-1-nested) -- olt depends
                               on forest position.  Test whether candidate
                               BMOCF measures give a SOUND+COMPLETE predictor of
                               olt on the HARD class (=> tractable) or not
                               (=> difficulty merely relocates).
"""
import sys, functools
sys.path.insert(0, '.')
from fast_pss import oper, diagSeq, Lng, le0, entry, nextrel1
from wfe_explore import translate, olt, maxsub
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt
from probe_bmocf_ancestor import build_next_le, enum_depth

def lead_t(t): return t[0] if t else -1

def subblocks(B):
    """reflexive-transitive takeWhile/dropWhile sub-blocks of B (lean SubBlock)."""
    res = set()
    def rec(seg):
        seg = tuple(seg)
        res.add(seg)
        if not seg: return
        (x, y) = seg[0]; rest = seg[1:]
        i = 0
        while i < len(rest) and rest[i][0] > x: i += 1
        if rest[:i]: rec(rest[:i])
        if rest[i:]: rec(rest[i:])
    rec(tuple(B))
    return res

# candidate measures over a block
def mu_len(B): return Lng(B)
def mu_nextchain(B):
    n = Lng(B)
    if n == 0: return 0
    nx, le = build_next_le(tuple(B))
    adj = {j: [] for j in range(n)}
    for (a, b) in nx[0]: adj[a].append(b)
    @functools.lru_cache(None)
    def lp(j): return 1 + max((lp(k) for k in adj[j]), default=0)
    r = max(lp(j) for j in range(n)); lp.cache_clear(); return r

def main():
    for rounds in (5, 6):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        hosts = [M for M in seen if Lng(M) <= 16 and Lng(M) >= 2]
        md = max(seen.values())

        checked = viol = 0; cex = []
        easy = hard = 0
        # predictor soundness/completeness on HARD class
        # predictor: "K's last column NOT row-0 reachable from K col0" (non-ascension)
        pred_sound_bad = 0   # predictor says olt-true but olt false  (UNSOUND)
        pred_miss = 0        # predictor says olt-false but olt true   (incomplete)
        pred_hit = 0
        hard_olt_false = 0
        hard_ex = []
        for H in hosts:
            B = H[1:]
            if not B: continue
            if not all(c[1] <= 1 for c in B): continue   # row1<=1 fragment
            tB = translate(B); leadB = lead_t(tB)
            for K in subblocks(B):
                if not K: continue
                tK = translate(K)
                checked += 1
                below = olt(tK, tB)
                if not below and K != tuple(B):
                    viol += 1
                    if len(cex) < 6: cex.append((H, B, K))
                if K == tuple(B): continue
                lK = lead_t(tK)
                if lK < leadB:
                    easy += 1
                elif lK == leadB:
                    hard += 1
                    if not below: hard_olt_false += 1
                    # predictor P_anc: last col of K not row-0-reachable from col0
                    nK = Lng(K)
                    asc = le0(tuple(K), 0, nK-1) if nK >= 1 else False
                    pred_olt = (not asc)  # predict olt when NO ascension
                    if pred_olt and not below: pred_sound_bad += 1
                    if (not pred_olt) and below: pred_miss += 1
                    if pred_olt and below: pred_hit += 1
                    if len(hard_ex) < 6:
                        hard_ex.append((B, K, below, asc))

        print(f'[closure+{rounds}] maxdepth={md} hosts={len(hosts)}')
        print(f'  TASK5 core (SubBlock olt): checked={checked} violations={viol}')
        for H, B, K in cex[:4]:
            print('    CEX H', mfmt(H), 'B', mfmt(B), 'K', mfmt(K),
                  '| tK', tfmt(translate(K)), 'tB', tfmt(translate(B)))
        print(f'  CRUX split (proper K): easy(leadK<leadB)={easy}  HARD(==)={hard}')
        print(f'     HARD class olt-false count = {hard_olt_false} (should be 0 if core true)')
        print(f'     predictor P_anc (olt <=> non-ascension): hits={pred_hit} '
              f'UNSOUND(pred-olt-but-false)={pred_sound_bad} '
              f'incomplete(olt-but-not-pred)={pred_miss}')
        for B, K, below, asc in hard_ex[:6]:
            print('       B', mfmt(B), 'K', mfmt(K), 'olt', below, 'ascends', asc)

if __name__ == '__main__':
    main()
