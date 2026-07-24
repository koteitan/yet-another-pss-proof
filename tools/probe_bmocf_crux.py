#!/usr/bin/env python3
"""TASK 5 (sanity) + CRUX (the decisive test).

Core:  for B with (0,0)::B in ST_PS and row1<=1, for every SubBlock K of B,
       olt(translate K)(translate B).
We test the STRONGER and more directly relevant form already model-verified in
the lean project (Gterm_translate_subblock): for every host B in the corpus and
every proper SubBlock K of B, olt(translate K)(translate B).

CRUX: is there a clean well-founded DECREASING measure mu, defined via the
<=_M / <_M^Next structure, such that the SubBlock induction step strictly
decreases mu AND the olt conclusion follows at each step?

We test candidate measures by checking the IMPLICATION we would need for a
structural induction to close:
  for a SubBlock step B -> K (K an immediate takeWhile/dropWhile child of B):
    (i)  mu(K) < mu(B)                       (well-founded descent)
    (ii) the olt conclusion is *reducible*:   does olt(K,B) follow from the
         child relation + IH, i.e. is olt(translate K)(translate B) recoverable
         from olt on the immediate children + a LOCAL fact provable without the
         global core?  We approximate "reducible" by: is there a uniform local
         lemma L(B,K) (depending only on the immediate decomposition, NOT on
         deeper structure) that already forces olt(K,B)?  We test the candidate
         local lemmas the advisor's reframe would need:
           L1: lead(translate K) < lead(translate B)   (strictly smaller head)
           L2: lead K == lead B  ->  the head-1-nested coefficient case
               (this is exactly the residual the lean project says is NON-local)
"""
import sys
sys.path.insert(0, '.')
from fast_pss import oper, diagSeq, Lng, le0, entry
from wfe_explore import translate, olt, maxsub
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt
from probe_bmocf_ancestor import build_next_le, enum_depth
from probe_bmocf_equivA import subblocks

def lead(t): return t[0] if t else -1

# ---- immediate SubBlock children (one takeWhile + one dropWhile step) ----
def immediate_children(B):
    B = list(B)
    if not B: return []
    (x, y) = B[0]; rest = B[1:]
    i = 0
    while i < len(rest) and rest[i][0] > x: i += 1
    kids = []
    if rest[:i]: kids.append(('desc', tuple(rest[:i])))
    if rest[i:]: kids.append(('sib', tuple(rest[i:])))
    return kids

def is_ST_PS_corpus(seen):
    return set(seen)

# ---- candidate measures ----
def mu_len(B): return Lng(B)
def mu_tsize(B):
    t = translate(B)
    def sz(t):
        if t == (): return 0
        return 1 + sz(t[1]) + sz(t[2])
    return sz(t)
def mu_nextchain(B):
    """length of the longest <_M^Next chain in row 0 (depth of row-0 ancestry)."""
    n = Lng(B)
    if n == 0: return 0
    nx, le = build_next_le(tuple(B))
    # longest path in DAG nx[0]
    import functools
    adj = {j: [] for j in range(n)}
    for (a, b) in nx[0]: adj[a].append(b)
    @functools.lru_cache(None)
    def lp(j): return 1 + max((lp(k) for k in adj[j]), default=0)
    return max(lp(j) for j in range(n))

def main():
    for rounds in (5, 6):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        corpus = [M for M in seen if Lng(M) <= 16]
        md = max(seen.values())

        # ---- TASK 5: core sanity -- every proper SubBlock K of B has olt(tK,tB) ----
        core_checked = core_viol = 0; cex = []
        for B in corpus:
            tB = translate(B)
            for K in subblocks(B):
                if not K or K == tuple(B): continue
                tK = translate(K)
                core_checked += 1
                if not olt(tK, tB):
                    core_viol += 1
                    if len(cex) < 5: cex.append((B, K, tK, tB))

        # ---- CRUX (i): measures strictly decrease on immediate children ----
        measures = {'len': mu_len, 'tsize': mu_tsize, 'nextchain': mu_nextchain}
        dec = {k: [0, 0] for k in measures}  # [ok, fail]
        for B in corpus:
            for tag, K in immediate_children(B):
                for name, mu in measures.items():
                    if mu(K) < mu(B): dec[name][0] += 1
                    else: dec[name][1] += 1

        # ---- CRUX (ii): is the olt conclusion LOCALLY reducible? ----
        # For each immediate child step B -> K, classify:
        #   easy  : lead(tK) < lead(tB)            (auto olt -- the local part)
        #   HARD  : lead(tK) == lead(tB)           (the head-1-nested residual)
        # and whether even at equal lead, olt(tK,tB) still holds (the core fact).
        easy = hard = hard_olt_ok = hard_olt_bad = 0
        hex = []
        for B in corpus:
            tB = translate(B)
            for tag, K in immediate_children(B):
                tK = translate(K)
                if lead(tK) < lead(tB):
                    easy += 1
                elif lead(tK) == lead(tB):
                    hard += 1
                    if olt(tK, tB): hard_olt_ok += 1
                    else:
                        hard_olt_bad += 1
                # lead(tK) > lead(tB) cannot happen for genuine subblocks; ignore

        print(f'[closure+{rounds}] maxdepth={md} hosts={len(corpus)}')
        print(f'  TASK5 core: checked={core_checked} violations={core_viol}')
        for B, K, tK, tB in cex[:4]:
            print('    CEX B', mfmt(B), 'K', mfmt(K))
        print('  CRUX(i) measure strict-descent on immediate children:')
        for name in measures:
            ok, fail = dec[name]
            print(f'     mu_{name}: decrease={ok} NON-decrease={fail}')
        print('  CRUX(ii) local reducibility of olt conclusion:')
        print(f'     easy (lead strictly smaller -> auto olt): {easy}')
        print(f'     HARD (equal lead -> needs the core fact): {hard}'
              f'   (of which olt holds={hard_olt_ok}, fails={hard_olt_bad})')

if __name__ == '__main__':
    main()
