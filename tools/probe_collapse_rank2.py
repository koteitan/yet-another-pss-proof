#!/usr/bin/env python3
"""probe_collapse_rank2.py -- the DECISIVE Towsner-mechanism test for door1.

probe_collapse_rank.py established: at every §12 dip step (maxsub INVARIANT), the
structural collapse-rank cr_inv MOVES (UP by the collapse), and the critical
subterm K^{<0}(cur) = the un-collapsed prev sits at a STRICTLY LOWER cr-stratum.
cr is olt-INDEPENDENT (check A passes).

But EVERY prior route died because the WITHIN-stratum recovery re-introduced the
SAME global non-local fact (maxsub-strat, SubBlock-deriv, dyn-oper all re-entered
the wall at the next level).  The decisive question for door1: does the
cr-stratification + Towsner accessibility (Acc_n = WF part of M_n; Lemma 3.10/3.11
ϑ closes Acc_n) genuinely REDUCE olt(tK,tB) to (lower-cr critical subterms, IH) +
(cr-FLAT monotone part), WITHOUT the within-cr-stratum part re-requiring the
global fact?

We test the Towsner accessibility REDUCTION directly on the dip-recover witnesses:

 TEST 1 (the reduction is GENUINE):  the comparison olt(tK, tB) on a dip-recover
   witness should decompose as: tB = (a, body, sib) where the collapse content is
   captured by cr.  We verify that olt(tK,tB) holds BY one of:
     (R1) cr(tK) < cr(tB): tK is at a strictly lower collapse-stratum than tB
          => Towsner Lemma 3.8 (m<n, alpha in Acc_m, beta in Acc_n => combine) /
          the lower stratum is accessible by IH.  [the dip-recover case]
     (R2) cr(tK) == cr(tB) AND the comparison is decided WITHIN-stratum by a
          cr-FLAT path = the GREEN RIGHT-grow monotone (ascending-copy) part.
   Tabulate: of the NEEDED witnesses, how many fall in R1 (lower-stratum, IH
   handles) vs R2 (cr-flat, GREEN handles) vs NEITHER (the route's residual).
   If NEITHER==0 => the cr-stratification PARTITIONS the obligation cleanly into
   {IH-covered, GREEN-covered} => door1 absorbs dip-recover.  If NEITHER>0 =>
   there is a within-stratum residual NOT covered by lower-cr-IH nor GREEN-flat =>
   report it (the route's true remaining content).

 TEST 2 (WELL-FOUNDEDNESS / base, check ii): cr is a non-neg integer, drops
   strictly into critical subterms (K^{<0} arg has cr-1).  cr=0 <=> NO collapse
   inversion <=> the term's olt-order is the maxsub-monotone PrSS/eps_0 order =
   wf_olt0 base.  We verify cr=0 terms are exactly handled by wf_olt0 (the L_0
   base): for cr=0 witnesses, is olt decided by maxsub/lead alone (no collapse)?

 TEST 3 (within-stratum recovery is cr-FLAT monotone = GREEN): for the RECOVERY
   part of a dip-recover path (after the dip, building back up), are those steps
   cr-FLAT (cr constant) AND olt-monotone (the RIGHT-grow direction)?  i.e. is
   recovery genuinely the GREEN core_i0/i1 ascending part within a fixed stratum?
"""
import sys
sys.path.insert(0, '.')
from fast_pss import Lng
from wfe_explore import translate, olt, maxsub
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt
from probe_bmocf_ancestor import enum_depth

Z = ()
def head_sub(t): return t[0] if t else -1
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

def cr_inv(t):
    if t == (): return 0
    a, b, c = t
    inv = 1 if (b != () and maxsub(b) > a) else 0
    return max(inv + cr_inv(b), cr_inv(c))

def main():
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 30, rounds)
        hosts = [M for M in seen if Lng(M) <= 20 and all(c[1] <= 1 for c in M)
                 and M and M[0] == (0, 0)]
        md = max(seen.values())

        # TEST 1 reduction partition (over ALL needed witnesses, dip & non-dip)
        needed = 0
        R1 = R2 = NEITHER = 0
        neither_ex = []
        # dip-recover subset specifically
        needed_dip = 0; dip_R1 = dip_R2 = dip_NEITHER = 0
        # TEST 2: cr=0 base decided by maxsub/lead-only
        cr0_wit = cr0_maxsub_decides = 0
        # TEST 3: recovery steps cr-flat & olt-monotone
        rec_steps = rec_flat_mono = 0

        for B0 in hosts:
            B = tuple(B0[1:]); tB = translate(B)
            if tB == Z: continue
            n = len(B); G0 = set(Gterm(0, tB))
            crB = cr_inv(tB)
            for x in G0:
                if x == tB: continue
                ij = find_infix(B, x)
                if ij is None: continue
                i, j = ij
                tK = translate(tuple(B[i:j]))
                if not olt(tK, tB):
                    continue
                needed += 1
                crK = cr_inv(tK)
                is_dip = False
                # detect dip on left path
                lo = i; prev = translate(tuple(B[lo:n]))
                while lo > 0:
                    lo -= 1; cur = translate(tuple(B[lo:n]))
                    if cur == Z or cur == prev: prev = cur; continue
                    if not olt(prev, cur): is_dip = True
                    prev = cur
                # TEST 1 classification
                if crK < crB:
                    R1 += 1; cls = 'R1'
                elif crK == crB:
                    # cr-flat: decided within stratum. Is it the GREEN flat-monotone?
                    # proxy: tK reachable from tB by a cr-flat olt-monotone descent
                    # (i.e. lead/maxsub-decided, no collapse between).  We test the
                    # simplest sufficient flat condition: lead(tK) and the spine are
                    # maxsub-monotone-comparable = olt decided without a p0-wrap gap.
                    # Operationally: crK==crB AND olt(tK,tB) AND no dip on the path.
                    if not is_dip:
                        R2 += 1; cls = 'R2'
                    else:
                        NEITHER += 1; cls = 'NEITHER'
                        if len(neither_ex) < 6:
                            neither_ex.append((B, tK, crK, crB))
                else:  # crK > crB : witness at HIGHER stratum than B (shouldn't dominate?)
                    NEITHER += 1; cls = 'NEITHER'
                    if len(neither_ex) < 6:
                        neither_ex.append((B, tK, crK, crB))
                if is_dip:
                    needed_dip += 1
                    if cls == 'R1': dip_R1 += 1
                    elif cls == 'R2': dip_R2 += 1
                    else: dip_NEITHER += 1
                # TEST 2 base
                if crK == 0:
                    cr0_wit += 1
                    # cr=0 => olt vs tB decided by lead/maxsub (no collapse).
                    # sufficient proxy: lead(tK) < lead(tB) OR maxsub(tK)<maxsub(tB)
                    if lead(tK) < lead(tB) or maxsub(tK) < maxsub(tB) \
                       or (lead(tK)==lead(tB) and crB==0):
                        cr0_maxsub_decides += 1
                # TEST 3 recovery: after dip, the build-up steps
                if is_dip:
                    lo = i; prev = translate(tuple(B[lo:n])); seen_dip = False
                    while lo > 0:
                        lo -= 1; cur = translate(tuple(B[lo:n]))
                        if cur == Z or cur == prev: prev = cur; continue
                        if not olt(prev, cur):
                            seen_dip = True
                        elif seen_dip:
                            # a recovery (up) step after a dip
                            rec_steps += 1
                            if cr_inv(cur) == cr_inv(prev) and olt(prev, cur):
                                rec_flat_mono += 1
                        prev = cur

        print(f'[closure+{rounds}] maxdepth={md} hosts={len(hosts)} needed-witnesses={needed}')
        print(f'  TEST1 cr-reduction partition:')
        print(f'     R1 (crK<crB, IH/lower-stratum) = {R1}')
        print(f'     R2 (crK==crB cr-flat, GREEN)    = {R2}')
        print(f'     NEITHER (within-stratum residual)= {NEITHER}')
        for B,tK,ck,cb in neither_ex[:4]:
            print(f'        NEITHER B {mfmt(B)} tK {tfmt(tK)[:24]} crK={ck} crB={cb}')
        print(f'     [dip-recover subset: needed_dip={needed_dip} -> R1={dip_R1} R2={dip_R2} NEITHER={dip_NEITHER}]')
        print(f'  TEST2 cr=0 base: cr0-witnesses={cr0_wit} maxsub/lead-decides={cr0_maxsub_decides}')
        print(f'  TEST3 recovery steps: total={rec_steps} cr-FLAT&olt-monotone={rec_flat_mono}')

if __name__ == '__main__':
    main()
