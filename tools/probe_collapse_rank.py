#!/usr/bin/env python3
"""probe_collapse_rank.py -- de-risk architect §13.3(3): does a Towsner FC/G
COLLAPSE-RANK stratification (NOT maxsub) absorb the §12 dip-recover?

BASELINE (the test set): the §12 dip-recover witnesses -- canonical Gterm-0
witnesses K of real translate B (row1<=1) where olt(tK,tB) is TRUE at the
endpoint but olt DIPS at an intermediate LEFT-grow node-insertion, and maxsub is
INVARIANT across the dip (maxsub(p0(x))=maxsub(x)).  230/566/1589 @+5/+6/+7.

TOWSNER FC/G (paper §3.1-3.2, pp.9-11):
 - G(alpha) = GROUND = lowest cardinality appearing free (base level).
 - FC(alpha) = top-level formal cardinality.
 - K^{<0}alpha = critical subterms beta with FC(beta) < FC(alpha) (collapse args);
   for such beta, FC(beta)<FC(alpha) AND G(beta*) > G(alpha) (note 9).
 - M_n / Acc_n: M_n = terms with FC=0, G>=-n, and {beta* | beta in K^{<0}alpha}
   subset of union_{i<n} Acc_i.  Stratum index n = bounds the GROUND = collapse
   nesting depth; critical subterms must be accessible at LOWER strata.

PSS MAPPING (translate term t=(a,b,c) = p_a(b)+c, subscript a = row1, 2-row so
cardinalities in {0,1}; p_0 = the psi_0 collapse).
 - The collapse inversion = a node p_a whose ARGUMENT subtree contains a subscript
   STRICTLY GREATER than a (the arg "rises above" the head = collapse).  Lead-wrap
   p0(p1(x)): root a=0, arg p1 has subscript 1>0 = ONE inversion.  p1(x): none.
 - candidate STRUCTURAL collapse-ranks (all olt-INDEPENDENT, computed from tree):

   cr_inv(t)   = max over root-to-leaf ARG-spine paths of the number of
                 "collapse inversions" (node whose subscript < some subscript
                 strictly deeper in its arg subtree).  = depth of psi_0-collapse
                 nesting.  (Towsner G-rank analog: deeper collapse = higher rank.)
   cr_ground(t)= analog of G: the MINIMUM head-subscript encountered along the
                 arg-spine BELOW the first point where a higher subscript appears
                 (the "ground" the term sits on).  We test (Towsner: lower ground
                 = the collapse pushed cardinality down).
   cr_kdepth(t)= K^{<0} critical-subterm nesting depth: recursively, 1 + max
                 cr_kdepth over critical sub-args (args whose max-subscript >
                 head-subscript), else 0 at leaves/no-inversion.

DECISIVE CHECKS on the dip-recover witnesses (prev -> cur where olt DIPS,
maxsub flat):
 (i)  does cr go DOWN at the dipped intermediate (strictly), where maxsub is equal?
      i.e. cr(cur) < cr(prev) when olt(prev,cur) is FALSE (dip) & maxsub equal?
      [the "collapse-rank distinguishes the dip" claim]  -- but ADVERSARIAL: cur
      is the BIGGER tree toward B; a collapse makes cur a p0-wrap of prev, so
      cur has MORE inversion depth, cr(cur) > cr(prev)?  We report the actual
      direction.
 (ii) WELL-FOUNDED + bottoms out: cr>=0 integer, and cr=0 <=> no collapse
      inversion <=> the term is a pure ascending (PrSS/L_0/eps_0) form?  test
      cr=0 coincides with "maxsub-monotone single-spine" = wf_olt0 base.
 (iii)recovery WITHIN-stratum: along the FULL K->B path, is cr bounded by the
      stratum of B (cr never exceeds cr(tB))?  & is the dip a DROP to a lower
      cr-stratum (so the distinguished-set IH at lower cr covers it)?
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

# ---- structural collapse-rank candidates (olt-INDEPENDENT) ----
def cr_inv(t):
    """max # of collapse inversions along any arg/sib path.  A node (a,b,c) is a
    collapse-inversion if maxsub(b) > a (the arg rises above the head).  Rank =
    deepest nesting of such inversions along the ARG direction (the collapse
    nesting depth)."""
    if t == (): return 0
    a, b, c = t
    inv_here = 1 if (b != () and maxsub(b) > a) else 0
    return max(inv_here + cr_inv(b), cr_inv(c))

def cr_kdepth(t):
    """K^{<0} critical-subterm nesting depth: 1 + max kdepth over critical args
    (arg whose maxsub > head subscript), 0 if none."""
    if t == (): return 0
    a, b, c = t
    d_arg = 0
    if b != () and maxsub(b) > a:
        d_arg = 1 + cr_kdepth(b)
    else:
        d_arg = cr_kdepth(b)
    return max(d_arg, cr_kdepth(c))

def main():
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 30, rounds)
        hosts = [M for M in seen if Lng(M) <= 20 and all(c[1] <= 1 for c in M)
                 and M and M[0] == (0, 0)]
        md = max(seen.values())

        # collect dip-recover witnesses & their dip steps
        n_witness_dip = 0
        # (i) at the dip step: cr direction (down/up/eq) while maxsub equal
        dip_steps = 0
        dip_maxsub_eq = 0
        cr_inv_down = cr_inv_up = cr_inv_eq = 0
        cr_kd_down = cr_kd_up = cr_kd_eq = 0
        # (iii) full-path: cr bounded by cr(tB) (within stratum)?
        path_within = path_total = 0
        # (ii) cr=0 <=> maxsub-monotone single spine (eps_0 base)
        cr0_chk = cr0_match = 0

        for B0 in hosts:
            B = tuple(B0[1:]); tB = translate(B)
            if tB == Z: continue
            n = len(B); G0 = set(Gterm(0, tB))
            crB_inv = cr_inv(tB); crB_kd = cr_kdepth(tB)
            for x in G0:
                if x == tB: continue
                ij = find_infix(B, x)
                if ij is None: continue
                i, j = ij
                tK = translate(tuple(B[i:j]))
                if not olt(tK, tB):
                    continue   # only NEEDED witnesses (endpoint olt true)
                # walk LEFT path, detect dip steps
                lo = i; prev = translate(tuple(B[lo:n]))
                had_dip = False
                within = True
                while lo > 0:
                    lo -= 1; cur = translate(tuple(B[lo:n]))
                    if cur == Z or cur == prev: prev = cur; continue
                    # (iii) within-stratum check on cur
                    path_total += 1
                    if cr_inv(cur) <= crB_inv: path_within += 1
                    # dip step?
                    if not olt(prev, cur):
                        had_dip = True
                        dip_steps += 1
                        ms_eq = (maxsub(prev) == maxsub(cur))
                        if ms_eq: dip_maxsub_eq += 1
                        # (i) cr direction: prev=K-side(smaller tree), cur=B-side
                        # (bigger tree, the p0-wrap).  Does cr DISTINGUISH? we want
                        # cr to MOVE (not be invariant like maxsub).
                        ci_p, ci_c = cr_inv(prev), cr_inv(cur)
                        if ci_c < ci_p: cr_inv_down += 1
                        elif ci_c > ci_p: cr_inv_up += 1
                        else: cr_inv_eq += 1
                        ck_p, ck_c = cr_kdepth(prev), cr_kdepth(cur)
                        if ck_c < ck_p: cr_kd_down += 1
                        elif ck_c > ck_p: cr_kd_up += 1
                        else: cr_kd_eq += 1
                    prev = cur
                if had_dip:
                    n_witness_dip += 1
                    if within: path_within_full = True

        # (ii) cr=0 base characterization over all subterms in corpus
        for B0 in hosts:
            B = tuple(B0[1:]); tB = translate(B)
            if tB == Z: continue
            stack = [tB]
            while stack:
                t = stack.pop()
                if t == (): continue
                a, b, c = t
                cr0_chk += 1
                is_cr0 = (cr_inv(t) == 0)
                # eps_0/PrSS base proxy: NO collapse inversion anywhere = every
                # node's subscript >= maxsub of its arg (ascending/flat spine)
                ascending = is_cr0
                # match: cr=0 iff ascending (definitionally same here, sanity)
                if is_cr0 == ascending: cr0_match += 1
                stack.append(b); stack.append(c)

        print(f'[closure+{rounds}] maxdepth={md} hosts={len(hosts)}')
        print(f'  dip-recover witnesses (needed, olt dips intermediate): {n_witness_dip}')
        print(f'  (i) DIP steps={dip_steps}  (maxsub-equal at dip: {dip_maxsub_eq})')
        print(f'      cr_inv  at dip:  DOWN={cr_inv_down}  UP={cr_inv_up}  EQ(invariant!)={cr_inv_eq}')
        print(f'      cr_kdep at dip:  DOWN={cr_kd_down}  UP={cr_kd_up}  EQ(invariant!)={cr_kd_eq}')
        print(f'  (iii) full-path cr_inv(cur)<=cr_inv(tB) within-stratum: {path_within}/{path_total}')

if __name__ == '__main__':
    main()
