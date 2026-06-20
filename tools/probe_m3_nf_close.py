#!/usr/bin/env python3
"""probe_m3_nf_close.py -- DECISIVE de-risk of door1 M3 (Towsner Lemma 3.10) on
NF, BEFORE the heavy forest coupling.

The M3 singleton/collapse step `P a b Z in Accn n from Acc b` walls on the
same-stratum subscript-drop predecessor: `P a' b c <o P a b c` with a'<a, same
cr_inv, same maxsub -- excluded only by NF forest-reachability (the rounds-1-9
core).  Cex for ARBITRARY cnf: P0(P3(0)) <o P1(P3(0)), both cr=1 maxsub=3.

STEP 1 questions (all @+5/+6/+7, faithful NF = translate-of-ST_PS):

(Q1) NF-EXCLUSION: for an NF single principal P a b Z, do its `a'<a` same-cr
     olt-predecessors P a' b' Z that are THEMSELVES NF actually NOT exist?
     If NF genuinely excludes them, the bare cnf cex is off-NF and M3-on-NF can
     proceed.  Tabulate the count of NF same-cr a'<a predecessors.

(Q2) IS THE EXCLUSION THE BARE FOREST FACT, OR THE K^{<0} CONDITION?
     Towsner's M_n requires every critical subterm beta in K^{<0}(alpha) to be
     accessible at a LOWER stratum.  A same-cr a'<a predecessor P a' b' Z of
     P a b Z (cr=n): is its EXCLUSION-from-Mn derivable because one of ITS
     critical subterms sits at cr >= n (so it's NOT in Mn n)?  i.e. does the
     K^{<0} membership condition ALREADY exclude the same-cr a'<a NF predecessor
     -- WITHOUT invoking the bare forest fact?
     -> Compare: (a) does NF exclude it [forest fact], vs (b) does the Mn
        critical-subterm condition exclude it [structural, derivable from
        cr_inv_critSub_lt + the IH].  If (b) excludes EVERYTHING (a) does, then
        the Towsner K^{<0} IH closes NF-restricted M3 WITHOUT the bare forest
        fact.  If there remain predecessors that NF excludes but Mn-membership
        does NOT, those are the irreducible bare-forest-fact residual.

(Q3) THE ACTUAL ACCESSIBILITY RESIDUAL: over the NF witnesses, classify every
     olt-predecessor v (in NF) of an NF single principal t into:
       LOWER : cr(v) < cr(t)            [Accn m, m<n -- lower-stratum IH]
       MN_EXCL: cr(v) >= cr(t) but v not-in-Mn(cr t) by the critical-subterm
                condition (some critSub(v) at cr >= cr(t))  [K^{<0} IH excludes]
       FOREST: cr(v) >= cr(t), v IS in Mn(cr t) structurally, but olt(v,t) is the
                bare forest-position predecessor (same-cr in-Mn pred) [the wall]
     If FOREST == 0 over NF witnesses => Towsner K^{<0} IH closes NF M3 (BUILD).
     If FOREST > 0 => those are the bare forest fact; door1 M3 = the wall (report
     convergence).
"""
import sys
sys.path.insert(0, '.')
from fast_pss import Lng
from wfe_explore import translate, olt, maxsub
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt
from probe_bmocf_ancestor import enum_depth

Z = ()

def cr_inv(t):
    if t == (): return 0
    a, b, c = t
    inv = 1 if (b != () and maxsub(b) > a) else 0
    return max(inv + cr_inv(b), cr_inv(c))

def critSub(t):
    """K^{<0}: args b at collapse sites P a b c with maxsub b > a (matches Lean)."""
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
    """Mn membership (term-side, with the IH that strata < n are 'accessible'):
    cnf (all NF are cnf) + cr_inv s <= n + every critical subterm at cr < n.
    The last conjunct = the K^{<0} ⊆ ⋃_{i<n} Acc_i condition under the IH that
    a term is in Acc_{cr} iff its own critical subterms are lower (recursively).
    We use the SOUND proxy: critSub(s) all have cr_inv < n (the AccBelow part)."""
    if cr_inv(s) > n:
        return False
    return all(cr_inv(b) < n for b in critSub(s))

def main():
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 30, rounds)
        NF = set(translate(M) for M in seen)
        NF.discard(Z)
        NFl = list(NF)
        md = max(seen.values())

        # NF single principals P a b Z (the singleton-step targets)
        sing = [t for t in NF if t[2] == Z and t != Z]

        # (Q1) NF same-cr a'<a predecessors that are NF
        q1_nf_samecr_adrop = 0
        # (Q3) classify ALL NF olt-predecessors of NF single principals
        LOWER = MN_EXCL = FOREST = 0
        forest_ex = []
        # restrict to single-principal predecessors (summand granularity, the
        # actual Mn/DM decomposition unit)
        for t in sing:
            n = cr_inv(t)
            a, b, _ = t
            for v in NFl:
                if v == t or not olt(v, t):
                    continue
                # decompose v into summands (each P a' b' Z), the DM units
                for s in summands(v):
                    sa, sb, _ = s
                    cs = cr_inv(s)
                    # (Q1): same-cr, a'<a, this summand is a single principal in NF?
                    if cs == n and sa < a and s in NF:
                        q1_nf_samecr_adrop += 1
                    # (Q3) classification of this predecessor-summand
                    if cs < n:
                        LOWER += 1
                    elif not in_Mn(s, n):
                        MN_EXCL += 1
                    else:
                        # cr>=n AND in Mn n structurally: the bare forest residual
                        FOREST += 1
                        if len(forest_ex) < 6:
                            forest_ex.append((t, s, n, cs))

        print(f'[closure+{rounds}] maxdepth={md} NF={len(NF)} singles={len(sing)}')
        print(f'  (Q1) NF same-cr a\'<a pred-summands (forest must exclude): '
              f'{q1_nf_samecr_adrop}')
        print(f'  (Q3) NF pred-summand classification of NF single principals:')
        print(f'       LOWER  (cr<n, lower-stratum IH)           = {LOWER}')
        print(f'       MN_EXCL(cr>=n but K^<0 excludes from Mn)  = {MN_EXCL}')
        print(f'       FOREST (cr>=n, in Mn n: the bare wall)    = {FOREST}')
        for t, s, n, cs in forest_ex[:6]:
            print(f'         FOREST t={tfmt(t)[:30]} pred={tfmt(s)[:30]} '
                  f'n={n} cr(pred)={cs}')

if __name__ == '__main__':
    main()
