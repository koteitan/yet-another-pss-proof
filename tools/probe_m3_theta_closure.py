#!/usr/bin/env python3
"""probe_m3_theta_closure.py -- THE decisive de-risk: does Towsner's ϑ-closure
(Lemma 3.10) supply head-1+ arg accessibility via the K^{<0} critical-subterm
MEMBERSHIP condition (forest-fact-FREE), or does it ALSO need the bare per-arg
domination olt(translate K)(translate A) = the forest fact?

TOWSNER 3.10 MECHANISM (PDF p.10): to show ϑ(α) ∈ Acc_n, prove every γ < ϑα with
γ ∈ M_n is in Acc_n, by structural induction on γ.  The COLLAPSE case γ = ϑβ:
  - find δ with β = δ^{≥0}_{-1}; show δ ∈ M_n by: for each critical subterm
    δ' ∈ K^{<0}δ, (δ')* ∈ Acc_m -- SUPPLIED BY γ ∈ M_n (the membership condition).
  - then γ = ϑδ ∈ Acc_n by the IH on α.
The accessibility of the collapse predecessor flows through the K^{<0} MEMBERSHIP
(critical subterms in lower Acc), NOT a bare domination.

TERM-SIDE TRANSLATION.  My naive M3 recursed into the arg A of P 0 A S as a fresh
Acc obligation, hitting olt(K,A) for head-1+ A (=H0clause).  Towsner's actual
mechanism: when a PREDECESSOR v = P 0 A' S' <o P 0 A S arrives, and A' (head-1+)
is a collapse node, its accessibility comes from v ∈ M_n -- i.e. A's critical
subterms (cr_inv-lower, IH) -- NOT from proving olt(K, A') directly.

THE DECISIVE TEST.  A predecessor v ∈ M_n of t (both head-0 NF, in Mn n).  v's
summands are P 0 A'_i S'_i.  The arg A'_i (head-1+).  Towsner says A'_i's
accessibility is supplied because A'_i's critical subterms are at cr < cr(A'_i)
(lower stratum, IH) AND A'_i ∈ M_n (membership).  CHECK whether this membership-
based accessibility is INDEPENDENT of the bare forest fact:

(T1) For every head-1+ arg A' that arises as the arg of a summand of an oltMn-n
     predecessor v of a head-0 NF term t: is A' ITSELF in Mn n (cnf, cr<=n, crit
     subterms at cr < n via cr_inv_arg_lt_of_inv)?  [if yes: A' ∈ M_n, membership
     holds, accessibility CAN flow through the ladder]

(T2) THE CRUX -- does A''s accessibility (as a head-1+ M_n term) require, at any
     point, a comparison olt(x, A') for a head-1+ x that is NOT decided by
     (cr-drop into critical subterm) ∨ (DM on summands) ∨ (head/lead structure)?
     i.e. enumerate the oltMn-n predecessors w of A' (w <o A', w ∈ Mn n) and check
     each splits as:
       - cr(w) < cr(A')           [lower stratum, IH -- forest-fact-FREE]
       - cr(w) = cr(A'), arg-drop  [DM/arg-induction within stratum]
       - cr(w) = cr(A'), SAME-lead arg-drop handled
       - OTHERWISE: a same-cr comparison NOT reducible = the FOREST FACT.
     If OTHERWISE == 0: the ϑ-closure closes head-1+ args via cr-drop IH +
     membership, FOREST-FACT-FREE => door1 CLOSES.
     If OTHERWISE > 0: even the faithful ϑ-closure needs the forest fact.

CRITICAL SOUNDNESS: the head-1+ arg A' = P a' b' c' (a'>=1).  Its oltMn-n preds w
= P a'' ... .  By olt, a'' <= a'.  If a'' < a': SUBSCRIPT DROP among args (these
exist!).  Is the subscript-drop pred w at LOWER cr (=> IH covers it) or same cr
(=> forest fact)?  THIS is the exact question.
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import translate, olt, maxsub
from probe_bmocf_ancestor import enum_depth

Z = ()
def lead(t): return t[0] if t != Z else 0
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
        if b != () and maxsub(b) > a: out.append(b)
        rec(b); rec(c)
    rec(t); return out
def summands(t):
    if t == (): return []
    a, b, c = t
    return [(a, b, ())] + summands(c)
def sargs(t):
    if t == (): return []
    a, b, c = t
    return [b] + sargs(c)
def in_Mn(s, n):
    if cr_inv(s) > n: return False
    return all(cr_inv(bb) < n for bb in critSub(s))

def collect_args(NF):
    """all head-1+ arg subterms arising in NF terms (the ϑ-closure universe)."""
    args = set()
    def rec(t):
        if t == Z: return
        a, b, c = t
        if b != Z: args.add(b)
        rec(b); rec(c)
    for t in NF: rec(t)
    return [a for a in args if lead(a) >= 1]

def main():
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 30, rounds)
        NF = set(translate(M) for M in seen); NF.discard(Z)
        h1args = collect_args(NF)
        # universe of all subterms (potential preds w of an arg A')
        allsub = set()
        def rec(t):
            if t == Z: return
            allsub.add(t); a, b, c = t; rec(b); rec(c)
        for t in NF: rec(t)
        allsub = list(allsub)
        md = max(seen.values())

        # For each head-1+ arg A', n=cr(A'), examine its oltMn-n preds w (in Mn n).
        lower = argdrop_same = subdrop_lowercr = subdrop_samecr = sibdrop = other = 0
        ex = []
        # bound the work: sample
        for A in h1args:
            n = cr_inv(A)
            a, B, S = A
            for w in allsub:
                if w == A or not olt(w, A): continue
                if not in_Mn(w, n): continue   # only oltMn-n preds
                cw = cr_inv(w)
                if cw < n:
                    lower += 1; continue
                # same cr (cw == n). split by olt mechanism vs A = P a B S
                wa = lead(w)
                if w[2] == Z and wa == a and olt(w[1], B):
                    argdrop_same += 1
                elif wa < a:
                    # SUBSCRIPT DROP among args
                    if cw < n: subdrop_lowercr += 1
                    else:
                        subdrop_samecr += 1
                        if len(ex) < 6:
                            from wfe_explore import fmt as tf
                            ex.append((tf(A)[:24], tf(w)[:24], n, cw, a, wa))
                elif wa == a:
                    sibdrop += 1
                else:
                    other += 1

        print(f'[closure+{rounds}] maxdepth={md} head-1+ args={len(h1args)}')
        print(f'  oltMn-n preds of head-1+ args:')
        print(f'    lower-cr (IH, forest-FREE)        = {lower}')
        print(f'    same-cr argdrop (DM/arg-ind)      = {argdrop_same}')
        print(f'    same-cr sibdrop (a\'\'=a)            = {sibdrop}')
        print(f'    SUBDROP same-cr (FOREST FACT?)    = {subdrop_samecr}')
        print(f'    subdrop lower-cr (IH)             = {subdrop_lowercr}')
        print(f'    other                             = {other}')
        for A, w, n, cw, a, wa in ex[:6]:
            print(f'      SUBDROP A={A} w={w} cr={n}/{cw} lead {a}>{wa}')

if __name__ == '__main__':
    main()
