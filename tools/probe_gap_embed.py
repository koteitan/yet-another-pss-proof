#!/usr/bin/env python3
"""probe_gap_embed.py -- de-risk the architect's §11 carrier FIX: replace flat
<=_M sequence-embedding with a Friedman GAP-EMBEDDING of the translate TREE
p_a(b)+c, where a GAP CONDITION on inserted nodes' subscripts is meant to encode
the head-lead polarity that flat <=_M missed (the §10 lead-wrap p1 |-> p0(p1)).

THE decisive §11.5 test, on the §10 LEFT-grow lead-wrap cases:
  partition the LEFT-grow steps by whether the inserted node satisfies a GAP
  CONDITION; check (i) gap-SATISFYING => olt 0-viol, (ii) gap-VIOLATING are the
  ones to exclude, (iii) the NEEDED canonical witnesses themselves gap-satisfy.

MANDATORY soundness:
 A. NON-CIRCULAR: the gap condition must be a STRUCTURAL subscript predicate
    checkable WITHOUT computing olt.  We state several explicit candidate gap
    predicates and confirm each is olt-independent.
 B. LOAD-BEARING + needed witnesses satisfy it: for the canonical Gterm-0
    witnesses K of real translate B where we NEED olt(tK,tB), does the gap
    embedding K <=_e B HOLD (gap condition satisfied)?  If NOT, the fix is hollow.

----------------------------------------------------------------------------
TREE MODEL.  translate term t = (a,b,c) = node `p_a` with ARG-subtree b and
SIBLING-forest c (the `+c`).  Reading as a TREE-with-labels: along the ARG spine
we have a path of nodes labelled by their subscripts a0,a1,...; siblings branch.
olt(s,t) compares subscripts first (a<e decides), so the head subscript is the
dominant label.

A LEFT-grow step prev -> cur inserts a NEW ROOT node `p_{a'}` ABOVE the old tree:
  prev = T,  cur = (a', T, c')   [the inserted column's row1 = a', arg = old T].
This is exactly "insert a node on the top edge" = the tree embedding prev ↪ cur
(prev is the arg-subtree of cur).  The inserted node label = a' = cur.head.subscript.
The "gap" it sits in: ABOVE = nothing (it's the new root) / the virtual +inf;
BELOW = the old root label = prev.head.subscript =: a_below.

GAP CONDITIONS tested (all structural, olt-free):
  GC_below  : a' >= a_below            (inserted label >= label just below it)
  GC_strict : a' >  a_below
  GC_le     : a' <= a_below            (Friedman <=-gap, the OTHER polarity)
  GC_eqabove: a' >= (label of the node the gap is 'under' in B) -- Buchholz gap:
              the inserted node's subscript >= the subscript at the TOP of the gap
              (the enclosing context's head in the full B).
We compute, for each LEFT-grow step, a' and a_below and the enclosing-context head,
then test which GC predicts olt(prev,cur) [note: cur is the BIGGER tree toward B,
olt(prev,cur) is the carrier we need].
"""
import sys
sys.path.insert(0, '.')
from fast_pss import Lng
from wfe_explore import translate, olt
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt
from probe_bmocf_ancestor import enum_depth

Z = ()
def head_sub(t): return t[0] if t else -1   # subscript a of node p_a

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

        # accumulate over LEFT-grow steps only (the §10 314/776/2265 wall)
        # for each candidate gap condition: confusion vs olt(prev,cur)
        GCs = ['GC_below', 'GC_strict', 'GC_le', 'GC_eqctx']
        # counts: sat&olt, sat&!olt, !sat&olt, !sat&!olt
        conf = {g: [0,0,0,0] for g in GCs}
        left_steps = 0
        for B0 in hosts:
            B = tuple(B0[1:]); tB = translate(B)
            if tB == Z: continue
            n = len(B); G0 = set(Gterm(0, tB))
            for x in G0:
                if x == tB: continue
                ij = find_infix(B, x)
                if ij is None: continue
                i, j = ij
                # LEFT-grow: from [i:n] prepend cols down to [0:n]
                lo = i; prev = translate(tuple(B[lo:n]))
                while lo > 0:
                    lo -= 1
                    cur = translate(tuple(B[lo:n]))
                    if cur == Z or cur == prev:
                        prev = cur; continue
                    left_steps += 1
                    aprime = head_sub(cur)         # inserted (new root) label
                    a_below = head_sub(prev)        # label just below the gap
                    # Buchholz "enclosing context" = head subscript of the full B
                    a_ctx = head_sub(tB)
                    ol = olt(prev, cur)
                    preds = {
                        'GC_below': aprime >= a_below,
                        'GC_strict': aprime > a_below,
                        'GC_le': aprime <= a_below,
                        'GC_eqctx': aprime >= a_ctx,
                    }
                    for g in GCs:
                        sat = preds[g]
                        if sat and ol: conf[g][0]+=1
                        elif sat and not ol: conf[g][1]+=1
                        elif (not sat) and ol: conf[g][2]+=1
                        else: conf[g][3]+=1
                    prev = cur
        print(f'[closure+{rounds}] maxdepth={md} hosts={len(hosts)} LEFT-grow steps={left_steps}')
        print(f'   (carrier = olt(prev,cur); prev=K-side, cur=B-side bigger tree)')
        for g in GCs:
            s_ol, s_no, ns_ol, ns_no = conf[g]
            # IDEAL gap condition: sat<=>olt, i.e. s_no==0 (no sat-but-not-olt:
            # we don't keep a bad embedding) AND ns_ol small (we don't drop needed ones)
            print(f'   {g:9s}: sat&olt={s_ol:5d}  sat&NOTolt={s_no:5d}  '
                  f'NOTsat&olt={ns_ol:5d}  NOTsat&NOTolt={ns_no:5d}')

if __name__ == '__main__':
    main()
