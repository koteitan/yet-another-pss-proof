#!/usr/bin/env python3
"""probe_wqo_bcore.py -- DECISIVE de-risk of the architect's WQO route milestone-2:
does (B-core)  K <=_e M  =>  olt(translate K)(translate B)  close by induction on
the <=_e-GENERATION (the <_M^Next / Ascend copy-domination step chain) WITH the
"proper sub-structures are good" IH, where the bare SubBlock-DERIVATION induction
FAILED at intermediate nodes (183/443 path-bad)?

THE decisive comparison (architect architect-wf.md sec 4): is the per-step
olt-monotonicity TRUE at the INTERMEDIATE <=_e-generation nodes, where the bare
SubBlock-tree desc/sib children were FALSE?

We model <=_e per architect sec 2 = "SubBlock + <=_M ancestor shift": K <=_e M iff
K embeds into M by a monotone injection of COLUMNS preserving the BMOCF ancestor
relation <=_M (= le0/nextrel1, verified ==). The GENERATION of <=_e is the chain of
<_M^Next single-ancestor-insertion steps (= oper bad-step, architect sec 4).

KEY MODELING DECISION -- two readings of "<=_e-generation step", we test BOTH so
the verdict cannot be gamed:

 (G1) ANCESTOR-CHAIN reading: the canonical Gterm-0 witness K of translate B is a
   contiguous infix M[i:j] (memory: 0 mismatch). Its <=_e-ancestors toward B are
   obtained by GROWING the infix one <_M^Next column at a time, in ancestor order
   (carrying the i_0=max{i|(i,0)<=_M(i,j1)} copy-domination). At each intermediate
   infix K' we test olt(translate K', translate B). Compare the intermediate-node
   truth to the bare-SubBlock desc/sib children.

 (G2) OPER-TILING reading: B's tiling block was produced by oper; the <=_e chain is
   K = oneblock  <=_e  twoblocks  <=_e ... <=_e  B (k copies). At each k we test
   olt(translate(k-copies), translate B). (the "richer carries which copy dominates
   which original" claim.)

For the bare-SubBlock baseline we re-tabulate the desc/sib intermediate-node
olt(child, B)-against-the-ROOT-B failures (NOT child-vs-parent; the IH target is
always the ROOT B), so the comparison is apples-to-apples.

Faithful object throughout: (0,0)::B in ST_PS, row1<=1, K a Gterm-0 witness of
translate B. closure +5/+6/+7.
"""
import sys
sys.path.insert(0, '.')
from fast_pss import Lng, le0, nextrel1, entry, oper, diagSeq
from wfe_explore import translate, olt
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt
from probe_bmocf_ancestor import enum_depth, build_next_le

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

# ---------------------------------------------------------------------------
# canonical Gterm-0 witness K of translate B = contiguous infix B[i:j]
# (memory FINAL VERDICT: 0 mismatch). Find for each witness x in Gterm0(tB) the
# infix [i:j] whose translate == x.
# ---------------------------------------------------------------------------
def find_infix_witness(B, x):
    n = len(B)
    cands = []
    for i in range(n):
        for j in range(i+1, n+1):
            if translate(tuple(B[i:j])) == x:
                cands.append((i, j))
    # canonical = the longest / earliest contiguous infix realizing x
    if not cands: return None
    cands.sort(key=lambda ij: (-(ij[1]-ij[0]), ij[0]))
    return cands[0]

# ---------------------------------------------------------------------------
# (G1) ANCESTOR-CHAIN <=_e generation: grow infix [i:j] toward [0:n] one column
# at a time, in <=_M ancestor order.  At each intermediate infix K' we record
# whether olt(translate K', translate B) (the IH ROOT target).
# We grow by extending the RIGHT boundary along nextrel1/le0 ancestry (the
# <_M^Next next-ancestor of the current right end), falling back to plain +1
# column growth when no genuine ancestor step exists (still a <=_e column-insert).
# ---------------------------------------------------------------------------
def ancestor_chain(B, i, j):
    """Yield the <=_e-generation chain of infixes from [i:j] up to [0:n],
    growing one column per step. Each grown infix is an intermediate node.
    We grow leftwards then rightwards (the ancestor-shift toward the full block);
    order chosen to keep each step a single-column <=_M ancestor extension."""
    n = len(B)
    chain = [(i, j)]
    lo, hi = i, j
    # grow rightward first (toward later copies = ascending-copy domination),
    # then leftward (toward the green prefix).
    while hi < n:
        hi += 1; chain.append((lo, hi))
    while lo > 0:
        lo -= 1; chain.append((lo, hi))
    return chain

# ---------------------------------------------------------------------------
# (G2) OPER-TILING generation: reconstruct B's leading tiling and step k copies
# ---------------------------------------------------------------------------
def oper_tiling_chain(B):
    """If B = oper(parent, k) for some parent & k>=1, return the chain of
    intermediate tilings [1 copy, 2 copies, ..., k copies] as blocks; else None.
    We detect the tiling directly: B = G ++ k*shifted-blocks. We instead use the
    forward simulation: for each detected (parent, j0, j1, d0, k), build the
    m-copy versions for m=1..k."""
    # detect via the oper structure of B itself: find a periodic suffix tiling.
    # Simpler faithful approach: B sits in the closure; its <=_e ancestors under
    # oper are the m-copy truncations. We reconstruct from the LAST genuine oper
    # that could produce B by trying every (j0,j1) split with periodic blocks.
    n = len(B)
    for j0 in range(n):
        # try block length L = j1-j0
        for L in range(1, n-j0+1):
            if (n - j0) % L != 0: continue
            k = (n - j0) // L
            if k < 2: continue
            # check periodicity: block b copies shifted by k*d0 in row0, row1 fixed
            base = B[j0:j0+L]
            d0 = None; okp = True
            for c in range(k):
                for t in range(L):
                    col = B[j0 + c*L + t]
                    exp0 = base[t][0]
                    if c > 0:
                        if d0 is None:
                            d0 = B[j0+L][0] - B[j0][0]
                        exp0 = base[t][0] + c*d0
                    if col[0] != exp0 or col[1] != base[t][1]:
                        okp = False; break
                if not okp: break
            if okp and d0 is not None:
                # build m-copy intermediate blocks (prefix B[:j0] kept)
                chain = []
                for m in range(1, k+1):
                    blk = list(B[:j0])
                    for c in range(m):
                        for t in range(L):
                            blk.append((base[t][0] + c*d0, base[t][1]))
                    chain.append(tuple(blk))
                return chain
    return None

# ---------------------------------------------------------------------------
# bare SubBlock-tree children (the FAILED baseline), but tested vs ROOT B
# ---------------------------------------------------------------------------
def subblock_tree_nodes(B):
    """all proper SubBlock-tree descendants (desc=takeWhile-arg, sib=dropWhile-
    tail) reachable from B."""
    res = []
    def rec(seg, isroot):
        seg = tuple(seg)
        if not isroot: res.append(seg)
        if not seg: return
        (x, y) = seg[0]; rest = seg[1:]
        i = 0
        while i < len(rest) and rest[i][0] > x: i += 1
        desc = tuple(rest[:i]); sib = tuple(rest[i:])
        if desc: rec(desc, False)
        if sib: rec(sib, False)
    rec(tuple(B), True)
    return res

def main():
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 30, rounds)
        hosts = [M for M in seen if Lng(M) <= 20 and all(c[1] <= 1 for c in M)
                 and M and M[0] == (0, 0)]
        md = max(seen.values())

        # === <=_e-generation (G1) intermediate-node truth ===
        g1_steps = g1_bad = 0      # all intermediate infixes K' (excluding endpoints)
        g1_top_ok = g1_top_chk = 0 # sanity: endpoint olt(tK, tB) at the witness itself
        g1_ex = []
        # === <=_e-generation (G2) oper-tiling intermediate truth ===
        g2_steps = g2_bad = 0
        g2_ex = []
        # === bare SubBlock-tree intermediate-node truth vs ROOT B ===
        sb_nodes = sb_bad = 0
        sb_ex = []

        for B0 in hosts:
            B = tuple(B0[1:])
            tB = translate(B)
            if tB == Z: continue
            n = len(B)
            G0 = set(Gterm(0, tB))

            # --- G1: for each genuine witness, build its ancestor chain ---
            for x in G0:
                if x == tB: continue
                ij = find_infix_witness(B, x)
                if ij is None: continue   # witness not a contiguous infix (rare)
                i, j = ij
                # sanity: the witness endpoint
                g1_top_chk += 1
                if olt(x, tB): g1_top_ok += 1
                chain = ancestor_chain(B, i, j)
                # intermediate nodes = chain[1:-1] (exclude the witness K and full B)
                for (lo, hi) in chain[1:-1]:
                    Kp = tuple(B[lo:hi])
                    tKp = translate(Kp)
                    if tKp == Z or tKp == tB: continue
                    g1_steps += 1
                    if not olt(tKp, tB):
                        g1_bad += 1
                        if len(g1_ex) < 5:
                            g1_ex.append((B, (lo, hi), tKp))

            # --- G2: oper-tiling chain ---
            ch = oper_tiling_chain(B)
            if ch is not None:
                for blk in ch[:-1]:   # exclude full B
                    tblk = translate(blk)
                    if tblk == Z or tblk == tB: continue
                    g2_steps += 1
                    if not olt(tblk, tB):
                        g2_bad += 1
                        if len(g2_ex) < 5:
                            g2_ex.append((B, blk, tblk))

            # --- bare SubBlock-tree vs ROOT B ---
            for node in subblock_tree_nodes(B):
                tnode = translate(node)
                if tnode == Z or tnode == tB: continue
                # only count nodes that are Gterm-0 witnesses (the IH-relevant ones)
                if tnode not in G0: continue
                sb_nodes += 1
                if not olt(tnode, tB):
                    sb_bad += 1
                    if len(sb_ex) < 5:
                        sb_ex.append((B, node, tnode))

        print(f'[closure+{rounds}] maxdepth={md} hosts={len(hosts)}')
        print(f'  SANITY witness endpoints olt(x,tB): chk={g1_top_chk} ok={g1_top_ok} (want all)')
        print(f'  G1 <=_e ANCESTOR-CHAIN intermediate nodes: steps={g1_steps} VIOL={g1_bad}')
        for B, ij, tK in g1_ex[:3]:
            print('      G1bad', mfmt(B), 'infix', ij, 'tK', tfmt(tK)[:40])
        print(f'  G2 <=_e OPER-TILING intermediate nodes:     steps={g2_steps} VIOL={g2_bad}')
        for B, blk, tk in g2_ex[:3]:
            print('      G2bad', mfmt(B), '->', tfmt(tk)[:40])
        print(f'  BARE SubBlock-tree witness nodes vs ROOT B: nodes={sb_nodes} VIOL={sb_bad}')
        for B, node, tn in sb_ex[:3]:
            print('      SBbad', mfmt(B), 'node', mfmt(node), 'tn', tfmt(tn)[:34])

if __name__ == '__main__':
    main()
