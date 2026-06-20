#!/usr/bin/env python3
"""probe_wqo_bcore2.py -- CORRECTED decisive de-risk.  The previous probe tested
olt(intermediate, ROOT B) which is trivially the witness fact.  The REAL question
that killed the bare SubBlock route is whether the INDUCTION CARRIER holds at the
intermediate node, i.e. with the FIXED witness K and the intermediate M' as the
TARGET:

    carrier(K, M') := olt(translate K)(translate M')   [or the seqlex form]

The bare SubBlock-derivation induction proves olt(tK,tB) by recursing B -> child
and needs carrier(K, child) at each desc/sib intermediate.  Memory: this is FALSE
(seqlex(shift K, B)=True but seqlex(shift K, desc-child)=False, 183/443 path-bad).

The architect claims the <=_e-GENERATION (grow K toward B along <_M^Next ancestor
steps) keeps carrier(K, M') TRUE at every intermediate M', BECAUSE the generation
visits the ANCESTOR-ORDERED supersequences of K (K subset M' subset B), not the
translate-tree sub-FORESTS of B.

THE apples-to-apples test:  fix the canonical witness K (infix B[i:j]).
 (A) bare-SubBlock chain: the translate-tree path from B DOWN to K -- i.e. the
     sequence of desc/sib children B=N0 -> N1 -> ... -> Nm=K (the SubBlock
     derivation that realizes K).  At each Nt (t>=1, t<m) test carrier(K, Nt).
 (B) <=_e ancestor chain: K=A0 subset A1 subset ... subset Am=B (grow one column,
     ancestor order).  At each At (0<t<m) test carrier(K, At).

If (B) intermediates are 0-viol where (A) intermediates are BAD -> the <=_e
generation is genuinely richer (route promising).  If (B) ALSO bad -> weak.

carrier tested in TWO forms (report both):
  C-olt:    olt(translate K)(translate M')
  C-seqlex: seqlex(shift K to head-row0 of M', M')  (the genuine engine content)
"""
import sys
sys.path.insert(0, '.')
from fast_pss import Lng, entry, diagSeq, oper
from wfe_explore import translate, olt
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt
from probe_bmocf_ancestor import enum_depth

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

# ---- seqlex on pair-sequences (the BMS native order, faithful) ----
def pairlt(p, q):
    # lexicographic on (row0, row1)? The lean seqlex first-diff is decided by the
    # column compare used in olt_ST_iff_seqlex.  Per memory, first-diff is decided
    # row0-OR-row1 lower.  We model column compare as (row0,row1) lex.
    return p < q

def seqlex(K, M):
    """seqlex(K, M): True iff K is seqlex-below M (proper-prefix => True,
    else first differing column has K's column < M's column lexicographically)."""
    nk, nm = len(K), len(M)
    i = 0
    while i < nk and i < nm:
        if K[i] == M[i]:
            i += 1; continue
        return pairlt(K[i], M[i])
    # one is a prefix of the other
    return nk < nm   # K strictly shorter prefix => below

def shift_to(K, target_row0):
    """shift K so its head row0 = target_row0 (row1 fixed), faithful translate_shift."""
    if not K: return K
    d = target_row0 - K[0][0]
    return tuple((r0 + d, r1) for (r0, r1) in K)

# ---- find canonical infix witness ----
def find_infix(B, x):
    n = len(B); cands = []
    for i in range(n):
        for j in range(i+1, n+1):
            if translate(tuple(B[i:j])) == x:
                cands.append((i, j))
    if not cands: return None
    cands.sort(key=lambda ij: (-(ij[1]-ij[0]), ij[0]))
    return cands[0]

# ---- bare SubBlock-tree DERIVATION path from B down to the node realizing K ----
def subblock_path_to(B, target):
    """Return the desc/sib derivation path B=N0,N1,...,Nm=target (list of blocks),
    or None if target is not a SubBlock-tree node of B."""
    from functools import lru_cache
    def children(seg):
        if not seg: return []
        (x, y) = seg[0]; rest = seg[1:]
        i = 0
        while i < len(rest) and rest[i][0] > x: i += 1
        out = []
        if rest[:i]: out.append(tuple(rest[:i]))
        if rest[i:]: out.append(tuple(rest[i:]))
        return out
    # BFS/DFS for target
    stack = [(tuple(B), [tuple(B)])]
    seen = set()
    while stack:
        seg, path = stack.pop()
        if seg == target:
            return path
        if seg in seen: continue
        seen.add(seg)
        for ch in children(seg):
            stack.append((ch, path + [ch]))
    return None

def main():
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 30, rounds)
        hosts = [M for M in seen if Lng(M) <= 20 and all(c[1] <= 1 for c in M)
                 and M and M[0] == (0, 0)]
        md = max(seen.values())

        # bare-SubBlock derivation-path intermediate carrier truth
        a_olt_chk = a_olt_bad = 0
        a_seq_chk = a_seq_bad = 0
        a_ex = []
        # <=_e ancestor-grow intermediate carrier truth
        b_olt_chk = b_olt_bad = 0
        b_seq_chk = b_seq_bad = 0
        b_ex = []
        # how many witnesses K are realizable as a SubBlock-tree node at all
        wit_total = wit_sbnode = 0

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
                K = tuple(B[i:j])
                wit_total += 1

                # === (A) bare SubBlock derivation path B -> ... -> (a node = K?) ===
                # the node realizing K = some SubBlock-tree node with translate==x
                # (K as infix may not be exactly a SubBlock-tree node; find one).
                target = None
                # search SubBlock-tree nodes for translate==x
                def find_node(seg):
                    res = []
                    def rec(s):
                        if translate(s) == x: res.append(s)
                        if not s: return
                        (px, py) = s[0]; rest = s[1:]
                        k = 0
                        while k < len(rest) and rest[k][0] > px: k += 1
                        if rest[:k]: rec(tuple(rest[:k]))
                        if rest[k:]: rec(tuple(rest[k:]))
                    rec(seg)
                    return res
                nodes = find_node(B)
                if nodes:
                    wit_sbnode += 1
                    target = nodes[0]
                    path = subblock_path_to(B, target)
                    if path and len(path) >= 3:
                        # intermediates: path[1:-1]; carrier target = the intermediate Nt
                        Kt = target  # the fixed witness block (a SubBlock-tree node)
                        tKt = translate(Kt)
                        for Nt in path[1:-1]:
                            tNt = translate(Nt)
                            if tNt == Z: continue
                            # C-olt: olt(tKt, tNt) -- is the witness still olt-below
                            # the intermediate ancestor node?
                            a_olt_chk += 1
                            if not olt(tKt, tNt):
                                a_olt_bad += 1
                                if len(a_ex) < 5: a_ex.append((B, Kt, Nt))
                            # C-seqlex: shift Kt to Nt head row0, seqlex below Nt
                            a_seq_chk += 1
                            Ksh = shift_to(Kt, Nt[0][0])
                            if not seqlex(Ksh, Nt):
                                a_seq_bad += 1

                # === (B) <=_e ancestor grow: K=infix[i:j] -> grow to [0:n]=B ===
                # intermediates At = B[i:j] subset ... subset B[0:n]; carrier target
                # = the intermediate At; the fixed witness = K.
                lo, hi = i, j
                chain = [(lo, hi)]
                while hi < n:
                    hi += 1; chain.append((lo, hi))
                while lo > 0:
                    lo -= 1; chain.append((lo, hi))
                tK = translate(K)
                for (clo, chi) in chain[1:-1]:
                    At = tuple(B[clo:chi])
                    tAt = translate(At)
                    if tAt == Z: continue
                    b_olt_chk += 1
                    if not olt(tK, tAt):
                        b_olt_bad += 1
                        if len(b_ex) < 5: b_ex.append((B, K, At))
                    b_seq_chk += 1
                    Ksh = shift_to(K, At[0][0])
                    if not seqlex(Ksh, At):
                        b_seq_bad += 1

        print(f'[closure+{rounds}] maxdepth={md} hosts={len(hosts)} '
              f'witnesses={wit_total} (sb-node-realizable={wit_sbnode})')
        print(f'  (A) BARE SubBlock deriv-path intermediates vs witness:')
        print(f'        C-olt  chk={a_olt_chk} VIOL={a_olt_bad}    '
              f'C-seqlex chk={a_seq_chk} VIOL={a_seq_bad}')
        for B, K, N in a_ex[:3]:
            print('        Abad B', mfmt(B), 'K', tfmt(translate(K))[:24],
                  'interm', tfmt(translate(N))[:24])
        print(f'  (B) <=_e ANCESTOR-GROW intermediates vs witness:')
        print(f'        C-olt  chk={b_olt_chk} VIOL={b_olt_bad}    '
              f'C-seqlex chk={b_seq_chk} VIOL={b_seq_bad}')
        for B, K, A in b_ex[:3]:
            print('        Bbad B', mfmt(B), 'K', tfmt(translate(K))[:24],
                  'interm', tfmt(translate(A))[:24])

if __name__ == '__main__':
    main()
