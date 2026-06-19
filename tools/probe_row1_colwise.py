#!/usr/bin/env python3
"""ROW-1 AXIS, step 2: hunt the columnwise invariant for seqlex(Ksh, B) on the
NARROW pinned object (single-tree blockok-1 B, canonical arg-witness K).

Last probe: seqlex(Ksh,B) decided at first diff by row0-lower OR row1-lower
(never shift-K higher).  Test stronger/cleaner candidate invariants:

 INV-A (columnwise pairlt-dominance, prefix): for all j < len(Ksh),
        Ksh[j].1 < B[j].1  OR  (Ksh[j].1 == B[j].1 and Ksh[j].2 <= B[j].2).
        i.e. Ksh weakly column-dominated by B's prefix everywhere it overlaps.
        (This would IMMEDIATELY give seqlex via first-strict-or-prefix.)
 INV-B (row-1 weak dominance under row-0 equality only -- the analog of the sib
        boundary fact): wherever Ksh[j].1 == B[j].1, Ksh[j].2 <= B[j].2.
 INV-C (row-0 dominance): for all j<len(Ksh), Ksh[j].1 <= B[j].1.
        (the row-0 'flattening' fact: the shifted deep infix never out-ascends B)
 INV-D: Ksh[j].1 == B[j].1  =>  Ksh[j].2 <= B[j].2  AND  Ksh[j].1 <= B[j].1
        (INV-B & INV-C combined = INV-A essentially)

Also: relate to the ORIGINAL (unshifted) K row-1 sequence vs B's row-1 prefix:
 INV-E: K.map(.2) is a prefix-position match: K[t].2 vs B[i+t].2 where K=B[i:j]?
        (K IS a contiguous infix B[i:j] so K[t]==B[i+t] EXACTLY -- row-1 of K
        equals row-1 of B at shifted index.  The shift only changes row-0.  So
        Ksh[t].2 == K[t].2 == B[i+t].2.  The row-1 comparison Ksh[t].2 vs B[t].2
        is B[i+t].2 vs B[t].2 -- a SELF-comparison of B's row-1 sequence at
        offset i.  TEST: is B[i+t].2 <= B[t].2 whenever row0 ties?  This is a
        row-1 quasi-monotonicity of B under index shift.)

Report 0-viol counts @+5/+6/+7.  A 0-viol INV that's provable from ST_PS row-1
discipline (steps1/row1<=1) closes the leaf.
"""
import sys
sys.path.insert(0, '.')
from fast_pss import Lng
from wfe_explore import translate, olt
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt
from probe_bmocf_ancestor import enum_depth

Z = ()
def Gterm(u, t):
    if t == (): return []
    a, b, c = t; out = []
    if u <= a: out.append(b); out += Gterm(u, b)
    out += Gterm(u, c); return out
def steps1(B): return all(B[j+1][0] <= B[j][0]+1 for j in range(len(B)-1))
def blockok(d, B):
    if not B: return True
    return B[0][0] == d and all(p[0] >= d for p in B) and steps1(B)
def split(B):
    c = B[0]; rest = B[1:]; i = 0
    while i < len(rest) and rest[i][0] > c[0]: i += 1
    return c, tuple(rest[:i]), tuple(rest[i:])
def all_subblocks_with_pos(B):
    """yield (K, i) where K = B[i:i+len(K)] contiguous infix (canonical witnesses
    are contiguous infixes; we also recover the start index i)."""
    res = []
    Bt = tuple(B)
    def rec(seg, start):
        seg = tuple(seg); res.append((seg, start))
        if not seg: return
        c = seg[0]; rest = seg[1:]; i = 0
        while i < len(rest) and rest[i][0] > c[0]: i += 1
        rec(rest[:i], start + 1)              # desc starts after head
        rec(rest[i:], start + 1 + i)          # sib starts after head+desc
    rec(Bt, 0)
    return res
def shift(K, delta): return tuple((p[0]+delta, p[1]) for p in K)

def main():
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        hosts = [M for M in seen if Lng(M) <= 18 and all(c[1] <= 1 for c in M)
                 and M and M[0] == (0, 0)]
        md = max(seen.values())
        chk = 0
        a_bad = b_bad = c_bad = e_bad = 0
        aex = bex = cex = eex = None
        for B0 in hosts:
            B = tuple(B0[1:])
            if not B: continue
            tB = translate(B)
            if tB == Z: continue
            y, A, S = tB
            if S != Z: continue
            if not blockok(1, B): continue
            G0 = set(Gterm(0, tB))
            seenK = {}
            for (K, i) in all_subblocks_with_pos(B):
                if not K: continue
                tK = translate(K)
                if tK in G0 and tK != tB and tK not in seenK:
                    seenK[tK] = (K, i)
            for tK, (K, i) in seenK.items():
                delta = 1 - K[0][0]
                Ksh = shift(K, delta)
                chk += 1
                n = len(Ksh)
                # INV-A
                okA = all(Ksh[t][0] < B[t][0] or
                          (Ksh[t][0] == B[t][0] and Ksh[t][1] <= B[t][1])
                          for t in range(min(n, len(B))))
                if not okA:
                    a_bad += 1
                    if aex is None: aex = (mfmt(B), mfmt(Ksh))
                # INV-B
                okB = all(not (Ksh[t][0] == B[t][0]) or Ksh[t][1] <= B[t][1]
                          for t in range(min(n, len(B))))
                if not okB:
                    b_bad += 1
                    if bex is None: bex = (mfmt(B), mfmt(Ksh))
                # INV-C
                okC = all(Ksh[t][0] <= B[t][0] for t in range(min(n, len(B))))
                if not okC:
                    c_bad += 1
                    if cex is None: cex = (mfmt(B), mfmt(Ksh))
                # INV-E: B[i+t].2 <= B[t].2 whenever Ksh[t].1==B[t].1 (row0 tie)
                # (K[t]==B[i+t] exactly; row1 unchanged by shift)
                okE = True
                for t in range(min(n, len(B))):
                    if i + t < len(B) and Ksh[t][0] == B[t][0]:
                        if not (B[i+t][1] <= B[t][1]):
                            okE = False; break
                if not okE:
                    e_bad += 1
                    if eex is None: eex = (mfmt(B), mfmt(Ksh), i)
        print(f'[+{rounds}] md={md} single-tree canonical-K checked={chk}')
        print(f'   INV-A colwise pairlt-dom (prefix): BAD={a_bad}')
        print(f'   INV-B row1<= under row0-tie:       BAD={b_bad}')
        print(f'   INV-C row0<= everywhere:           BAD={c_bad}')
        print(f'   INV-E B[i+t].2<=B[t].2 @row0-tie:  BAD={e_bad}')
        if aex: print('      Aex B', aex[0], 'Ksh', aex[1])
        if bex: print('      Bex B', bex[0], 'Ksh', bex[1])
        if cex: print('      Cex B', cex[0], 'Ksh', cex[1])
        if eex: print('      Eex B', eex[0], 'Ksh', eex[1], 'i', eex[2])

if __name__ == '__main__':
    main()
