#!/usr/bin/env python3
"""ROW-1 AXIS, step 2b: does seqlex(Ksh, B) reduce by a ROW-1-anchored recursion?

Both Ksh and B start at row0=1.  seqlex first column: Ksh[0]=(1, k0), B[0]=(1, y)
where y=B[0].2.  pairlt((1,k0),(1,y)) iff k0 < y.  If k0<y: DONE (row-1 win at
col0).  If k0==y: tails must seqlex.  If k0>y: FAIL.

So the FIRST-COLUMN row-1 fact is: k0 <= y (the canonical infix's head row-1,
after shift, <= B's head row-1 y).  And when k0==y we recurse into the
translate-arg structure.

Test the candidate inductive invariant on the narrow object:
  R1col: Ksh[0].2 <= B[0].2  (head row-1 of shifted canonical-K <= y)   [first col]
  And classify the k0==y cases: do they recurse to a SMALLER instance of the SAME
  pinned problem (single-tree blockok-1, canonical witness)?  i.e. is the recursion
  self-similar and well-founded on the row-1 axis?

Also reframe via the translate tree: tK = translate K = P k0 KA KS.  Since tK in
Gterm0(tB) and tB = P y A Z (single tree), and seqlex<->olt:
  olt(tK, tB):  k0 vs y.  k0<y: done.  k0==y: olt(KA,A) then olt(KS, Z=...).
So the row-1 first-column fact IS  k0 <= y = lead(tB), and the recursion is the
olt-drill.  Test: lead(tK) <= lead(tB) for ALL canonical witnesses (row-1 head
dominance), AND when lead(tK)==lead(tB), does the arg-drill go to a smaller
canonical-witness problem?
"""
import sys
sys.path.insert(0, '.')
from fast_pss import Lng
from wfe_explore import translate, olt
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt
from probe_bmocf_ancestor import enum_depth

Z = ()
def lead(t): return t[0] if t else -1
def Gterm(u, t):
    if t == (): return []
    a, b, c = t; out = []
    if u <= a: out.append(b); out += Gterm(u, b)
    out += Gterm(u, c); return out
def steps1(B): return all(B[j+1][0] <= B[j][0]+1 for j in range(len(B)-1))
def blockok(d, B):
    if not B: return True
    return B[0][0] == d and all(p[0] >= d for p in B) and steps1(B)

def main():
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        hosts = [M for M in seen if Lng(M) <= 18 and all(c[1] <= 1 for c in M)
                 and M and M[0] == (0, 0)]
        md = max(seen.values())
        chk = 0
        leadbad = 0          # lead(tK) > lead(tB)  (R1col fail)
        eq_lead = 0          # lead(tK)==lead(tB): the recurse case
        # in the eq case, olt drills: tK=P y KA KS, tB=P y A Z.
        #   need olt(KA, A) [if KA!=A] -- then KA must be < A.  Is KA in Gterm0 A?
        #   KA = arg of the witness; A = arg of tB.  Recurse problem: olt(KA, A)
        #   where A=translate(B-body) is a (level-2) forest.  Is KA a canonical
        #   Gterm0 witness of A?  i.e. does the recursion stay self-similar?
        eq_KAeqA = eq_KA_in_G0A = eq_KA_olt_A = eq_KA_other = 0
        leadex = None
        for B0 in hosts:
            B = tuple(B0[1:])
            if not B: continue
            tB = translate(B)
            if tB == Z: continue
            y, A, S = tB
            if S != Z: continue
            if not blockok(1, B): continue
            G0 = set(Gterm(0, tB))
            for tK in G0:
                if tK == Z or tK == tB: continue
                chk += 1
                if lead(tK) > lead(tB):
                    leadbad += 1
                    if leadex is None: leadex = (mfmt(B), tfmt(tK), lead(tB))
                elif lead(tK) == lead(tB):
                    eq_lead += 1
                    KA = tK[1]
                    if KA == A: eq_KAeqA += 1
                    elif olt(KA, A):
                        eq_KA_olt_A += 1
                        if KA in set(Gterm(0, A)): eq_KA_in_G0A += 1
                    else:
                        eq_KA_other += 1
        print(f'[+{rounds}] md={md} single-tree canonical-K checked={chk}')
        print(f'   R1col lead(tK) > lead(tB) [row-1 head dom FAIL]: BAD={leadbad}')
        if leadex: print('      leadbad B', leadex[0], 'tK', leadex[1], 'leadtB', leadex[2])
        print(f'   eq-lead cases={eq_lead}: KA=A:{eq_KAeqA}  olt(KA,A):{eq_KA_olt_A} '
              f'(of which KA in Gterm0 A:{eq_KA_in_G0A})  KA-not<=A:{eq_KA_other}')

if __name__ == '__main__':
    main()
