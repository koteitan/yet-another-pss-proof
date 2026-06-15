#!/usr/bin/env python3
"""Find the cleanest provable invariant for proj0_bothfire_eqmaxsub_NF.

Candidate routes (eqmaxsub firing pairs, olt b f, both NF head-0 args):
  R1: proj0 b in Gterm 0 f ?  (known FALSE per task -- confirm)
  R2: proj0 b <o f ? (proj0 b is below the larger arg)
  R3: exists g' in Gterm 0 f with proj0 b <o g' AND g' <o f is FALSE (violator)
      -> i.e. a VIOLATOR of f strictly above proj0 b (other than proj0 f).
  R4: proj0 b <=o proj0 f directly, and analyze the b1=f1 tie sub-case:
      when proj0 b=P k b1 c1, proj0 f=P k f1 d1, b1=f1 -> is olt c1 d1?
      and is (b1,c1) "smaller" so a recursion terminates?
  R5: KEY -- is maxsub(proj0 b) <= maxsub(proj0 f) ? and lead ties.
      Does the SECOND subscript (maxsub of the .b arg) strictly order?
  R6: proj0 b = max over criticals; is it <=o proj0 f because every critical
      of b is <=o some critical of f (a critical-domination/embedding)?
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import translate, enum_ST, olt, maxsub, spine
Z = ()
def le(s, t): return s == t or olt(s, t)
def Gterm(u, t):
    if t == Z: return []
    a, b, c = t; out = []
    if u <= a: out.append(b); out += Gterm(u, b)
    out += Gterm(u, c); return out
def pfire(u, b): return any(not olt(g, b) for g in Gterm(u, b))
def proj(u, b):
    while True:
        bad = [g for g in Gterm(u, b) if not olt(g, b)]
        if not bad: return b
        m = bad[0]
        for h in bad[1:]:
            if olt(m, h): m = h
        b = m
def lead(t): return 0 if t == Z else t[0]

def main():
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=14, rounds=8)
    NF = sorted({translate(M) for M in ST}, key=str)
    args = sorted({t[1] for t in NF if t != Z and t[0] == 0}, key=str)
    fire = [b for b in args if pfire(0, b)]

    R = dict(R1_in=0, R2_below=0, R3_violwit=0, tie=0, tie_olt_c=0,
             R5_msub_b_le_f=0, R5_msub_strict=0, tot=0)
    tie_examples = []
    for b in fire:
        pb = proj(0, b)
        for f in fire:
            if not olt(b, f) or maxsub(b) != maxsub(f): continue
            R['tot'] += 1
            pf = proj(0, f)
            Gf = Gterm(0, f)
            if pb in Gf: R['R1_in'] += 1
            if olt(pb, f): R['R2_below'] += 1
            # violator witness other than pf
            if any((not olt(gp, f)) and olt(pb, gp) and gp != pf for gp in Gf):
                R['R3_violwit'] += 1
            # maxsub relation of proj results
            if maxsub(pb) <= maxsub(pf): R['R5_msub_b_le_f'] += 1
            if maxsub(pb) < maxsub(pf): R['R5_msub_strict'] += 1
            # tie sub-case
            if pb != Z and pf != Z:
                _, b1, c1 = pb; _, f1, d1 = pf
                if b1 == f1:
                    R['tie'] += 1
                    if olt(c1, d1): R['tie_olt_c'] += 1
                    if len(tie_examples) < 8:
                        tie_examples.append((b1==f1, c1, d1, olt(c1,d1), b, f))
    print("eqmaxsub firing pairs:", R['tot'])
    print(f"R1 proj0 b in Gterm0 f          : {R['R1_in']}   (expect 0, FALSE)")
    print(f"R2 proj0 b <o f                 : {R['R2_below']}")
    print(f"R3 violator wit != proj0 f      : {R['R3_violwit']}")
    print(f"R5 maxsub(pb) <= maxsub(pf)     : {R['R5_msub_b_le_f']}")
    print(f"R5 maxsub(pb) <  maxsub(pf)     : {R['R5_msub_strict']}")
    print(f"tie (b1=f1) cases               : {R['tie']}")
    print(f"   of which olt c1 d1           : {R['tie_olt_c']}")
    print("tie examples (b1=f1, c1, d1, olt c1 d1):")
    for e in tie_examples: print("   ", e[:4])

if __name__ == '__main__':
    main()
