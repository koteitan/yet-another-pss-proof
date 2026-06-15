#!/usr/bin/env python3
"""Drill the proj-result structure for proj0_bothfire_eqmaxsub_NF.

proj0 b = P k b1 c1, proj0 f = P k f1 d1, k = maxsub b = maxsub f.
Questions:
  T1: is c1 ALWAYS Z (the smaller's proj tail is empty)?  (tie examples suggest)
  T2: in the main case, is olt b1 f1 ? and does b1=f1 <-> c1=Z and the tie?
  T3: KEY structural fact: proj0 b is the GREATEST critical of b.
      proj0 b = P k b1 c1. What ARE b1, c1 in terms of b?  proj is a critical
      so P k b1 c1 sits inside b. Is b1 = proj k+? Let's see if proj0 result has
      a recursive shape: greatest critical = the deepest p_k(...) chain.
  T4: Does olt(proj0 b)(proj0 f) reduce to: maxsub b = maxsub f = k AND
      olt(proj over the k-criticals)?  Try: proj0 b vs proj0 f compare by
      second-level maxsub:  define ms2 = maxsub of the .b of proj0.
      Is ms2(proj0 b) <= ms2(proj0 f), strict unless deeper tie?
  T5: The clean recursion: is (b1, with host P k b1 c1) again an NF-arg-like
      object on which a SMALLER instance of the same lemma applies?
      Check: is P 0 b1 c1 (or P k b1 c1) in NF-arg class & b1 fires etc.
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

    c1_nonZ = 0
    main_olt_b1f1 = 0
    main_cnt = 0
    tie_cnt = 0
    # T4: second-level maxsub of proj0 .b
    ms2_le = ms2_strict = 0
    # When c1 != Z (smaller proj has nonempty tail), what relates?
    c1nonz_examples = []
    tot = 0
    for b in fire:
        pb = proj(0, b)
        if pb == Z: continue
        _, b1, c1 = pb
        for f in fire:
            if not olt(b, f) or maxsub(b) != maxsub(f): continue
            pf = proj(0, f)
            if pf == Z: continue
            _, f1, d1 = pf
            tot += 1
            if c1 != Z:
                c1_nonZ += 1
                if len(c1nonz_examples) < 6:
                    c1nonz_examples.append((c1, b1, f1, d1, olt(b1,f1), b1==f1))
            if b1 == f1:
                tie_cnt += 1
            else:
                main_cnt += 1
                if olt(b1, f1): main_olt_b1f1 += 1
            # second-level maxsub
            if maxsub(b1) <= maxsub(f1): ms2_le += 1
            if maxsub(b1) < maxsub(f1): ms2_strict += 1
    print("eqmaxsub firing pairs (both proj nonZ):", tot)
    print(f"T1 c1 (smaller proj tail) != Z   : {c1_nonZ}")
    print(f"   main case (b1!=f1)            : {main_cnt}, of which olt b1 f1: {main_olt_b1f1}")
    print(f"   tie  case (b1==f1)            : {tie_cnt}")
    print(f"T4 maxsub(b1) <= maxsub(f1)      : {ms2_le}")
    print(f"   maxsub(b1) <  maxsub(f1)      : {ms2_strict}")
    print("c1!=Z examples (c1,b1,f1,d1,olt b1 f1, b1=f1):")
    for e in c1nonz_examples: print("   ", e)

if __name__ == '__main__':
    main()
