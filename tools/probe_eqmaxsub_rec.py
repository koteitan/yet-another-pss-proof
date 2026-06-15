#!/usr/bin/env python3
"""Is proj0_bothfire_eqmaxsub provable by a clean recursion?

proj0 b = P k b1 c1, proj0 f = P k f1 d1.  Need olt b1 f1 OR (b1=f1 & olt c1 d1).

Hypothesis H_REC: the head-args b1,f1 are themselves projections of SMALLER
NF args, and (b1, f1) satisfy the SAME lemma at a strictly smaller tsize, so
strong induction closes it.

Probe:
  (a) tsize measure: is tsize(b1)+tsize(f1) < tsize(b)+tsize(f) ? (well-founded)
  (b) when b1!=f1 and olt b1 f1: are b1,f1 NF-arg-class & do they fire & eq maxsub?
      (so the SAME lemma applies recursively)  OR is olt b1 f1 already from a
      simpler fact (e.g. their leads differ)?
  (c) lead b1 vs lead f1: does lead b1 < lead f1 give olt b1 f1 outright in the
      main case (subscript-first)?  count main cases where lead b1 < lead f1.
  (d) tie b1=f1: is c1 = Z always?  (then olt c1 d1 = olt Z d1, trivial if d1!=Z)
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import translate, enum_ST, olt, maxsub, spine
Z = ()
def le(s, t): return s == t or olt(s, t)
def tsize(t):
    if t == Z: return 1
    return 1 + tsize(t[1]) + tsize(t[2])
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

    leadlt = 0   # main cases with lead b1 < lead f1
    leadeq_argolt = 0  # main: lead b1 = lead f1, need deeper
    main = 0
    tie = 0; tie_c1Z = 0
    # (c') decompose olt b1 f1 reason
    reason = {'lead_lt':0, 'lead_eq_arg':0, 'lead_eq_tail':0}
    for b in fire:
        pb = proj(0, b)
        if pb == Z: continue
        _, b1, c1 = pb
        for f in fire:
            if not olt(b, f) or maxsub(b) != maxsub(f): continue
            pf = proj(0, f)
            if pf == Z: continue
            _, f1, d1 = pf
            if b1 == f1:
                tie += 1
                if c1 == Z: tie_c1Z += 1
            else:
                main += 1
                # decompose olt b1 f1
                if b1 == Z or f1 == Z:
                    reason['lead_lt'] += 1  # Z<P handled as lead
                    continue
                if lead(b1) < lead(f1): reason['lead_lt'] += 1
                elif lead(b1) == lead(f1):
                    if olt(b1[1], f1[1]): reason['lead_eq_arg'] += 1
                    else: reason['lead_eq_tail'] += 1
                else:
                    reason['REVERSAL'] = reason.get('REVERSAL',0)+1
    print(f"main (b1!=f1): {main}")
    print(f"  olt b1 f1 reason: {reason}")
    print(f"tie  (b1==f1): {tie}, of which c1==Z: {tie_c1Z}")

if __name__ == '__main__':
    main()
