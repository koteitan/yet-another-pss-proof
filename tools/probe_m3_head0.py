#!/usr/bin/env python3
"""probe_m3_head0.py -- verify the HEAD-0 singleton step is fully clean (the M4
target is head-0 diagonal towers; the Acc Rnf reduction needs Acc(translate
diagSeq 0 v) = p0(p1(...pv(0))), all head-0).

For a head-0 NF single P 0 b Z, the oltMn-in-stratum predecessors v <o P 0 b Z:
  - olt_P_P: head a'=0 (can't be < 0), so a'=0 = a always (NO subscript drop,
    VACUOUSLY -- the bad case needs a'<a=0, impossible).
  - so every predecessor-summand P 0 b' Z has b' <o b (argdrop) OR b'=b (then
    tail decides, but single principal so b'=b => equal).
  => the head-0 singleton step is the PURE arg-accessibility induction on b.

CHECK (faithful, @+5/+6/+7): for head-0 NF single P 0 b Z, every NF predecessor v
decomposes into summands P 0 b'_i Z (all head-0) with b'_i <o b.  Tabulate:
  - are all predecessor-summands head-0?  (head match, trivial from olt a'<=0)
  - is each b'_i <o b?  (the argdrop, = olt_P_P middle disjunct)
  - is cr(P 0 b'_i Z) <= cr(P 0 b Z)?  (stays in stratum / lower)
If all clean => BUILD head-0 M3 (no forest fact, no H0clause enumeration).
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import translate, olt, maxsub
from probe_bmocf_ancestor import enum_depth

Z = ()
def cr_inv(t):
    if t == (): return 0
    a, b, c = t
    inv = 1 if (b != () and maxsub(b) > a) else 0
    return max(inv + cr_inv(b), cr_inv(c))
def summands(t):
    if t == (): return []
    a, b, c = t
    return [(a, b, ())] + summands(c)

def main():
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 30, rounds)
        NF = set(translate(M) for M in seen); NF.discard(Z)
        NFl = list(NF)
        md = max(seen.values())
        # head-0 NF singles
        h0 = [t for t in NF if t[2] == Z and t != Z and t[0] == 0]

        tot = head0 = argdrop = cr_ok = 0
        bad = []
        for t in h0:
            a, b, _ = t   # a == 0
            n = cr_inv(t)
            for v in NFl:
                if v == t or not olt(v, t):
                    continue
                for s in summands(v):
                    sa, sb, _ = s
                    tot += 1
                    if sa == 0:
                        head0 += 1
                    # argdrop: head 0 and sb <o b, OR sb == b
                    if sa == 0 and (olt(sb, b) or sb == b):
                        argdrop += 1
                    elif len(bad) < 6:
                        from wfe_explore import fmt as tf
                        bad.append((tf(t)[:26], tf(s)[:26]))
                    if cr_inv(s) <= n:
                        cr_ok += 1

        print(f'[closure+{rounds}] maxdepth={md} head0-NF-singles={len(h0)}')
        print(f'  pred-summands={tot}  head-0={head0}  argdrop(head0 & sb<o b or =b)={argdrop}'
              f'  cr<=n={cr_ok}')
        if bad:
            print('  NON-ARGDROP examples:', bad[:6])

if __name__ == '__main__':
    main()
