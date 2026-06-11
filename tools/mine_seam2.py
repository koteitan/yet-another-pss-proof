#!/usr/bin/env python3
"""Structural mining of the seam (same-cut both-fire) instances:
classify msfx S shapes to find a small frozen core for E6_seam
(like QDIAG did for qcut_last).

Candidate reductions tested per instance:
  SING   : msfx S is a singleton
  ALL    : msfx S = S (whole segment at max level)
  CONST0 : all fst equal within msfx S
  HDMIN  : hd(msfx) is fst-min of msfx (INV2 itself)
  HD_S   : hd(msfx S) = hd S
  SNDC   : snd constant on S
  NDEC   : snd non-decreasing along S
"""
import sys
sys.path.insert(0, '.')
from collections import Counter
from wfe_explore import translate, fmt, enum_ST
from valnorm import conv, nrm, lt_term, fmtb
from mine_proj import proj
from mine_e6 import NT
from mine_fire4 import msfx
from fast_pss import oper


def hosts_plus(extra_rounds=1):
    ST = enum_ST(seed_max_v=4, oper_ns=(1, 2, 3, 4), max_len=13, rounds=7)
    out = set(tuple(M) for M in ST)
    cur = list(out)
    for _ in range(extra_rounds):
        new = []
        for M in cur:
            if len(M) < 2:
                continue
            for n in (1, 2, 3, 4):
                t = tuple(oper(list(M), n))
                if t not in out:
                    out.add(t)
                    new.append(t)
        cur = new
    return out


def main():
    HS = hosts_plus(1)
    print('hosts:', len(HS), flush=True)
    n = 0
    c = Counter()
    lens = Counter()
    ex = {}
    for Mt in HS:
        M = list(Mt)
        if len(M) < 2:
            continue
        q = M[-1]
        for i in range(len(M) - 1):
            pp = M[i]
            S = list(M[i + 1:-1])
            if not S:
                continue
            if not all(pp[0] < r[0] for r in S):
                continue
            if not pp[0] < q[0]:
                continue
            u = pp[1]
            x = NT(S)
            x2 = NT(S + [q])
            if proj(u, x) == x or proj(u, x2) == x2:
                continue
            m = max(cc[1] for cc in S)
            if q[1] > m:
                continue  # q-cut
            n += 1
            T = msfx(S)
            lens[len(T)] += 1
            tags = []
            if len(T) == 1:
                tags.append('SING')
            if T == S:
                tags.append('ALL')
            if all(t[0] == T[0][0] for t in T):
                tags.append('CONST0')
            if all(T[0][0] <= t[0] for t in T):
                tags.append('HDMIN')
            if T[0] == S[0]:
                tags.append('HD_S')
            if all(cc[1] == S[0][1] for cc in S):
                tags.append('SNDC')
            if all(S[k][1] <= S[k + 1][1] for k in range(len(S) - 1)):
                tags.append('NDEC')
            key = tuple(tags)
            c[key] += 1
            if key not in ex:
                ex[key] = (M, i, S, T, q)
    print('instances:', n)
    print('len(msfx) histogram:', dict(sorted(lens.items())))
    for k, v in sorted(c.items(), key=lambda kv: -kv[1]):
        print(f'{v:6d}  {"+".join(k) if k else "(none)"}')
    for k, (M, i, S, T, q) in ex.items():
        print('EX', '+'.join(k) if k else '(none)', 'i=', i,
              'M=', ''.join(f'({a},{b})' for a, b in M))
        print('   S=', ''.join(f'({a},{b})' for a, b in S),
              ' T=', ''.join(f'({a},{b})' for a, b in T), ' q=', q)


if __name__ == '__main__':
    main()
