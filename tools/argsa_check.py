#!/usr/bin/env python3
"""Check whether wf_ArgsA (wfsum.thy's sole sorry) is plausibly TRUE.

ArgsA m = { c | exists host in NF with maxsub host = m,
                host = sum of p0(b_i)  (sargs),
                b_i = sum of P a_j c_j Z (summands),
                c = some c_j }
i.e. depth-2 args across ALL standard hosts of level m (a UNION class).

Danger: the x_k / y_k descending chain (y_0 = p1(0), y_{k+1} = p0(p1(y_k)))
might have each element inside a DIFFERENT standard host => wf_ArgsA false.

Tests:
  T1: is any y_k (k>=1) in ArgsA m for some m?
  T2: are ArgsA members themselves in NF (hereditarily standard-shaped)?
      (with what level distribution relative to host level m)
  T3: longest olt-descending chains inside each ArgsA m (finite corpus heuristic).
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import (Z, P, translate, olt, maxsub, spine, fmt, enum_ST,
                          subterms)

def topsummands(t):
    out = []
    while t != ():
        a, b, c = t
        out.append((a, b))
        t = c
    return out

def sargs(t):
    return [b for (a, b) in topsummands(t)]

def build_argsa(ST):
    NFset = set()
    argsa = {}   # m -> set of c
    hosts = {}   # (m, c) -> example host M
    for M in ST:
        t = translate(M)
        NFset.add(t)
        m = maxsub(t)
        for b in sargs(t):
            for (a, c) in topsummands(b):
                argsa.setdefault(m, set()).add(c)
                hosts.setdefault((m, c), M)
    return NFset, argsa, hosts

def y_chain(n):
    ys = [P(1, Z, Z)]
    for _ in range(n):
        ys.append(P(0, P(1, ys[-1], Z), Z))
    return ys

def main():
    ST = enum_ST(seed_max_v=4, oper_ns=(1, 2, 3, 4), max_len=14, rounds=6)
    print(f'#ST_PS enumerated: {len(ST)}')
    NFset, argsa, hosts = build_argsa(ST)
    for m in sorted(argsa):
        print(f'ArgsA[{m}]: {len(argsa[m])} terms')

    # T1: y_k membership
    ys = y_chain(6)
    print('\nT1: y_k in ArgsA m ?')
    for k, y in enumerate(ys):
        found = [m for m in argsa if y in argsa[m]]
        print(f'  y_{k} = {fmt(y)[:60]} : in ArgsA{found}')
        for m in found:
            M = hosts[(m, y)]
            print('      host:', ''.join(f'({a},{b})' for a, b in M))

    # T2: ArgsA members in NF?  level distribution
    print('\nT2: ArgsA[m] subset NF ?  (and level of members)')
    for m in sorted(argsa):
        out, lv = 0, {}
        for c in argsa[m]:
            if c not in NFset:
                out += 1
            lv[maxsub(c)] = lv.get(maxsub(c), 0) + 1
        print(f'  m={m}: |ArgsA|={len(argsa[m])}, NOT in NF: {out}, '
              f'levels: {sorted(lv.items())}')
        if out:
            ex = [c for c in argsa[m] if c not in NFset][:3]
            for c in ex:
                print('    notNF:', fmt(c)[:70])

    # T3: longest descending chain in ArgsA m (greedy DAG longest path)
    print('\nT3: longest olt-chain inside each ArgsA m (corpus heuristic)')
    import functools
    for m in sorted(argsa):
        lst = sorted(argsa[m], key=lambda t: (len(fmt(t))))
        if len(lst) > 400:
            lst = lst[:400]
        # longest path in DAG of olt (it's a linear order, so chain = all
        # comparable... olt is total => chain length = |set|). Skip; instead
        # just note totality.
        print(f'  m={m}: olt total on terms => any finite subset is a chain; '
              f'wf is about infinite descent only')
        break

if __name__ == '__main__':
    main()
