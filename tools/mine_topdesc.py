#!/usr/bin/env python3
"""TOP_desc statement mining (続27補6: 474 pairs / 0 violations).
Top-level trees of a standard host M: maximal segments rooted at fst=0
columns. For adjacent root positions p < p' (consecutive 0-columns):
  K  = M[p:p']        (earlier tree, root included)
  K1 = M[p':next0]    (later tree)
Claim: ole (NT K1) (NT K)   (weak nrm descent).
Variants: roots included/excluded to pin the exact 474-form.
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import enum_ST
from valnorm import lt_term
from mine_e6 import NT
from fast_pss import oper

def hosts_plus(extra=1):
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=13, rounds=7)
    out = set(tuple(M) for M in ST)
    cur = list(out)
    for _ in range(extra):
        new = []
        for M in cur:
            if len(M) < 2: continue
            for n in (1,2,3,4):
                t = tuple(oper(list(M), n))
                if t not in out:
                    out.add(t); new.append(t)
        cur = new
    return out

def main():
    HS = hosts_plus(1)
    print('hosts:', len(HS), flush=True)
    ntc = {}
    def NTC(S):
        S = tuple(S)
        if S not in ntc: ntc[S] = NT(list(S))
        return ntc[S]
    seen = set()
    nI = vI = nX = vX = 0
    ex = []
    for Mt in HS:
        M = list(Mt)
        roots = [i for i, c in enumerate(M) if c[0] == 0]
        if len(roots) < 2: continue
        roots.append(len(M))
        for t in range(len(roots) - 2):
            p, p2, p3 = roots[t], roots[t+1], roots[t+2]
            K = tuple(M[p:p2]); K1 = tuple(M[p2:p3])
            key = (K, K1)
            if key in seen: continue
            seen.add(key)
            # roots included
            nI += 1
            a, b = NTC(K1), NTC(K)
            if not (a == b or lt_term(a, b)):
                vI += 1
                if len(ex) < 4: ex.append(('I', M, p, p2, p3))
            # roots excluded (bodies only)
            Kb, K1b = K[1:], K1[1:]
            nX += 1
            ab = NTC(K1b); bb = NTC(Kb)
            if not (ab == bb or lt_term(ab, bb)):
                vX += 1
                if len(ex) < 4: ex.append(('X', M, p, p2, p3))
    print(f'adjacent top-tree pairs: {nI}  viol(root-incl): {vI}  viol(bodies): {vX}')
    for t in ex:
        print(t[0], 'p=', t[2], t[3], t[4], 'M=', ''.join(f'({a},{b})' for a, b in t[1]))

if __name__ == '__main__':
    main()
