#!/usr/bin/env python3
"""closure+3 re-audit of remaining freezes: FBS, NT3-emptiness, memT-emptiness."""
import sys
sys.path.insert(0, '.')
from mine_proj import proj
from mine_e6 import NT
from mine_sibm2 import bad_params
from fast_pss import oper, entry
from wfe_explore import enum_ST

ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=13, rounds=7)
out = set(tuple(M) for M in ST)
cur = list(out)
for _ in range(3):
    new = []
    for M in cur:
        if len(M) < 2: continue
        for nn in (1,2,3,4):
            t = tuple(oper(list(M), nn))
            if t not in out:
                out.add(t); new.append(t)
    cur = new
print('hosts(+3):', len(out), flush=True)
ntc = {}
def NTC(S):
    S = tuple(S)
    if S not in ntc: ntc[S] = NT(list(S))
    return ntc[S]
n_fbs = v_fbs = 0
n_nt3 = 0
n_memt = 0
seen = set()
for Mt in out:
    M = list(Mt)
    L = len(M)
    # FBS: exact segprov windows
    for i in range(L - 1):
        pp = M[i]; u = pp[1]
        for j in range(i + 2, L):
            S = M[i+1:j]; q = M[j]
            if not all(pp[0] < r[0] for r in S): break
            if not pp[0] < q[0]: continue
            if len(S) < 2: continue
            key = (u, tuple(S), q)
            if key in seen: continue
            seen.add(key)
            x2 = NTC(tuple(S) + (q,))
            if proj(u, x2) == x2: continue
            n_fbs += 1
            x = NTC(tuple(S))
            if proj(u, x) == x:
                v_fbs += 1
    # NT3 emptiness: bad branch d0=0, anchor qa with head-tie, q attaining Suc
    bp = bad_params(M)
    if bp is not None:
        j0, j1, i1, d0 = bp
        if d0 == 0:
            Lb = j1 - j0
            for qa in range(Lb):
                if not all(entry(M,0,j0+qa) < entry(M,0,j0+q2) for q2 in range(qa+1, Lb)):
                    continue
                if qa + 1 >= Lb: continue
                if entry(M,1,j0+qa+1) != entry(M,1,j0+qa): continue
                for q2 in range(qa+1, Lb):
                    if entry(M,1,j0+q2) == entry(M,1,j0+qa) + 1:
                        n_nt3 += 1
    # memT emptiness: dseg with max strictly in tail
    for j in range(1, L):
        pp = M[j-1]; u = pp[1]
        for kk in range(j + 1, L + 1):
            S = M[j:kk]
            if not all(pp[0] < r[0] for r in S): break
            c0 = S[0]; rest = S[1:]
            ke = 0
            while ke < len(rest) and rest[ke][0] > c0[0]:
                ke += 1
            T = rest[ke:]
            if not T: continue
            mw = max(c[1] for c in S)
            mk = max([c0[1]] + [c[1] for c in rest[:ke]])
            if mk < mw:
                x = NTC(tuple(S))
                if proj(u, x) != x:
                    n_memt += 1
print(f'FBS: extended-fire windows={n_fbs}  S-nofire violations={v_fbs}')
print(f'NT3 class instances: {n_nt3} (expect 0)')
print(f'memT class instances: {n_memt} (expect 0)')
