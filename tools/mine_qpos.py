#!/usr/bin/env python3
"""qpos window decomposition mining at closure+3.
Config (exact ginv_ob_qpos premises): X = oper-bad image of M with n copies,
window (p, p+1, ..., Suc p+N) with dom, stop cl at Suc p side, p >= j0,
qP = (p-j0) mod L != 0, crossing into next copy.
For each window element l in (p, Suc p+N]:
  side: SAME copy as p / NEXT copy / further
  claim: snd(X!l) <= max(snd(X!p), snd(X!Suc p))   [the lemma]
  sub-claims: same-copy side <= Suc(snd(X!p))?  next-copy side: e1 = e1j1?
              <= snd(X!p)?
"""
import sys
sys.path.insert(0, '.')
from collections import Counter
from mine_sibm2 import bad_params
from fast_pss import oper, entry, Lng
from wfe_explore import enum_ST

def main():
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
    print('hosts:', len(out), flush=True)
    nwin = 0
    cls = Counter()
    viol = Counter()
    for Mt in out:
        M = list(Mt)
        bp = bad_params(M)
        if bp is None: continue
        j0, j1, i1, d0 = bp
        L = j1 - j0
        if L <= 0: continue
        for n in (2, 3):
            X = M[:j0] + [(entry(M,0,j)+k*d0, entry(M,1,j)) for k in range(n) for j in range(j0, j1)]
            lenX = len(X)
            for p in range(j0, lenX - 1):
                if (p - j0) % L == 0: continue
                qP = (p - j0) % L
                kp = (p - j0) // L
                cross = j0 + (kp + 1) * L
                # find max window: dom run from p
                e = p + 1
                while e < lenX and X[e][0] > X[p][0]:
                    e += 1
                if e >= lenX: continue   # need bounded window... actually window is (p, e)
                # premises: need stop cl: fst(X!(Suc p + t)) <= fst(X!Suc p) for some t in (0, N]
                # use full dominated run: N = e - p - 1; require crossing premise
                N = e - 1 - (p + 1) + 1  # count of elements after Suc p... align: Suc p + N < lenX, dom to Suc p + N
                SpN = e - 1
                if SpN <= p + 1: continue
                # cl: exists t: take minimal t with fst <= fst(X!Suc p)
                tt = None
                for t in range(1, SpN - p):
                    if X[p + 1 + t][0] <= X[p + 1][0]:
                        tt = t; break
                if tt is None: continue
                if not cross <= SpN: continue
                nwin += 1
                bound = max(X[p][1], X[p+1][1])
                for l in range(p + 1, SpN + 1):
                    side = ('same' if l < cross else
                            'next' if l < cross + L else 'far')
                    ok = X[l][1] <= bound
                    cls[(side, ok)] += 1
                    if not ok:
                        viol[side] += 1
                    if side == 'next':
                        q2 = (l - j0) % L
                        cls[('next-e1j1', X[l][1] == entry(M,1,j1))] += 1
                        cls[('next-le-p', X[l][1] <= X[p][1])] += 1
    print('windows:', nwin)
    for k, v in sorted(cls.items(), key=lambda kv: (str(kv[0]))):
        print(f'{v:7d}  {k}')
    print('violations by side:', dict(viol))

if __name__ == '__main__':
    main()
