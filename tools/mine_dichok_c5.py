#!/usr/bin/env python3
"""Verify dichOK (edge dichotomy) on ya-pss reachable hosts at deep closure:
  forall p q t: nextrel1 M p t and le0 M p q and q<t and 0<snd(M!q)
    ==> le0 M q t  or  M!q == M!t
Usage: mine_dichok_c5.py [extra]
"""
import sys
sys.path.insert(0, '.')
from fast_pss import oper, nextrel1, le0
from wfe_explore import enum_ST

def hosts_plus(extra):
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=13, rounds=7)
    out = set(ST); cur = list(out)
    for i in range(extra):
        new = []
        for M in cur:
            if len(M) < 2: continue
            for n in (1,2,3,4):
                t = tuple(oper(list(M), n))
                if t not in out: out.add(t); new.append(t)
        cur = new
        print('  +%d total %d' % (i+1, len(out)), flush=True)
    return out

def main():
    extra = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    HS = hosts_plus(extra)
    print('hosts:', len(HS), flush=True)
    n = bad = 0; ex = []
    for Mt in HS:
        M = list(Mt); L = len(M)
        # find nextrel1 edges p->t
        for t in range(L):
            for p in range(t):
                if not nextrel1(M, p, t): continue
                # q with le0 p q, q<t, snd(M!q)>0
                for q in range(p, t):
                    if not le0(M, p, q): continue
                    if M[q][1] == 0: continue
                    if le0(M, q, t) or M[q] == M[t]: continue
                    n += 1; bad += 1
                    if len(ex) < 6: ex.append((p, q, t, Mt))
                # also count satisfied for sanity
    print(f'dichOK violations: {bad}')
    for p, q, t, M in ex:
        print('  fail p=%d q=%d t=%d M=%s' % (p, q, t,
              ''.join('(%d,%d)' % c for c in M)))

if __name__ == '__main__':
    main()
