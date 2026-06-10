#!/usr/bin/env python3
"""Closure+1 audit of the sorry-class miners (memo 続29 lesson: the sibm
falsity was invisible because violations first appear one oper step beyond
the sampled closure).  Monkey-patch each miner's enum_ST with a closure+1
wrapper and re-run its main().
"""
import sys, importlib, traceback
sys.path.insert(0, '.')
import wfe_explore
from fast_pss import oper, Lng

_orig = wfe_explore.enum_ST

def plus1(seed_max_v=3, oper_ns=(1,2,3), max_len=11, rounds=4):
    base = _orig(seed_max_v=seed_max_v, oper_ns=oper_ns,
                 max_len=max_len, rounds=rounds)
    out = set(base)
    for M in base:
        if Lng(M) <= 1: continue
        for n in oper_ns:
            out.add(tuple(oper(list(M), n)))
    print('[audit] closure %d -> +1 %d hosts' % (len(base), len(out)))
    return out

def main():
    targets = sys.argv[1:] or ['mine_lpl', 'mine_nbc', 'mine_seam',
                               'mine_fire5', 'mine_master', 'mine_ntdom']
    for name in targets:
        print('############ %s (closure+1) ############' % name, flush=True)
        try:
            mod = importlib.import_module(name)
            mod.enum_ST = plus1
            mod.main()
        except Exception:
            traceback.print_exc()
        print(flush=True)

if __name__ == '__main__':
    main()
