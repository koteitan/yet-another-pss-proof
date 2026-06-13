#!/usr/bin/env python3
"""Deep audit (closure+5/+6) of the two live Lean obligations:

  (A) nrm_step_dec  : olt (nrm (translate (M[n]))) (nrm (translate M))
        -- the STEP-only decrease; SUFFICIENT for PSS_terminates_nrm.
  (B) nrm_order_pres: v,u in NF, olt v u  =>  olt (nrm v) (nrm u)
        -- the GENERAL order preservation; only used by the *alt* route.

Per soundness-discipline: the 7 prior false invariants all passed shallow
(closure+3) and first failed at +5/+6 (re-entry = audit-depth+1). The existing
"2,643,843 pairs, 0 collapse" validation used rounds=7,len<=13 -- shallow.
This pushes rounds (=closure depth) and max_len so re-entry hosts appear.
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import translate, olt, maxsub
from fast_pss import oper, diagSeq, Lng
from valnorm import conv, nrm, lt_term

def nrm3(t):
    """nrm of a Three term t, returned in conv'd (principal-list) form."""
    return nrm(conv(t))

def enum_with_depth(seed_max_v, oper_ns, max_len, rounds):
    """Like enum_ST but tracks closure depth of each host."""
    seen = {}
    frontier = []
    for v in range(seed_max_v+1):
        M = tuple(diagSeq(0, v))
        if M not in seen:
            seen[M] = 0; frontier.append(M)
    for r in range(rounds):
        nxt = []
        for M in frontier:
            if Lng(M) <= 1: continue
            for n in oper_ns:
                N = tuple(oper(list(M), n))
                if len(N) <= max_len and N not in seen:
                    seen[N] = r+1; nxt.append(N)
        frontier = nxt
        if not frontier: break
    return seen

def audit_step(seed_max_v, oper_ns, max_len, rounds):
    seen = enum_with_depth(seed_max_v, oper_ns, max_len, rounds)
    viol = []; checked = 0; maxdepth = 0
    for M, d in seen.items():
        maxdepth = max(maxdepth, d)
        if Lng(M) <= 1: continue
        for n in oper_ns:
            N = tuple(oper(list(M), n))
            if len(N) > max_len: continue
            tM = translate(M); tN = translate(N)
            # precondition (m_step_decreases, should always hold):
            if not olt(tN, tM):
                viol.append(('PRE-FAIL', M, n))
                continue
            checked += 1
            if not lt_term(nrm3(tN), nrm3(tM)):
                viol.append(('STEP', M, n, d))
    return checked, viol, maxdepth, len(seen)

def audit_general(seed_max_v, oper_ns, max_len, rounds, cap=400000):
    seen = enum_with_depth(seed_max_v, oper_ns, max_len, rounds)
    # group translates by maxsub level (the INJ experiment grouping)
    NF = {}
    for M, d in seen.items():
        w = translate(M)
        NF.setdefault(maxsub(w), []).append((w, conv(w), d))
    collapse = []; reversal = []; checked = 0
    for lvl, lst in NF.items():
        L = len(lst)
        for i in range(L):
            wi, ci, di = lst[i]
            ni = nrm(ci)
            for j in range(L):
                if i == j: continue
                wj, cj, dj = lst[j]
                if not olt(wi, wj): continue
                checked += 1
                if checked > cap:
                    return checked, collapse, reversal, True
                nj = nrm(cj)
                if ni == nj:
                    collapse.append((wi, wj, max(di, dj)))
                elif not lt_term(ni, nj):
                    reversal.append((wi, wj, max(di, dj)))
    return checked, collapse, reversal, False

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'step'
    smv = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    rounds = int(sys.argv[3]) if len(sys.argv) > 3 else 6
    mlen = int(sys.argv[4]) if len(sys.argv) > 4 else 28
    ns = (1, 2, 3)
    if mode == 'step':
        ck, vi, md, ns_ = audit_step(smv, ns, mlen, rounds)
        print(f'[STEP] seed_max_v={smv} rounds={rounds} max_len={mlen} '
              f'hosts={ns_} maxdepth={md} checked={ck} violations={len(vi)}')
        for v in vi[:20]:
            print('  ', v)
    else:
        ck, coll, rev, capped = audit_general(smv, ns, mlen, rounds)
        print(f'[GENERAL] seed_max_v={smv} rounds={rounds} max_len={mlen} '
              f'checked={ck} capped={capped} collapses={len(coll)} reversals={len(rev)}')
        for v in coll[:15]:
            print('  COLLAPSE', v)
        for v in rev[:15]:
            print('  REVERSAL', v)
