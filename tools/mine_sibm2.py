#!/usr/bin/env python3
"""Run-stop geography for sibm_oper_bad.

For X = oper(M,n) in the bad branch (X = take j0 M @ copies of block [j0,j1)),
enumerate adjacent tie-sibling pairs (a,b) of X (b = stop of a's run, equal
level>0 and equal row1) and record, per pair category
  P  = position < j0 (prefix), Ck = copy k (offset q),
where the runs of a and b STOP relative to the region boundaries:
  stop < j0 / inside copy k at offset q / end-of-X (None).

Questions:
 Q1 PP pairs: can b's run reach j1 (= start of copy1)?  end of X?
 Q2 PC pairs: where exactly is b (copy,offset), where do both runs stop?
 Q3 CC-same: does b's run stay in the copy?  cross into next copy?
 Q4 CC-adjacent: offsets of a and b; both-run stops.
 Q5 does any category beyond {PP,PC,CC same,CC+1} occur?
"""
import sys
sys.path.insert(0, '.')
from collections import Counter, defaultdict
from fast_pss import (Lng, entry, oper, diagSeq, idx1,
                      hasParent0, hasParent1, parent0, parent1, fmt)
from wfe_explore import enum_ST

def bad_params(M):
    """Return (j0,j1,i1,d0) if oper takes the bad branch, else None."""
    j1 = Lng(M) - 1
    if j1 == 0: return None
    if entry(M,0,j1) == 0 and entry(M,1,j1) == 0: return None
    i1 = idx1(M, j1)
    if i1 == 1:
        if not hasParent1(M, j1): return None
        j0 = parent1(M, j1)
    else:
        if not hasParent0(M, j1): return None
        j0 = parent0(M, j1)
    d0 = (entry(M,0,j1) - entry(M,0,j0)) if i1 > 0 else 0
    return (j0, j1, i1, d0)

def mrun_stop(X, a):
    """First position c > a with lev(c) <= lev(a), or None."""
    la = X[a][0]
    for c in range(a+1, len(X)):
        if X[c][0] <= la: return c
    return None

def region(p, j0, L):
    if p < j0: return ('P', None, None)
    k, q = divmod(p - j0, L)
    return ('C', k, q)

def main():
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=13, rounds=7)
    cats = Counter()
    runstop = defaultdict(Counter)
    bad = []
    npairs = 0
    for M in ST:
        bp = bad_params(list(M))
        if bp is None: continue
        j0, j1, i1, d0 = bp
        L = j1 - j0
        for n in range(1, 5):
            X = oper(list(M), n)
            lenX = len(X)
            assert lenX == j0 + n*L
            for a in range(lenX):
                if X[a][0] <= 0: continue
                b = mrun_stop(X, a)
                if b is None: continue
                if X[b][0] != X[a][0] or X[b][1] != X[a][1]: continue
                npairs += 1
                ra, rb = region(a, j0, L), region(b, j0, L)
                c = mrun_stop(X, b)
                rc = None if c is None else region(c, j0, L)
                # category key
                if ra[0]=='P' and rb[0]=='P': cat='PP'
                elif ra[0]=='P': cat=f'PC{rb[1]}'
                elif rb[0]=='C' and ra[0]=='C':
                    dk = rb[1]-ra[1]
                    cat = f'CC+{dk}'
                else: cat='??'
                cats[(cat,)] += 1
                # run-stop geography per category
                def stoptag(r, c):
                    if c is None: return 'END'
                    if r[0]=='P': return 'P'
                    return f'C{r[1]}@{"hd" if r[2]==0 else "mid"}'
                # b-run stop relative to b's own region
                if cat=='PP':
                    # Q1: does b's run pass j0? reach j1?
                    if c is None: tag='END'
                    elif c < j0: tag='stop<j0'
                    elif c < j1: tag='stop in copy0'
                    else:
                        kk,qq = divmod(c-j0, L)
                        tag=f'stop C{kk}@{qq}'
                    runstop['PP'][ (n>1, tag) ] += 1
                    if c is not None and c >= j1 and n>1:
                        bad.append(('PPdeep', fmt(M), n, a, b, c))
                elif cat.startswith('PC'):
                    kb,qb = rb[1], rb[2]
                    if c is None: tag='END'
                    else:
                        kk,qq=region(c,j0,L)[1:],None
                    tag = stoptag(rc, c)
                    runstop[f'PC b@C{kb}o{qb}'][ (n, tag) ] += 1
                elif cat=='CC+0':
                    qa, qb = ra[2], rb[2]
                    tag = stoptag(rc, c)
                    # does b's run leave the copy?
                    leave = 'in-copy'
                    if c is None: leave='END'
                    elif rc[0]=='P': leave='P!?'
                    elif rc[1] != rb[1]: leave=f'leave+{rc[1]-rb[1]}'
                    runstop['CCsame'][ (qa-0>=0 and 'qa>0' if qa>0 else 'qa=0', f'qb={qb}' if qb<3 else 'qb>=3', leave) ] += 1
                elif cat=='CC+1':
                    qa, qb = ra[2], rb[2]
                    tag = stoptag(rc, c)
                    runstop['CCadj'][ (f'qa={qa}' if qa<3 else 'qa>=3', f'qb={qb}' if qb<3 else 'qb>=3', tag if c is None else ('stop+%d'%(rc[1]-rb[1]) if rc[0]=='C' else 'P!?')) ] += 1
                else:
                    bad.append((cat, fmt(M), n, a, b, c))
    print('total tie pairs:', npairs)
    print('categories:', dict(cats))
    for k in sorted(runstop):
        print(f'--- {k} ---')
        for kk, v in sorted(runstop[k].items(), key=lambda t:-t[1]):
            print('   ', kk, v)
    print('anomalies:', len(bad))
    for t in bad[:20]: print('  ', t)

if __name__ == '__main__':
    main()
