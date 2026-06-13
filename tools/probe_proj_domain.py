#!/usr/bin/env python3
"""Determine the DOMAIN of proj_mono (design §5.1): does
   b <T b'  =>  proj u b <=T proj u b'
hold for ALL Three terms, or only for wf3 (in_OT) terms?

nrm always calls proj on `nrm b` which is wf3, so wf3-only suffices for the
Lean proof -- but knowing whether it holds unconditionally tells us if the Lean
lemma needs a hypothesis. Enumerate small conv-form terms, split by in_OT.
"""
import sys
sys.path.insert(0, '.')
from valnorm import conv, lt_term, le_term, G as Gset, in_OT

def proj(u, b):
    bb = b
    while True:
        bad = [g for g in Gset(u, bb) if not lt_term(g, bb)]
        if not bad: break
        g = bad[0]
        for h in bad[1:]:
            if lt_term(g, h): g = h
        bb = g
    return bb

def enum_terms(depth, maxlevel):
    """all conv-form terms up to nesting `depth`, levels 0..maxlevel,
    sums of up to 2 principals."""
    if depth == 0:
        return [()]
    sub = enum_terms(depth-1, maxlevel)
    princ = [('D', a, b) for a in range(maxlevel+1) for b in sub]
    out = [()]
    for p in princ:
        out.append((p,))
        for q in princ:
            out.append((p, q))
    # dedup
    seen = []; ss = set()
    for t in out:
        if t not in ss: ss.add(t); seen.append(t)
    return seen

if __name__ == '__main__':
    depth = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    maxlevel = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    terms = enum_terms(depth, maxlevel)
    wf = [t for t in terms if in_OT(t)]
    print(f'terms={len(terms)}  wf3={len(wf)}  levels=0..{maxlevel} depth={depth}')

    for label, dom in (('ALL', terms), ('WF3', wf)):
        viol = []; ck = 0
        for u in range(maxlevel+1):
            for i in range(len(dom)):
                pi = proj(u, dom[i])
                for j in range(len(dom)):
                    if i == j: continue
                    if lt_term(dom[i], dom[j]):
                        ck += 1
                        if not le_term(pi, proj(u, dom[j])):
                            viol.append((u, dom[i], dom[j]))
        print(f'[{label}] proj_mono checked={ck} violations={len(viol)}')
        for v in viol[:8]:
            print('   REVERSAL u=%d  b=%s  b\'=%s  proj b=%s  proj b\'=%s'
                  % (v[0], v[1], v[2], proj(v[0], v[1]), proj(v[0], v[2])))
