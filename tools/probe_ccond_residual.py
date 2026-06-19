#!/usr/bin/env python3
"""Validate the residual cnf_Ccond and its TRUTH (lighter corpus, finishes fast).

cnf_Ccond:  cnf (P a' b' c')  ==>  oV b' in C_a'(oV b')   [C-membership]

(1) On RAW NF args this FAILS (the gap) -- count.
(2) The collapse identity that closes it:  psi(oV b') a' == psi(proj_{a'}(oV b')) a',
    where proj is the value-level Buchholz projection.  We confirm the projected
    argument IS C-canonical (proj is a fixpoint of project), so psi_strict_mono_arg
    applies to it.  And projected-arg MONOTONICITY:
       olt b f (same subscript a) ==> proj_a(oVb) < proj_a(oVf).
    These two => oV_mono holds for the arg case even when raw C-membership fails.
"""
import sys, itertools
sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from wfe_explore import translate, olt, fmt, enum_ST, maxsub
from valnorm import conv, nrm, lt_term, fmtb, G

Z=()
def name(t): return nrm(conv(t))
def project(a, nm):
    bb=nm
    while True:
        bad=[g for g in G(a,bb) if not lt_term(g,bb)]
        if not bad: break
        g=bad[0]
        for h in bad[1:]:
            if lt_term(g,h): g=h
        bb=g
    return bb
def is_Ccanon(a, nm):
    """oV-name nm is C_a-canonical iff project fixes it iff all G_a members < nm."""
    return project(a,nm)==nm

def main():
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3), max_len=12, rounds=5)
    seen=set(); NF=[]
    for M in ST:
        t=translate(M)
        if t not in seen: seen.add(t); NF.append(t)
    print(f"#NF terms (light corpus): {len(NF)}")

    # collect distinct (a, name b) arg nodes
    uniq={}
    def collect(t):
        if t==Z: return
        a,b,c=t
        uniq[(a,name(b))]=(a,b)
        collect(b); collect(c)
    for t in NF: collect(t)
    items=list(uniq.values())
    print(f"#distinct arg nodes (a, oVname b): {len(items)}")

    # (1) raw C-membership failures
    cfail=0
    for a,b in items:
        if not is_Ccanon(a,name(b)): cfail+=1
    print(f"(1) raw C-membership FAILS on {cfail}/{len(items)} arg nodes  (= the gap cnf_Ccond bridges)")

    # (2a) projection lands in C (fixpoint) -- always
    pjok=sum(1 for a,b in items if is_Ccanon(a, project(a,name(b))))
    print(f"(2a) projected arg IS C-canonical: {pjok}/{len(items)}  (must = all)")

    # (2b) projected-arg strict monotonicity, same subscript
    from collections import defaultdict
    bya=defaultdict(list)
    for a,b in items: bya[a].append(b)
    tested=0; viol=0; ex=[]
    for a,bs in bya.items():
        for b,f in itertools.permutations(bs,2):
            if not olt(b,f): continue
            tested+=1
            pb=project(a,name(b)); pf=project(a,name(f))
            if pb==pf or lt_term(pf,pb):
                viol+=1
                if len(ex)<6: ex.append((a,b,f,pb,pf))
    print(f"(2b) projected-arg strict mono [olt b f => proj_a oVb < proj_a oVf]: tested={tested} VIOL={viol}")
    for a,b,f,pb,pf in ex:
        print(f"   a={a} b={fmt(b)} f={fmt(f)} pb={fmtb(pb)} pf={fmtb(pf)}")

if __name__=="__main__":
    main()
