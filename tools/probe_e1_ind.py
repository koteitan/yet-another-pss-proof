#!/usr/bin/env python3
"""Find an inductive proof of E1 (critical embedding) for firing NF args, OR a
more direct route to proj0 b <=o proj0 f.

NF head-0 args b: shape P 1 b' c' when firing (lead=1).  Criticals Gterm0 b
include b' (the head arg) and deeper.  Test:

  A) Is E1 actually equivalent to a SIMPLER monotone fact:
     'the greatest critical proj0 is olt-monotone' -- circular with goal.

  B) STRUCTURAL: olt b f on NF args.  Use NF_lead0 etc.  Both lead 1 (firing).
     b = P 1 b' c', f = P 1 f' d'.  olt b f => (b'<o f') or (b'=f' & c'<o d')
     [since leads equal =1].  Does proj0 b <=o proj0 f reduce to recursion on
     (b',c') vs (f',d')?  proj0 (P1 b' c') = ?  relate to proj0 of b'/c'.

  C) KEY: proj0 of P1 b' c': its criticals at level 0 are b' (since 0<=1),
     Gterm0 b', and Gterm0 c'.  The greatest critical = max of these.
     Is proj0 (P1 b' c') = max(proj-ish of b', c')?  Probe structure.

  D) Most promising for Lean: prove proj0_bothfire_NF by strong induction on
     tsize b.  Inductive hyp: for smaller NF args, proj0 monotone.  Need to
     express proj0 b via proj0 of SMALLER args.  Does proj0(P1 b' c') relate to
     proj0 b' and proj0 c' by a max/recursion?
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import translate, enum_ST, olt, maxsub, spine
Z = ()
def le(s, t): return s == t or olt(s, t)
def tsize(t):
    if t==Z: return 1
    return 1+tsize(t[1])+tsize(t[2])
def Gterm(u, t):
    if t == Z: return []
    a, b, c = t; out = []
    if u <= a: out.append(b); out += Gterm(u, b)
    out += Gterm(u, c); return out
def pfire(u, b): return any(not olt(g, b) for g in Gterm(u, b))
def proj(u, b):
    while True:
        bad = [g for g in Gterm(u, b) if not olt(g, b)]
        if not bad: return b
        m = bad[0]
        for h in bad[1:]:
            if olt(m, h): m = h
        b = m
def gmax(u,t):
    """greatest critical (or None)"""
    G=Gterm(u,t)
    if not G: return None
    m=G[0]
    for h in G[1:]:
        if olt(m,h): m=h
    return m

def main():
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=14, rounds=8)
    NF = sorted({translate(M) for M in ST}, key=str)
    args = sorted({t[1] for t in NF if t != Z and t[0] == 0}, key=str)
    fire = [b for b in args if pfire(0, b)]

    # C: proj0 b vs gmax. is proj0 b = greatest critical (gmax 0 b)? should be
    pb_eq_gmax=0; tot=0
    for b in fire:
        tot+=1
        if proj(0,b)==gmax(0,b): pb_eq_gmax+=1
    print(f"firing args {tot}: proj0 b == gmax(0,b): {pb_eq_gmax}")

    # B: firing args shape P 1 b' c' ; proj0 b vs proj0 b', proj0 c'
    # is proj0(P1 b' c') = max_olt(proj0 b' if fires.., b', proj0 c'..)?
    # simpler: greatest critical of P1 b' c' at level 0
    #   = max over {b'} ∪ Gterm0 b' ∪ Gterm0 c'.  = max(gmax-incl b', gmax0 c')
    # check: gmax0(P1 b' c') = the olt-max of (b' or its crit) and (c' crit).
    shape_ok=0; sf=0
    for b in fire:
        if b==Z or b[0]!=1: continue
        sf+=1
        _,bp,cp = b
        # candidates for greatest critical
        cands=[bp]+Gterm(0,bp)+Gterm(0,cp)
        m=cands[0]
        for h in cands[1:]:
            if olt(m,h): m=h
        if m==gmax(0,b): shape_ok+=1
    print(f"firing P1 args {sf}: gmax decomposition consistent {shape_ok}")

    # D: recursion measure -- on olt b f (both P1), reduce to b' vs f'
    # count: olt b f with b=P1 b' c', f=P1 f' d'.  cases:
    #   b'<o f' : does proj0 b <=o proj0 f follow from 'b' contributes <=o f' side'?
    #   b'=f' & c'<o d'
    rec={'bp_lt_fp':0,'bp_eq_fp':0,'other':0}
    for b in fire:
        if b[0]!=1: continue
        _,bp,cp=b
        for f in fire:
            if f[0]!=1 or not olt(b,f): continue
            _,fp,dp=f
            if olt(bp,fp): rec['bp_lt_fp']+=1
            elif bp==fp: rec['bp_eq_fp']+=1
            else: rec['other']+=1
    print(f"olt b f (both P1) decomposition: {rec}")

if __name__ == '__main__':
    main()
