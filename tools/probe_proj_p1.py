#!/usr/bin/env python3
"""Closed form / recursion for proj0(P1 b' c') on firing NF args.
proj0 is greatest critical = on leading .b-chain, depends only on b'.

Test:
  P1: proj0(P1 b' c') == ?  among {b', proj0 b' (if b' fires at 0), b' itself}
  Since Gterm0(P1 b' c') = {b'} ∪ Gterm0 b' ∪ Gterm0 c', greatest critical:
    candidates: b' and greatest-crit(b') and greatest-crit(c').
  Hypothesis: proj0(P1 b' c') = max_olt(b', proj0 b' if pfire else b'? , ...)
  Simplest: gmax0(P1 b' c') = max_olt(gmax-incl(b'), gmax0(c')) where
    gmax-incl(b') = max_olt(b', gmax0(b')) = max(b', proj0 b' if fires else None)
  Test: is proj0(P1 b' c') = (b' if not pfire 0 b' AND b' dominates, else proj0 b')?
        i.e. = max_olt(b', proj0 b'-when-fires, proj0 c'-when-fires)
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import translate, enum_ST, olt, maxsub, spine
Z = ()
def le(s, t): return s == t or olt(s, t)
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
def omax(*xs):
    xs=[x for x in xs if x is not None]
    m=xs[0]
    for h in xs[1:]:
        if olt(m,h): m=h
    return m

def main():
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=14, rounds=8)
    NF = sorted({translate(M) for M in ST}, key=str)
    args = sorted({t[1] for t in NF if t != Z and t[0] == 0}, key=str)
    fire = [b for b in args if pfire(0, b)]

    # candidate closed form
    okA=okB=tot=0
    fail=[]
    for b in fire:
        if b[0]!=1: continue
        tot+=1
        _,bp,cp=b
        pb=proj(0,b)
        # crit of b' included as a 0-critical of b: b' itself, plus proj0 b' if b' fires
        gb_incl = omax(bp, proj(0,bp) if pfire(0,bp) else None)
        gc = proj(0,cp) if (cp!=Z and pfire(0,cp)) else (None)
        # also c' itself is NOT a 0-critical of P1 b' c' (c' is the tail, contributes
        # its OWN 0-criticals Gterm0 c', not c' itself).  So tail gives gmax0(c').
        gc0 = None
        Gc=Gterm(0,cp)
        if Gc:
            gc0=Gc[0]
            for h in Gc[1:]:
                if olt(gc0,h): gc0=h
        candA = omax(gb_incl, gc0) if gc0 is not None else gb_incl
        if candA==pb: okA+=1
        else:
            if len(fail)<6: fail.append((bp,cp,pb,candA))
    print(f"firing P1 {tot}: proj0 = max(gmax-incl b', gmax0 c'): {okA}")
    for f in fail: print("  FAIL b',c',proj0,cand=",f)

if __name__ == '__main__':
    main()
