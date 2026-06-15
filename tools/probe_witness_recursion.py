#!/usr/bin/env python3
"""Re-verify EXACT Lean statements for the witness recursion, closure+5/+6.

The witness lemma (verified): firing NF args b,f (head-0 args, so b=P1 b' c',
f=P1 f' d'), olt b f => exists h in Gterm0 f, olt(proj0 b) h.

Recursion steps to confirm in their EXACT Lean form:

S1 head-arg descent (the load-bearing step):
   olt b f, both fire, NF  =>  olt b' f'   (b=P1 b' c', f=P1 f' d')
   -- confirm zero tail-resolution AND confirm it needs NF (false off-class).

S2 witness-in-head:  the witness h is in {f'} ∪ Gterm0 f'  (never the tail d').

S3 RECURSIVE witness:  the witness for (b,f) is obtainable from (b',f'):
   Either olt (proj0 b) f'  (f' itself works), OR
   recurse: a witness h' in Gterm0 f' with olt (proj0 b) h'.
   Precisely: exists h in {f'} ∪ Gterm0 f' with olt (proj0 b) h.
   AND the recursion is on (proj0-of-head):  is proj0 b <=o proj0 b'-ish so that
   IH on (b',f') -- which compares proj0 b' vs ... -- lifts?

   The CLEAN recursive claim to test:
     W(x,y): x<o y, [class] => exists h in {y_arg} ∪ Gterm0 y_arg with olt (proj0_of_host x) h
   But proj0 b (host) vs proj0 b' (head arg) differ.  Let's find the RIGHT IH.

S4 closed form:  proj0 (P1 b' c') = max_olt(M1, M2) where
     M1 = (proj0 b' if pfire0 b' else b')   [included gmax of head arg]
     M2 = gmax0 c'  (greatest 0-critical of tail, or absent)
   Re-confirm in the form usable in Lean.

KEY new test S5 -- the actual recursion that closes it:
   Since proj0 b = max_olt(M1(b'), M2(c')) and we need h in Gterm0 f with
   olt (proj0 b) h:  it suffices to dominate BOTH M1(b') and M2(c').
   Claim: olt M1(b') (something in Gterm0 f) and olt M2(c') (something), OR
   the max itself is dominated by f' or a head critical of f.
   Test: olt (proj0 b) f'  fraction; and when NOT, is proj0 b dominated by a
   critical strictly inside f' (recurse on f')?
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import translate, enum_ST, olt, maxsub, spine
Z = ()
def le(s, t): return s == t or olt(s, t)
def lead(t): return 0 if t==Z else t[0]
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
def gmax0(t):
    G=Gterm(0,t)
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

    # S1: head-arg descent on firing pairs.  EXACT: both P1 (lead 1).
    s1_tot=s1_ok=s1_tail=0
    notP1=0
    for b in fire:
        if lead(b)!=1: notP1+=1
    for b in fire:
        for f in fire:
            if not olt(b,f): continue
            assert lead(b)==1 and lead(f)==1
            s1_tot+=1
            bp=b[1]; fp=f[1]
            if olt(bp,fp): s1_ok+=1
            elif bp==fp: s1_tail+=1
    print(f"firing args not lead-1: {notP1} (expect 0)")
    print(f"S1 head-arg descent olt b' f': {s1_ok}/{s1_tot}, tail(b'=f'): {s1_tail}")

    # S4 closed form
    s4_ok=s4_tot=0
    for b in fire:
        if lead(b)!=1: continue
        s4_tot+=1
        bp,cp=b[1],b[2]
        M1 = proj(0,bp) if pfire(0,bp) else bp
        M2 = gmax0(cp)
        cf = M1 if M2 is None else (M1 if le(M2,M1) else M2)
        if cf==proj(0,b): s4_ok+=1
    print(f"S4 closed form proj0(P1 b' c')=max(M1,M2): {s4_ok}/{s4_tot}")

    # S5 the recursion: olt(proj0 b) f' fraction, and when not, witness inside f'
    s5_fp=s5_inner=s5_tot=0
    for b in fire:
        pb=proj(0,b)
        for f in fire:
            if not olt(b,f): continue
            s5_tot+=1
            fp=f[1]
            if olt(pb,fp): s5_fp+=1
            elif any(olt(pb,h) for h in Gterm(0,fp)): s5_inner+=1
            else:
                pass  # neither -> would break recursion
    print(f"S5 olt(proj0 b) f': {s5_fp}; else witness inside Gterm0 f': {s5_inner}; "
          f"sum {s5_fp+s5_inner}/{s5_tot}")

    # S6 -- the IH shape: when olt(proj0 b) f' FAILS, we recurse to (?,f').
    #   we need: exists h in Gterm0 f' with olt(proj0 b) h.  Is proj0 b related to
    #   a 'host' whose head arg descends to compare with f'?  Test the cleanest IH:
    #   olt (proj0 b) (proj0 f) and proj0 f in {f'}∪Gterm0 f' part?  Actually
    #   test: is the GLOBAL witness h = a critical reachable by descending f's
    #   leading .b-chain until lead exceeds lead(proj0 b) or structural-dominates?
    # Test recursion termination measure: tsize f' < tsize f always.
    print("(tsize f' < tsize f trivially; recursion well-founded on tsize)")

if __name__ == '__main__':
    main()
