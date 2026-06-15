#!/usr/bin/env python3
"""Nail the EXACT recursive witness lemma, induction on f.

Facts: p := proj0 b.  f <o p ... wait check sign on ALL firing pairs (not just eq).
Witness h in f's .b-chain (head-arg chain), h in Gterm0 f, olt p h.

The recursion on f = P1 f' d':
  Gterm0 f = {f'} ∪ Gterm0 f' ∪ Gterm0 d'.  The witness is in {f'}∪Gterm0 f'
  (head part), specifically on f's .b-chain = [f', f'.b, f'.b.b, ...].
  Note f' = f.b, and f.b-chain nodes after f' are f'.b, ... which are in Gterm0 f'.

  So WITREC reduces to: find h in {f'} ∪ (f'-chain) with olt p h.
  Step: either olt p f'  (DONE, h=f'),  OR  recurse on f' to find h in
        f'-chain with olt p h.  Recursion measure: tsize f' < tsize f.

  The recursion needs NO hypothesis linking p to f' beyond: SOME node of f's
  chain dominates p.  But to PROVE existence we need a reason.  The reason:
  olt b f and the chains align (S1: b'<o f', recursively).

  CLEAN inductive lemma candidate (induction on f's chain depth):
    LEM: for firing NF args b,f with olt b f:
         olt (proj0 b) f'  OR  [recurse: b' , f' give olt(proj0 b') f''...]
    -- but proj0 b vs proj0 b' differ.

  Test the SIMPLEST sufficient recursive fact:
    A) olt (proj0 b) f'  when  maxsub b < maxsub f'  (lead of proj0 b = maxsub b)
       -- is lead f' related to maxsub b?  test maxsub b vs lead f'.
    B) when olt(proj0 b) f' fails, recurse with the SAME b but smaller f' :
       i.e. the lemma 'exists h in f's chain with olt (proj0 b) h' is monotone:
       proved by induction on f alone (b fixed), using: f is a firing NF arg,
       proj0 b is a fixed critical with lead = maxsub b, and the chain of f
       eventually exceeds it because maxsub f >= maxsub b and the chain realizes
       increasing structure.
  Test B's engine:  is there ALWAYS a chain node fn of f with
     lead fn > maxsub b  OR (lead fn = maxsub b AND fn structurally > proj0 b)?
  Simpler robust test:  the chain node f' (=f.b): compare (lead f', then deeper).
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

def main():
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=14, rounds=8)
    NF = sorted({translate(M) for M in ST}, key=str)
    args = sorted({t[1] for t in NF if t != Z and t[0] == 0}, key=str)
    fire = [b for b in args if pfire(0, b)]

    # sign of f vs proj0 b on ALL firing pairs
    f_lt_p=p_lt_f=eq=tot=0
    for b in fire:
        pb=proj(0,b)
        for f in fire:
            if not olt(b,f): continue
            tot+=1
            if olt(f,pb): f_lt_p+=1
            elif olt(pb,f): p_lt_f+=1
            else: eq+=1
    print(f"ALL firing pairs: f<o proj0 b {f_lt_p}, proj0 b<o f {p_lt_f}, eq {eq} /{tot}")

    # The recursion engine B: descend f.b-chain; find first node dominating proj0 b.
    # h in chain, olt(proj0 b) h.  Confirm exists for all; report MAX depth needed.
    def chain(t):  # [t.b, t.b.b, ...] = head-arg chain (all in Gterm0 t)
        out=[]; cur=t[1] if t!=Z else Z
        while cur!=Z:
            out.append(cur); cur=cur[1]
        return out
    maxdepth=0; allok=0; tot2=0
    for b in fire:
        pb=proj(0,b)
        for f in fire:
            if not olt(b,f): continue
            tot2+=1
            ch=chain(f)
            d=None
            for i,n in enumerate(ch):
                if olt(pb,n): d=i; break
            if d is not None:
                allok+=1; maxdepth=max(maxdepth,d)
    print(f"witness on f.b-chain: {allok}/{tot2}, max depth index {maxdepth}")

    # The KEY recursive sufficient condition for h = f' (depth 0):
    #   olt (proj0 b) f'  iff ?  decompose: lead(proj0 b)=maxsub b=:kb, lead f'=:lf
    #   olt p f' holds when kb < lf, OR kb=lf & deeper.  When it FAILS (kb>lf or
    #   kb=lf & p>=f'), recurse to f'.b chain.  Test the recursion correctness:
    #   when olt p f' FAILS, is olt b' f'  STILL giving a smaller instance with
    #   f replaced by ... hmm.  Test: when NOT olt(p,f'), do we have lead f' <= kb,
    #   and a DEEPER node f'' with olt p f''?
    fail_recurse_ok=0; fail_tot=0
    for b in fire:
        pb=proj(0,b)
        for f in fire:
            if not olt(b,f): continue
            fp=f[1]
            if olt(pb,fp): continue
            fail_tot+=1
            ch=chain(f)[1:]  # deeper nodes
            if any(olt(pb,n) for n in ch): fail_recurse_ok+=1
    print(f"when olt(p,f') fails ({fail_tot}): deeper chain node works {fail_recurse_ok}")

if __name__ == '__main__':
    main()
