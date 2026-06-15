#!/usr/bin/env python3
"""Strict witness for proj0 b <o proj0 f on firing NF pairs.

We have (verified): proj0 b <=o proj0 f, proj0 b != proj0 f, all firing pairs.
Need a Lean-provable STRICT argument.  Candidates:
  W1: EXISTS h in Gterm0 f with olt (proj0 b) h   (strict).  Then h<=o proj0 f
      (proj_ge_crit) gives olt(proj0 b)(proj0 f).  count pairs where such h exists.
  W2: olt b f, both P1: b=P1 b' c', f=P1 f' d', olt b' f'.  Is f' itself a
      critical of f with olt(proj0 b) f' ?  (f' in Gterm0 f since 0<=1).
      i.e. is proj0 b <o f' ?
  W3: is proj0 b <o f ?  (R2 said NO, 0).  skip.
  W4: the head arg f' of f: olt (proj0 b) f' ?  count.
  W5: combine -- the witness h = proj0 f works for <=o; for STRICT we need
      proj0 b strictly below SOME critical.  Since proj0 b <=o proj0 f and !=,
      proj0 b <o proj0 f directly (that's <=o + !=).  So if I can prove
      proj0 b <=o proj0 f AND proj0 b != proj0 f, done.  Focus W_NEQ: a clean
      reason proj0 b != proj0 f.  Test: lead2 (maxsub of head arg) or the
      head-arg of proj differ?
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

def main():
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=14, rounds=8)
    NF = sorted({translate(M) for M in ST}, key=str)
    args = sorted({t[1] for t in NF if t != Z and t[0] == 0}, key=str)
    fire = [b for b in args if pfire(0, b)]
    W1=W4=tot=0
    for b in fire:
        pb=proj(0,b)
        for f in fire:
            if not olt(b,f): continue
            tot+=1
            Gf=Gterm(0,f)
            if any(olt(pb,h) for h in Gf): W1+=1
            fp = f[1]  # head arg f' (f=P1 f' d')
            if olt(pb, fp): W4+=1
    print(f"firing pairs {tot}")
    print(f"W1 EXISTS h in Gterm0 f, olt(proj0 b) h : {W1}")
    print(f"W4 olt(proj0 b) f'(head arg of f)       : {W4}")

if __name__ == '__main__':
    main()
