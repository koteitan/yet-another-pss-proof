#!/usr/bin/env python3
"""Where does the witness h (in Gterm0 f, olt(proj0 b) h) live, and is there a
clean recursive witness?

f = P1 f' d'.  Gterm0 f = {f'} ∪ Gterm0 f' ∪ Gterm0 d'.
b = P1 b' c'.  proj0 b on leading .b-chain.

Test recursive witness candidates:
  L1: h in {f'} ∪ Gterm0 f'  (head-arg part) suffices?  i.e. exists h in that
      subset with olt(proj0 b) h.
  L2: the SPECIFIC witness: relate proj0 b to f'.  Since olt b' f', and proj0 b
      is built from b' ... is olt (proj0 b) (proj0 f) reducible to a recursion:
      witness for (b,f) comes from witness for (b', f') lifted, OR f' itself.

  KEY recursion hypothesis WH:
    olt (proj0 b) f'  OR  (proj0 b in Gterm0 f' region via recursion on (b',f')).
  Test: define the would-be inductive claim
    CLAIM(x,y): x,y firing NF-ish, olt x y => exists h in Gterm0 y, olt (proj0 x) h.
  Reduce f's witness:  proj0 b leads with k=maxsub b<=maxsub f.
    case maxsub b < maxsub f: f' has lead... actually proj0 f leads maxsub f>k,
       and f' (head of f=P1 f' d') -- lead f' = maxsub f (NF spine!) ?  check.
    So lead f' = maxsub f.  If maxsub f > k = lead(proj0 b): olt(proj0 b) f' by lead!
    eqmaxsub: lead f' = maxsub f = k = lead(proj0 b); need deeper.

Test:
  T_leadfp: lead f' (head arg of firing f) == maxsub f ?
  T_L1: witness in {f'}∪Gterm0 f' suffices?
  T_strictmaxsub_fp: when maxsub b < maxsub f, does olt(proj0 b) f' hold (lead)?
  T_eqmaxsub_rec: when maxsub b = maxsub f, recurse: olt(proj0 b)(proj0 f) with
      witness from (b', f') -- check olt b' f' AND both fire AND ... the SAME claim
      on (b',f') smaller.
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

    # T_leadfp
    leadfp_eq=0; sf=0
    for f in fire:
        if f[0]!=1: continue
        sf+=1
        fp=f[1]
        if lead(fp)==maxsub(f): leadfp_eq+=1
    print(f"firing P1 {sf}: lead(head arg f') == maxsub f : {leadfp_eq}")

    L1=0; strictfp=0; eqrec=0; eqrec_ok=0; tot=0; eq_tot=0
    for b in fire:
        pb=proj(0,b)
        for f in fire:
            if not olt(b,f): continue
            tot+=1
            fp=f[1]
            headset=[fp]+Gterm(0,fp)
            if any(olt(pb,h) for h in headset): L1+=1
            if maxsub(b)<maxsub(f):
                if olt(pb, fp): strictfp+=1
            else:  # eqmaxsub
                eq_tot+=1
                # recurse on (b', f'): is olt b' f' and would CLAIM(b',f') give witness?
                bp=b[1]; fpp=f[1]
                if olt(bp, fpp): eqrec+=1
    print(f"firing pairs {tot}: witness in head part {{f'}}∪Gterm0 f': {L1}")
    msb_strict = sum(1 for b in fire for f in fire if olt(b,f) and maxsub(b)<maxsub(f))
    print(f"  strict-maxsub: olt(proj0 b) f'(head): {strictfp} / {msb_strict}")
    print(f"  eqmaxsub pairs: {eq_tot}, of which olt b' f' (recurse handle): {eqrec}")

if __name__ == '__main__':
    main()
