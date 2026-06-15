#!/usr/bin/env python3
"""Test the hypothesis NF subseteq wf3, i.e. every translate(M) for M in ST_PS
is a Buchholz OT term (wf3).  If TRUE, oV_mono_NF reduces to oV_order_pres.

Models the Isabelle defs exactly:
  Gterm u Z = {}
  Gterm u (P a b c) = (if u<=a then {b} | Gterm u b else {}) | Gterm u c
  hdle Z y = True; hdle (P..) Z = False;
  hdle (P a b c)(P e f g) = a<e or (a=e and (olt b f or b=f))
  wf3 Z = True
  wf3 (P a b c) = wf3 b & wf3 c & (forall x in Gterm a b. olt x b) & hdle c (P a b Z)
"""
import sys; sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from wfe_explore import translate, olt, fmt, enum_ST, maxsub

Z = ()

def Gterm(u, t):
    if t == Z: return []
    a,b,c = t
    res = []
    if u <= a:
        res.append(b)
        res += Gterm(u, b)
    res += Gterm(u, c)
    return res

def hdle(s, t):
    if s == Z: return True
    if t == Z: return False
    a,b,c = s; e,f,g = t
    return a < e or (a == e and (olt(b,f) or b == f))

def wf3(t):
    if t == Z: return True
    a,b,c = t
    if not wf3(b): return False
    if not wf3(c): return False
    for x in Gterm(a,b):
        if not olt(x,b): return False
    if not hdle(c, (a,b,Z)): return False
    return True

def main():
    # Deep closure of ST_PS
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4,5), max_len=18, rounds=7)
    print(f"#ST_PS enumerated: {len(ST)}")
    viol = 0; tot = 0; ex = []
    maxlevel = 0
    for M in ST:
        t = translate(M)
        maxlevel = max(maxlevel, maxsub(t))
        tot += 1
        if not wf3(t):
            viol += 1
            if len(ex) < 10:
                ex.append((M, t))
    print(f"max maxsub level reached: {maxlevel}")
    print(f"NF terms tested: {tot}  wf3-VIOLATIONS: {viol}")
    for M,t in ex:
        fm = lambda X: ''.join('(%d,%d)'%(a,b) for a,b in X)
        print("  VIOL M=", fm(M), " translate=", fmt(t))
        # show which subterm fails
        def find(t):
            if t==Z: return
            a,b,c=t
            for x in Gterm(a,b):
                if not olt(x,b):
                    print("     OT3 fail at P%d(%s): x=%s not < b=%s"%(a,fmt(b),fmt(x),fmt(b)))
            if not hdle(c,(a,b,Z)):
                print("     hdle fail: c=%s not <= head P%d(%s)"%(fmt(c),a,fmt(b)))
            find(b); find(c)
        find(t)

if __name__ == "__main__":
    main()
