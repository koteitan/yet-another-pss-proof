#!/usr/bin/env python3
"""THE crucial test for the OT2+value-OT3 route:

oV_order_pres needs, in the arg case, the C-membership of oV b, supplied by
Ccond_of_lt from:   for every x in Gterm a b (raw translate subterms),  oV x < oV b.

NF VIOLATES the SYNTACTIC OT3 (olt x b can fail). But we test the VALUE version:
   for every x in Gterm a b on the RAW translate term,  oV x < oV b  (ordinal <).

If this VALUE-OT3 holds hereditarily on NF, then Ccond_of_lt gives C-membership
and oV_order_pres's induction goes through with wf3 REPLACED by:
   ot2h (OT2 hereditary, already 0-viol) + value-OT3-hereditary.
Both proven 0-viol => oV_mono_NF closes for real.

oV proxy: nrm(conv(.)) with lt_term ordinal order.
Gterm on raw three-term exactly as Isabelle.
"""
import sys, itertools
sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from wfe_explore import translate, olt, fmt, enum_ST, maxsub
from valnorm import conv, nrm, lt_term, fmtb

Z=()
def oVkey(t): return nrm(conv(t))
def oVlt(s,t): return lt_term(oVkey(s),oVkey(t))
def oVeq(s,t): return oVkey(s)==oVkey(t)

def Gterm(u,t):
    if t==Z: return []
    a,b,c=t
    res=[]
    if u<=a:
        res.append(b); res+=Gterm(u,b)
    res+=Gterm(u,c)
    return res

def value_ot3_node(t):
    """at node P a b c: every x in Gterm a b has oV x < oV b (VALUE)."""
    if t==Z: return True
    a,b,c=t
    for x in Gterm(a,b):
        if not (oVlt(x,b)):   # require strict oV x < oV b
            return False
    return True

def value_ot3_all(t):
    if t==Z: return True
    a,b,c=t
    if not value_ot3_node(t): return False
    return value_ot3_all(b) and value_ot3_all(c)

def main():
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4,5), max_len=18, rounds=7)
    seen=set(); NF=[]
    for M in ST:
        t=translate(M)
        if t not in seen: seen.add(t); NF.append(t)
    print(f"#distinct NF terms: {len(NF)}  max maxsub={max(maxsub(t) for t in NF)}")

    viol=0; ex=[]; nodes=0
    for t in NF:
        if not value_ot3_all(t):
            viol+=1
            if len(ex)<10:
                # find the violating node
                def find(tt):
                    if tt==Z: return None
                    a,b,c=tt
                    for x in Gterm(a,b):
                        if not oVlt(x,b): return (tt,x,b)
                    return find(b) or find(c)
                ex.append((t,find(t)))
    print(f"[VALUE-OT3 hereditary on RAW translate, oV x < oV b for x in Gterm a b]")
    print(f"  NF terms VIOL = {viol}/{len(NF)}")
    for t,f in ex:
        if f:
            tt,x,b=f
            print(f"   t={fmt(t)}")
            print(f"      node={fmt(tt)} x={fmt(x)} (oV={fmtb(oVkey(x))}) b={fmt(b)} (oV={fmtb(oVkey(b))})")

    # also test with <= (in case some equal-value G members exist but strict needed)
    eqcnt=0
    for t in NF:
        def chk(tt):
            global_=0
            if tt==Z: return 0
            a,b,c=tt
            n=0
            for x in Gterm(a,b):
                if oVeq(x,b): n+=1
            return n+chk(b)+chk(c) if tt!=Z else 0
        eqcnt+=chk(t)
    print(f"  (#G-members with oV x == oV b across all nodes: {eqcnt})")

if __name__=="__main__":
    main()
