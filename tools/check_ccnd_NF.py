#!/usr/bin/env python3
"""Test the C-membership obligation ccnd on NF, in the genuine finite ordinal
collapse model (cset_remark_check.py): for each principal P a b c hereditarily
in an NF term (with subscripts <=2 so the model applies), is

    oV b  in  Cset(lambda xi. psi xi)(oV b) a    <=>    acanon a (oV b) ?

This is the SOLE step where oV_order_pres uses wf3.  If acanon a (oV b) holds on
ALL NF principals despite NF not being wf3, then ccnd transfers to NF and
oV_mono_NF's proof structure runs.  If it FAILS, the gap is real and located.
"""
import sys, importlib.util; sys.setrecursionlimit(1000000)
sys.path.insert(0,'.')
spec = importlib.util.spec_from_file_location("crc","cset_remark_check.py")
crc = importlib.util.module_from_spec(spec); spec.loader.exec_module(crc)
from wfe_explore import translate, enum_ST, fmt

Z=()
# oV on three-terms -> model ordinals
from functools import lru_cache
def oV(t):
    if t==Z: return crc.ZERO
    a,b,c=t
    p = crc.psi(oV(b), a)
    if p is None:
        raise ValueError("psi None: subscript/arg out of model range")
    return crc.oadd(p, oV(c))

def principals(t):
    if t==Z: return
    a,b,c=t
    yield (a,b,c)
    yield from principals(b)
    yield from principals(c)

def maxsub_all(t):
    if t==Z: return 0
    a,b,c=t
    return max(a,maxsub_all(b),maxsub_all(c))

def main():
    ST = enum_ST(seed_max_v=3,oper_ns=(1,2,3,4),max_len=14,rounds=7)
    NF = set(translate(M) for M in ST)
    # restrict to subscripts <=2 (model limit)
    NF2 = [t for t in NF if maxsub_all(t)<=2]
    print(f"#NF total={len(NF)}  #NF with subs<=2 (model-applicable)={len(NF2)}")
    # warm psi over all argument values we'll need
    args=set()
    def collect(t):
        if t==Z: return
        a,b,c=t; collect(b); collect(c)
        args.add(oV(b))
    bad_warm=0
    feas=[]
    for t in NF2:
        try:
            collect(t); feas.append(t)
        except ValueError:
            bad_warm+=1
    print(f"feasible NF terms (all psi defined): {len(feas)}  (skipped {bad_warm} out-of-model)")
    crc.warm_psi(list(args))

    checks=0; viol=0; ex=[]
    seenpr=set()
    for t in feas:
        for (a,b,c) in principals(t):
            ob=oV(b)
            key=(a,ob)
            if key in seenpr: continue
            seenpr.add(key)
            checks+=1
            if not crc.acanon(a, ob):
                viol+=1
                if len(ex)<12: ex.append((a,b,ob))
    print(f"ccnd C-membership checks (distinct (a,oV b)): {checks}")
    print(f"  ★ acanon a (oV b) FAILS on NF principal: {viol}")
    for a,b,ob in ex:
        print(f"   VIOL a={a}  b={fmt(b)}  oV b={crc.to_str(ob)}")

if __name__=="__main__":
    main()
