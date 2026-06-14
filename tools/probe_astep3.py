#!/usr/bin/env python3
# Broaden: directly check the FULL closure Cset(alpha,v) (==Cset_c by Remark)
# for noncanon xi<alpha, and whether psi(xi,u) in Cset(alpha,v).
import importlib.util
spec = importlib.util.spec_from_file_location("m", "cset_remark_check.py")
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
from functools import cmp_to_key
key = cmp_to_key(m.cmp)
args = sorted(m.SMALL, key=key)
m.warm_psi(args)

total=0; ok=0; bad=0; exs=[]
val_lt_alpha=0
for alpha in args:
    for v in (0,1):
        C=m.Cset(alpha,v,False)  # full closure
        for xi in C:
            if not m.lt(xi,alpha): continue
            for u in (0,1,2):
                if v>u: continue
                if m.acanon(u,xi): continue
                p=m.psi(xi,u)
                if p is None: continue
                total+=1
                if m.lt(p,alpha): val_lt_alpha+=1
                if p in C: ok+=1
                else:
                    bad+=1
                    if len(exs)<8: exs.append((m.to_str(alpha),v,m.to_str(xi),u,m.to_str(p),m.lt(p,alpha)))
print(f"FULL-closure test: total={total} ok={ok} bad={bad}; val<alpha={val_lt_alpha}")
for e in exs: print("  BAD",e)
