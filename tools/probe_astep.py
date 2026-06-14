#!/usr/bin/env python3
import importlib.util, sys
spec = importlib.util.spec_from_file_location("m", "cset_remark_check.py")
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
from functools import cmp_to_key
key = cmp_to_key(m.cmp)
args = sorted(m.SMALL, key=key)
m.warm_psi(args)

# Test alpha_step_residue claim over many (alpha, v, xi, u).
# xi < alpha, xi in Cset_c(alpha,v), not acanon(u,xi), v<=u  =>  psi(xi,u) in Cset_c(alpha,v)
total=0; ok=0; bad=0
# also collect: when claim holds, is psi(xi,u) itself a fixpoint (wit==psi)? and is psi(xi,u)<alpha?
cnt_val_lt_alpha=0
cnt_val_in_Cc=0
examples=[]
for alpha in args:
    Csetc_cache={}
    for v in (0,1):
        Cc = m.Cset(alpha, v, True)   # canonical closure Cset_c(alpha,v)
        for xi in args:
            if not m.lt(xi, alpha): continue
            if xi not in Cc: continue
            for u in (0,1,2):
                if v>u: continue
                if m.acanon(u,xi): continue
                p = m.psi(xi,u)
                if p is None: continue
                total+=1
                inCc = p in Cc
                if inCc: cnt_val_in_Cc+=1
                if m.lt(p, alpha): cnt_val_lt_alpha+=1
                if inCc: ok+=1
                else:
                    bad+=1
                    if len(examples)<8:
                        examples.append((m.to_str(alpha),v,m.to_str(xi),u,m.to_str(p), m.lt(p,alpha)))
print(f"total={total} ok={ok} bad={bad}")
print(f"  of total: psi(xi,u)<alpha in {cnt_val_lt_alpha}; psi(xi,u) in Cset_c in {cnt_val_in_Cc}")
if examples:
    print("BAD examples (alpha,v,xi,u,psi,psi<alpha):")
    for e in examples: print("   ",e)
