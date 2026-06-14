#!/usr/bin/env python3
import importlib.util
spec = importlib.util.spec_from_file_location("m", "cset_remark_check.py")
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
from functools import cmp_to_key
key = cmp_to_key(m.cmp)
args = sorted(m.SMALL, key=key)
m.warm_psi(args)

# Refine: is acanon u xi monotone-ish? Test simplest form:
# H0: xi in Cset(alpha,v) and xi<alpha ==> acanon v xi   (same subscript)
v0=0;viol=0;checked=0;exs=[]
for alpha in args:
    for v in (0,1,2):
        C=m.Cset(alpha,v,False)
        for xi in C:
            if not m.lt(xi,alpha): continue
            checked+=1
            if not m.acanon(v,xi):
                viol+=1
                if len(exs)<10: exs.append((m.to_str(alpha),v,m.to_str(xi)))
print(f"H0 (acanon v xi): checked={checked} viol={viol}")
for e in exs: print("  ",e)

# Also: does acanon v xi imply acanon u xi for u>=v?  (monotone in subscript)
viol2=0;ch2=0;exs2=[]
for xi in args:
    for v in (0,1,2):
        if not m.acanon(v,xi): continue
        for u in (v,1,2):
            if u<v: continue
            ch2+=1
            if not m.acanon(u,xi):
                viol2+=1
                if len(exs2)<10: exs2.append((m.to_str(xi),v,u))
print(f"acanon monotone in subscript: checked={ch2} viol={viol2}")
for e in exs2: print("  MONO-VIOL",e)
