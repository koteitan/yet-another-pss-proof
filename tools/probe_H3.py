#!/usr/bin/env python3
import importlib.util
spec = importlib.util.spec_from_file_location("m", "cset_remark_check.py")
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
from functools import cmp_to_key
key = cmp_to_key(m.cmp)
args = sorted(m.SMALL, key=key)
m.warm_psi(args)

# H3: xi in Cset(alpha,v) and xi<alpha ==> xi in Cset(xi,v)   (own closure)
# Note Cset(xi,v) full closure == acanon-related: acanon v xi <=> xi in Cset(xi,v,False)
viol=0;ch=0;exs=[]
for alpha in args:
    for v in (0,1,2):
        C=m.Cset(alpha,v,False)
        for xi in C:
            if not m.lt(xi,alpha): continue
            ch+=1
            own=m.Cset(xi,v,False)
            if xi not in own:
                viol+=1
                if len(exs)<10: exs.append((m.to_str(alpha),v,m.to_str(xi)))
print(f"H3 xi in own Cset(xi,v): checked={ch} viol={viol}")
for e in exs: print("  ",e)

# Also test the CANONICAL version: xi in Cset_c(alpha,v) and xi<alpha ==> xi in Cset_c(xi,v)
viol2=0;ch2=0;exs2=[]
for alpha in args:
    for v in (0,1,2):
        C=m.Cset(alpha,v,True)
        for xi in C:
            if not m.lt(xi,alpha): continue
            ch2+=1
            own=m.Cset(xi,v,True)
            if xi not in own:
                viol2+=1
                if len(exs2)<10: exs2.append((m.to_str(alpha),v,m.to_str(xi)))
print(f"H3c xi in own Cset_c(xi,v): checked={ch2} viol={viol2}")
for e in exs2: print("  ",e)
