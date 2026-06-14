#!/usr/bin/env python3
import importlib.util
spec = importlib.util.spec_from_file_location("m", "cset_remark_check.py")
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
from functools import cmp_to_key
key = cmp_to_key(m.cmp)
args = sorted(m.SMALL, key=key)
m.warm_psi(args)

# count how many xi are noncanonical at each u
for u in (0,1,2):
    nc=[xi for xi in args if not m.acanon(u,xi)]
    print(f"u={u}: noncanon count={len(nc)} / {len(args)}; sample={[m.to_str(x) for x in nc[:6]]}")

# For a few alpha, list Cset_c membership of noncanon xi<alpha
cnt=0
for alpha in args:
    for v in (0,1):
        Cc=m.Cset(alpha,v,True)
        for xi in args:
            if not m.lt(xi,alpha): continue
            if m.acanon(0,xi) and m.acanon(1,xi) and m.acanon(2,xi): continue
            if xi in Cc:
                cnt+=1
                if cnt<=10:
                    print(f"  alpha={m.to_str(alpha)} v={v} xi={m.to_str(xi)} in Cc, acanon(0,1,2)={m.acanon(0,xi),m.acanon(1,xi),m.acanon(2,xi)}")
print("noncanon-xi-in-Cc count:",cnt)
