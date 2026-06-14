# Final robust check of psi_value_acanon using the closure directly (no psi-None dependence
# on the value side): for every ordinal p that IS a psi_w-value for some zeta with v<=w,
# check p in Cset(p,v).  Also independently: every element of Cset(alpha,v) that is a
# psi-value is canonical at v.
import importlib.util
spec = importlib.util.spec_from_file_location("m", "cset_remark_check.py")
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
from functools import cmp_to_key
args=sorted(m.SMALL,key=cmp_to_key(m.cmp))
m.warm_psi(args)
# Collect all (value, w) where value=psi(zeta,w)
val_w=set()
for zeta in args:
    for w in (0,1,2):
        p=m.psi(zeta,w)
        if p is not None: val_w.add((p,w))
viol=0;ch=0;exs=[]
for (p,w) in val_w:
    for v in range(0,w+1):
        ch+=1
        if not m.acanon(v,p):
            viol+=1
            if len(exs)<20: exs.append((m.to_str(p),w,v))
print(f"psi_value_acanon over distinct (value,w): checks={ch} viol={viol}")
for e in exs: print("  VIOL value,w,v:",e)
