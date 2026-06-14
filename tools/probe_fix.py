import importlib.util
spec = importlib.util.spec_from_file_location("m", "cset_remark_check.py")
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
from functools import cmp_to_key
key = cmp_to_key(m.cmp)
args = sorted(m.SMALL, key=key)
m.warm_psi(args)
# For each value c=psi(d,w), least witness delta. Relationship of delta to c.
# Also: is the least witness characterized by delta <= c (i.e. psi delta w >= delta)?
print("least-witness delta vs value c: is delta<=c? is acanon? is delta in C_w(c)?")
for w in (0,1,2):
    vals={}
    for d in args:
        p=m.psi(d,w)
        if p is None: continue
        if p not in vals: vals[p]=d
    for p,d in sorted(vals.items(), key=lambda kv: key(kv[0])):
        # check: psi(d,w) >= d  (i.e. d canonical-ish / d <= value)?
        dle = m.le(d,p)
        # Is d < c, and d in Cset(c,w)? acanon means d in Cset(d,w,False)
        print(f"  w={w} c={m.to_str(p):<10} least-wit d={m.to_str(d):<10} d<=c:{dle} acanon:{m.acanon(w,d)}")
