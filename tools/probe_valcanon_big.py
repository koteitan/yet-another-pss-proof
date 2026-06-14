import importlib.util
spec = importlib.util.spec_from_file_location("m", "cset_remark_check.py")
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
from functools import cmp_to_key
args = sorted(m.SMALL, key=cmp_to_key(m.cmp))
m.warm_psi(args)
# Broad test: for ALL zeta,w with psi defined, and all v<=w: acanon v (psi zeta w)?
# Count defined cases and check.
viol=0;ch=0;exs=[]; defined=0
for zeta in args:
    for w in (0,1,2):
        p=m.psi(zeta,w)
        if p is None: continue
        defined+=1
        for v in range(0,w+1):
            ch+=1
            if not m.acanon(v,p):
                viol+=1
                if len(exs)<20: exs.append((m.to_str(zeta),w,v,m.to_str(p)))
print(f"psi defined (zeta,w) pairs: {defined}; checks(v<=w): {ch}; viol acanon v(psi): {viol}")
for e in exs: print("  VIOL",e)
# distinct psi values:
vals=set()
for zeta in args:
    for w in (0,1,2):
        p=m.psi(zeta,w)
        if p is not None: vals.add(p)
print("distinct psi values:",len(vals), [m.to_str(x) for x in sorted(vals,key=cmp_to_key(m.cmp))][:20])
