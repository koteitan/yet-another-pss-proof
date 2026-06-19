#!/usr/bin/env python3
"""
Is the LEAST witness xi0 of a psi-value c=psi(.,w) ALWAYS < c ?
And separately: does there exist a canonical delta with delta >= psi(delta,w)
(the 'false lemma' regime), and if so is it ever a least witness?

We use the enlarged pool to maximize chances of catching delta >= psi(delta,w).
"""
import importlib.util
spec = importlib.util.spec_from_file_location("m", "cset_remark_check.py")
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
from functools import cmp_to_key
key = cmp_to_key(m.cmp)
base = sorted(m.SMALL, key=key); m.warm_psi(base)
vals=set()
for z in base:
    for w in (0,1,2):
        p=m.psi(z,w)
        if p is not None: vals.add(p)
pool=set(base)|vals
for a in list(vals):
    for b in list(vals):
        s=m.oadd(a,b)
        if m.lt(s,m.NABLA): pool.add(s)
args=sorted(pool,key=key); m.warm_psi(args)

# delta with acanon(w,delta) but delta >= psi(delta,w):
ge=[]
for d in args:
    for w in (0,1,2):
        if m.acanon(w,d):
            p=m.psi(d,w)
            if p is not None and not m.lt(d,p):  # d >= p
                ge.append((m.to_str(d),w,m.to_str(p)))
print(f"canonical delta with delta>=psi(delta,w): {len(ge)}")
for x in ge[:20]: print("  GE",x)

# least witnesses and whether < value:
def least_wit(c,w):
    for xi in args:
        p=m.psi(xi,w)
        if p is not None and m.eq(p,c): return xi
    return None
bad=[]
for z in args:
    for w in (0,1,2):
        c=m.psi(z,w)
        if c is None: continue
        xi0=least_wit(c,w)
        if xi0 is not None and not m.lt(xi0,c):
            bad.append((m.to_str(c),w,m.to_str(xi0)))
print(f"least witness NOT < value: {len(set(bad))}")
for x in list(set(bad))[:20]: print("  BAD",x)
