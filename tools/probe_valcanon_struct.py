#!/usr/bin/env python3
"""
Structural probe of psi_value_acanon:  v <= w  ==>  acanon v (psi zeta w).

For each defined value c = psi(zeta,w), we:
  - compute the least witness xi0 = least xi with psi(xi,w)=c
  - report acanon(w, xi0), whether xi0 < c, and xi0 vs zeta
  - directly check acanon(v,c) for all v<=w  (c in Cset(c,v,False))
and we look for ANY (zeta,w,v<=w) with NOT acanon(v, psi(zeta,w)).
We also widen the test args beyond SMALL using all distinct psi values as args.
"""
import importlib.util
spec = importlib.util.spec_from_file_location("m", "cset_remark_check.py")
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
from functools import cmp_to_key
key = cmp_to_key(m.cmp)

args = sorted(m.SMALL, key=key)
m.warm_psi(args)

def least_wit(c, w):
    # least xi in args with psi(xi,w)=c
    for xi in args:
        p = m.psi(xi, w)
        if p is not None and m.eq(p, c):
            return xi
    return None

viol = []
rows = []
for zeta in args:
    for w in (0,1,2):
        c = m.psi(zeta, w)
        if c is None: continue
        xi0 = least_wit(c, w)
        ac_w_xi0 = m.acanon(w, xi0) if xi0 is not None else None
        xi0_lt_c = m.lt(xi0, c) if xi0 is not None else None
        for v in range(0, w+1):
            if not m.acanon(v, c):
                viol.append((m.to_str(zeta), w, v, m.to_str(c)))
        rows.append((m.to_str(c), w, m.to_str(zeta),
                     None if xi0 is None else m.to_str(xi0),
                     ac_w_xi0, xi0_lt_c))

print(f"VIOLATIONS of psi_value_acanon (v<=w, NOT acanon v (psi zeta w)): {len(viol)}")
for x in viol[:30]: print("  VIOL", x)

# Per-value structural summary (dedup by c,w)
seen=set()
print("\nvalue c | w | least-witness xi0 | acanon(w,xi0) | xi0<c")
for (c,w,zeta,xi0,acw,lt) in rows:
    k=(c,w)
    if k in seen: continue
    seen.add(k)
    print(f"  {c:<10} w={w}  xi0={str(xi0):<8} acanon(w,xi0)={acw}  xi0<c={lt}")

# Is there ANY value c=psi(zeta,w) whose least witness is NOT < c (psi-fixpoint-ish)?
nonlt = [(c,w,xi0) for (c,w,zeta,xi0,acw,lt) in rows if lt is False]
print(f"\nvalues whose least witness is NOT < value: {len(set((c,w) for c,w,_ in nonlt))}")
for c,w,xi0 in list({(c,w,xi0) for c,w,xi0 in nonlt})[:20]:
    print("   NONLT", c, "w=",w, "xi0=",xi0)
