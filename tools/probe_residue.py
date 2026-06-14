#!/usr/bin/env python3
# Probe: for the residue, when xi is non-canonical (xi not in C_w(xi)) and
# psi(xi,w) <= xi, find the LEAST delta with psi(delta,w)=psi(xi,w) and check
# whether that delta is canonical and < arg, and whether psi(xi,w) in Cset_c.
import importlib.util, sys
spec = importlib.util.spec_from_file_location("m", "cset_remark_check.py")
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
from functools import cmp_to_key
key = cmp_to_key(m.cmp)

# enlarge the principal candidate pool & NABLA already fixed; instead directly
# search: enumerate xi in SMALL, w in 0,1,2; check noncanon and psi defined.
args = sorted(m.SMALL, key=key)
m.warm_psi(args)

print("Searching for residue case: xi noncanon at w, psi(xi,w) defined, psi(xi,w)<=xi")
found=0
for w in (0,1,2):
    for xi in args:
        p = m.psi(xi,w)
        if p is None: continue
        if m.acanon(w,xi): continue       # need non-canonical
        # psi(xi,w) <= xi ?
        if not m.le(p, xi): continue
        found+=1
        # least delta with psi(delta,w)=p
        least=None
        for d in args:
            if m.psi(d,w) is not None and m.eq(m.psi(d,w), p):
                least=d; break
        print(f"  w={w} xi={m.to_str(xi)} psi={m.to_str(p)} <=xi; least-wit={m.to_str(least)} acanon(least)={m.acanon(w,least)}")
print("found cases:", found)
