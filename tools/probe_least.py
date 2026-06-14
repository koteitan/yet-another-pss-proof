import importlib.util
spec = importlib.util.spec_from_file_location("m", "cset_remark_check.py")
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
from functools import cmp_to_key
key = cmp_to_key(m.cmp)
args = sorted(m.SMALL, key=key)
m.warm_psi(args)

# Test claim: for every defined psi-value c at subscript w, the LEAST delta
# with psi(delta,w)=c is canonical (acanon w delta).
print("Claim A: least witness of any psi-value is canonical")
bad=0; tot=0
for w in (0,1,2):
    vals={}
    for d in args:
        p=m.psi(d,w)
        if p is None: continue
        if p not in vals: vals[p]=d  # args sorted ascending => first = least
    for p,d in vals.items():
        tot+=1
        if not m.acanon(w,d):
            bad+=1
            print(f"  COUNTEREX w={w} value={m.to_str(p)} least-wit={m.to_str(d)} NONcanon")
print(f"  tested {tot}, counterexamples {bad}")

# Test claim B: among ALL witnesses, is at least one canonical? (some delta with psi=val and acanon)
print("Claim B: every psi-value has at least one canonical witness")
bad=0;tot=0
for w in (0,1,2):
    valset=set(m.psi(d,w) for d in args if m.psi(d,w) is not None)
    for p in valset:
        tot+=1
        has=any(m.eq(m.psi(d,w),p) and m.acanon(w,d) for d in args)
        if not has:
            bad+=1; print(f"  COUNTEREX w={w} value={m.to_str(p)} has NO canonical witness")
print(f"  tested {tot}, counterexamples {bad}")
