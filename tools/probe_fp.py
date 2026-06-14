import importlib.util
spec = importlib.util.spec_from_file_location("m", "cset_remark_check.py")
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
from functools import cmp_to_key
key=cmp_to_key(m.cmp)
args=sorted(m.SMALL,key=key); m.warm_psi(args)
# Test: psi(d,w)<=d  =>  psi(psi(d,w),w)=psi(d,w)  (fixpoint when value<=arg)
print("Test FP: psi d w <= d  =>  psi(psi d w)w = psi d w")
tot=0;bad=0;cases=0
for w in (0,1,2):
  for d in args:
    p=m.psi(d,w)
    if p is None: continue
    if m.le(p,d):   # value <= arg
      cases+=1
      pp=m.psi(p,w)
      tot+=1
      if pp is None or not m.eq(pp,p):
        bad+=1
        print(f"  CE w={w} d={m.to_str(d)} p={m.to_str(p)} pp={m.to_str(pp) if pp else None}")
print(f"  cases(value<=arg)={cases} bad={bad}")
# Also test: psi d w <= d  => acanon w (psi d w) ? (value canonical) -- known false per noncanon_value_noncanon
# Test: is psi d w >= d ALWAYS when d canonical?  (acanon w d => d <= psi d w)
print("Test: acanon w d => d <= psi d w  (canonical args sit below their value)")
tot=0;bad=0
for w in (0,1,2):
  for d in args:
    if not m.acanon(w,d): continue
    p=m.psi(d,w)
    if p is None: continue
    tot+=1
    if not m.le(d,p): bad+=1; print(f"  CE w={w} d={m.to_str(d)} p={m.to_str(p)}")
print(f"  tested {tot} bad {bad}")
