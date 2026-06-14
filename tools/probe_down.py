import importlib.util
spec = importlib.util.spec_from_file_location("m", "cset_remark_check.py")
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
from functools import cmp_to_key
key=cmp_to_key(m.cmp)
args=sorted(m.SMALL,key=key); m.warm_psi(args)
# For non-canonical xi (psi defined), is there beta<xi with psi(beta,w)=psi(xi,w)?
print("non-canonical xi: exists beta<xi with psi beta w = psi xi w ?")
tot=0;bad=0;cases=0
for w in (0,1,2):
  for xi in args:
    p=m.psi(xi,w)
    if p is None: continue
    if m.acanon(w,xi): continue
    cases+=1
    ex=[b for b in args if m.lt(b,xi) and m.psi(b,w) is not None and m.eq(m.psi(b,w),p)]
    tot+=1
    if not ex:
      bad+=1
      print(f"  NO smaller wit: w={w} xi={m.to_str(xi)} p={m.to_str(p)}")
print(f"  noncanon-with-psi cases={cases} no-smaller={bad}")
