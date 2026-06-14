import importlib.util
spec = importlib.util.spec_from_file_location("m", "cset_remark_check.py")
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
from functools import cmp_to_key
args = sorted(m.SMALL, key=cmp_to_key(m.cmp))
m.warm_psi(args)
found=0; viol=0
for d in args:
    for a in (0,1):  # Om(a+1) defined
        if not m.acanon(a,d): continue
        if m.le(m.Om(a+1), d):  # delta >= Om(a+1)
            p=m.psi(d,a)
            found+=1
            dlp = m.lt(d,p) if p else None
            if dlp is False: viol+=1
            if found<=20:
                print(f"  delta={m.to_str(d)} a={a} Om(a+1)={m.to_str(m.Om(a+1))} psi={m.to_str(p) if p else None} delta<psi={dlp}")
print(f"canonical delta>=Om(a+1) (a in 0,1): count={found} viol(delta>=psi)={viol}")
