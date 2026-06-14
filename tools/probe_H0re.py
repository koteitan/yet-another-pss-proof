import importlib.util
spec = importlib.util.spec_from_file_location("m", "cset_remark_check.py")
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
from functools import cmp_to_key
args = sorted(m.SMALL, key=cmp_to_key(m.cmp))
m.warm_psi(args)
# H0: xi in Cset_c(alpha,v) and xi<alpha => acanon v xi.   acanon doesn't need psi-None.
viol=0;ch=0;exs=[]
for alpha in args:
    for v in (0,1,2):
        Cc=m.Cset(alpha,v,True)
        for xi in Cc:
            if not m.lt(xi,alpha): continue
            ch+=1
            if not m.acanon(v,xi):
                viol+=1
                if len(exs)<15: exs.append((m.to_str(alpha),v,m.to_str(xi)))
print(f"H0 (Cset_c version): checked={ch} viol={viol}")
for e in exs: print("  VIOL",e)
