import importlib.util
spec = importlib.util.spec_from_file_location("m", "cset_remark_check.py")
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
from functools import cmp_to_key
args = sorted(m.SMALL, key=cmp_to_key(m.cmp))
m.warm_psi(args)
# Q: psi_w(zeta) with acanon w zeta  => acanon v (psi_w zeta) for v<=w ?
viol=0;ch=0;exs=[]
for zeta in args:
    for w in (0,1,2):
        if not m.acanon(w,zeta): continue
        p=m.psi(zeta,w)
        if p is None: continue
        for v in range(0,w+1):
            ch+=1
            if not m.acanon(v,p):
                viol+=1
                if len(exs)<15: exs.append((m.to_str(zeta),w,v,m.to_str(p)))
print(f"Q psi_w(zeta) canonical at v<=w (zeta canon): checked={ch} viol={viol}")
for e in exs: print("  VIOL zeta,w,v,psi:",e)
# Also without requiring zeta canonical (any zeta producing a value in closure):
viol2=0;ch2=0;exs2=[]
for zeta in args:
    for w in (0,1,2):
        p=m.psi(zeta,w)
        if p is None: continue
        for v in range(0,w+1):
            ch2+=1
            if not m.acanon(v,p):
                viol2+=1
                if len(exs2)<10: exs2.append((m.to_str(zeta),w,v,m.to_str(p)))
print(f"Q' any zeta: psi_w(zeta) canonical at v<=w: checked={ch2} viol={viol2}")
for e in exs2: print("  VIOL'",e)
