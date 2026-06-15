#!/usr/bin/env python3
"""Does the per-step strict-monotonicity psi_strict_mono_arg survive on NF args?
For NF principals sharing subscript a, with args b' , f drawn from NF arg-positions:
  oV b' < oV f   =?=>   psi(oV b') a  <  psi(oV f) a
If this FAILS (psi collapses b' and f to the same value while oV b' < oV f),
that is exactly why ccnd-canonicity is needed and why oV_mono_NF does not reduce
per-principal -- the §1 core.  Done in the genuine finite collapse model.
"""
import sys, importlib.util; sys.setrecursionlimit(1000000); sys.path.insert(0,'.')
spec=importlib.util.spec_from_file_location("crc","cset_remark_check.py")
crc=importlib.util.module_from_spec(spec); spec.loader.exec_module(crc)
from wfe_explore import translate, enum_ST, fmt
Z=()
def oV(t):
    if t==Z: return crc.ZERO
    a,b,c=t
    p=crc.psi(oV(b),a)
    if p is None: raise ValueError
    return crc.oadd(p,oV(c))
def maxsub_all(t):
    if t==Z: return 0
    a,b,c=t; return max(a,maxsub_all(b),maxsub_all(c))
def args_at(t,sub,out):
    if t==Z: return
    a,b,c=t
    if a==sub: out.add(b)
    args_at(b,sub,out); args_at(c,sub,out)

def main():
    ST=enum_ST(seed_max_v=3,oper_ns=(1,2,3,4),max_len=14,rounds=7)
    NF=[t for t in set(translate(M) for M in ST) if maxsub_all(t)<=2]
    feas=[]
    for t in NF:
        try: oV(t); feas.append(t)
        except ValueError: pass
    print(f"feasible NF: {len(feas)}")
    # collect arg terms per subscript
    argset={0:set(),1:set(),2:set()}
    for t in feas:
        for s in (0,1,2):
            args_at(t,s,argset[s])
    # warm
    allargs=set()
    for s in (0,1,2):
        for b in argset[s]:
            try: allargs.add(oV(b))
            except ValueError: pass
    crc.warm_psi(list(allargs))
    tot=0; coll=0; rev=0; ex=[]
    for a in (0,1,2):
        bs=[b for b in argset[a]]
        ov={}
        for b in bs:
            try: ov[b]=oV(b)
            except ValueError: pass
        bs=[b for b in bs if b in ov]
        for b1 in bs:
            for f in bs:
                if crc.lt(ov[b1],ov[f]):  # oV b1 < oV f
                    p1=crc.psi(ov[b1],a); p2=crc.psi(ov[f],a)
                    if p1 is None or p2 is None: continue
                    tot+=1
                    if crc.eq(p1,p2):
                        coll+=1
                        if len(ex)<10: ex.append(('COLLAPSE',a,b1,f,p1))
                    elif crc.lt(p2,p1):
                        rev+=1
                        if len(ex)<10: ex.append(('REV',a,b1,f,p1))
    print(f"psi_strict_mono_arg on NF args: tested={tot}")
    print(f"  COLLAPSES (oV b'<oV f but psi equal): {coll}")
    print(f"  REVERSALS: {rev}")
    for tag,a,b1,f,p in ex:
        print(f"   {tag} a={a}: oV {fmt(b1)} < oV {fmt(f)} but psi_a both = {crc.to_str(p)}")

if __name__=="__main__":
    main()
