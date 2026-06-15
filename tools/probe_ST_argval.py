#!/usr/bin/env python3
"""ST-level structural invariant (IST):
   for every ST form M = (0,y)#r, every value v in the arg zone
   aM = takeWhile(0<fst) (tail) satisfies  v >= y   (and is v > y always?)
Also: every value in the WHOLE arg-zone-translate's subscript multiset >= y.
This is the cheap, provable diagonal-derived fact that feeds NT_subs/proj_subs.
"""
import sys
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
from wfe_explore import enum_ST
from fast_pss import oper

def takeW(r):
    out=[]
    for p in r:
        if p[0]>0: out.append(p)
        else: break
    return out

base=enum_ST(seed_max_v=5,oper_ns=(1,2,3,4,5),max_len=16,rounds=8)
extra=set(base); cur=list(extra)
for _ in range(5):
    new=[]
    for M in cur:
        M=list(M)
        if len(M)<2: continue
        for n in (1,2,3,4,5):
            tt=tuple(oper(M,n))
            if len(tt)<=22 and tt not in extra:
                extra.add(tt); new.append(tt)
    cur=new
    if not cur: break
print('deep ST closure =',len(extra),flush=True)

ge=gt=tot=0; exGe=[]; exGt=[]
for M in extra:
    M=list(M)
    if not M or M[0][0]!=0: continue
    y=M[0][1]; aM=takeW(M[1:])
    if not aM: continue
    tot+=1
    vals=[v for (i,v) in aM]
    if all(v>=y for v in vals): ge+=1
    else: exGe.append((y,M)) if len(exGe)<6 else None
    if all(v>y for v in vals): gt+=1
    else: exGt.append((y,aM)) if len(exGt)<6 else None
print(f'arg zones total={tot}')
print(f'IST>= : all arg-zone values >= y : {ge}/{tot}')
for y,M in exGe[:5]: print(f'    FAIL y={y} M={M}')
print(f'IST>  : all arg-zone values >  y : {gt}/{tot}')
for y,aM in exGt[:5]: print(f'    (>) y={y} aM={aM}')
print('DONE')
