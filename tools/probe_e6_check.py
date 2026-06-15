#!/usr/bin/env python3
"""Check E6_value on REAL dseg arg-zones: does proj y (NT aM) == NT(msfx aM)
when it fires, for aM = takeWhile-positive arg zone of a genuine (0,y)#r in ST_PS?
Print the firing-but-mismatch cases with full ST context, to see if dseg really holds."""
import sys, itertools, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(23)
from wfe_explore import translate, enum_ST, fmt
from valnorm import conv, nrm, lt_term, fmtb, G, in_OT
from fast_pss import oper

def proj(a,x):
    bb=x
    while True:
        bad=[g for g in G(a,bb) if not lt_term(g,bb)]
        if not bad: break
        g=bad[0]
        for h in bad[1:]:
            if lt_term(g,h): g=h
        bb=g
    return bb
def takeW(r):
    out=[]
    for p in r:
        if p[0]>0: out.append(p)
        else: break
    return out
def maxr1(S): return max(c[1] for c in S)
def msfx(S):
    m=maxr1(S); out=list(S)
    while out and out[0][1]<m: out=out[1:]
    return out
def NT(S): return nrm(conv(translate(list(S))))

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
STset=set(extra)
print('deep ST closure =',len(extra),flush=True)

vtot=vbad=0; exV=[]
checked=set()
for M in extra:
    M=list(M)
    if not M or M[0][0]!=0: continue
    y=M[0][1]
    r=M[1:]
    aM=tuple(takeW(r))
    if not aM: continue
    key=(y,aM)
    if key in checked: continue
    checked.add(key)
    B=NT(aM)
    p=proj(y,B)
    if p==B: continue   # not firing
    vtot+=1
    ms=NT(msfx(list(aM)))
    if p!=ms:
        vbad+=1
        if len(exV)<8:
            # is (0,y)#aM by itself in ST? what is the host M?
            host_in_st = tuple(M) in STset
            exV.append((y,aM,fmtb(p),fmtb(ms),tuple(M),host_in_st))
print(f'E6_value on dedup arg-zones: ok={vtot-vbad}/{vtot} bad={vbad}')
for y,aM,p,m,M,h in exV:
    print(f'  Vbad y={y}')
    print(f'      aM={aM}')
    print(f'      host M={M} in_ST={h}')
    print(f'      proj={p}  msfx_img={m}')
print('DONE')
