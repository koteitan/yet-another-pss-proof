#!/usr/bin/env python3
"""Probe: on the ARGUMENT ZONE of an ST form (0,y)#r, is
   proj y (nrm (translate aM)) == nrm (translate aM) ?
i.e. is the normalized argument zone already y-canonical (proj=id)?
If TRUE deep, the core lemma proj_nrm_argzone_olt collapses to oV_order_pres on nrm.
"""
import sys
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
from wfe_explore import translate, olt, fmt, enum_ST
from valnorm import conv, nrm, lt_term, le_term, G, fmtb
from fast_pss import oper

def proj(a, x):
    bb = x
    while True:
        bad = [g for g in G(a, bb) if not lt_term(g, bb)]
        if not bad: break
        g = bad[0]
        for h in bad[1:]:
            if lt_term(g, h): g = h
        bb = g
    return bb

def takeW(r):  # rows >0
    out=[]
    for p in r:
        if p[0]>0: out.append(p)
        else: break
    return out

base = enum_ST(seed_max_v=5, oper_ns=(1,2,3,4,5), max_len=16, rounds=8)
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
print('deep ST closure =', len(extra), flush=True)

tot=0; neq=0; ex=[]
for M in extra:
    M=list(M)
    if not M: continue
    if M[0][0]!=0: continue
    y=M[0][1]
    r=M[1:]
    aM=takeW(r)
    if not aM: continue
    B=conv(translate(aM))
    nB=nrm(B)
    pB=proj(y,nB)
    tot+=1
    if pB!=nB:
        neq+=1
        if len(ex)<8: ex.append((y,aM,nB,pB))
print(f'argzone proj=id : tested={tot}  proj-MOVED={neq}', flush=True)
for y,aM,nB,pB in ex:
    print(f'  y={y} aM={aM}\n     nrm={fmtb(nB)}\n     proj={fmtb(pB)}')
print('DONE', flush=True)
