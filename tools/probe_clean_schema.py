#!/usr/bin/env python3
"""DECISIVE clean proof-schema checker (NO consulting real olt for decisions).

Goal: olt x (translate B) for x in Gterm0(translate B), (0,0)::B in ST_PS row1<=1.

Engine facts assumed (all GREEN-provable):
  E1  olt_P_of_lead_lt:  lead t < w  ->  olt t (P w b c).   (and Z<o anything)
  E2  seqlex_imp_olt:    blockok d M, blockok d N, seqlex M N  ->  olt(tM)(tN).
  E3  translate_shift:   translate(shift(M,delta)) = translate(M).
  E4  olt_P_P lex:       olt (P a b c)(P e f g) <=> a<e or (a=e&olt b f) or (a=e&b=f&olt c g).
  E5  olt_trans.

SCHEMA  D(x, B):  returns a BOOL = "schema proves olt x (translate B)" using ONLY
E1-E5 and structural recursion. We then compare D(x,B) to the real olt; any case
real=True but D=False is a SCHEMA GAP (route incomplete); any D=True but real=False
is a SCHEMA UNSOUNDNESS (route wrong).  We want 0 of BOTH at +5 AND +6.

D(x,B):
  tB=translate B = P y A S  (y=B.head.2, A=translate(takeW), S=translate(sib),
     d=B.head.1, takeW=rest.takeWhile(d<.), sib=rest.dropWhile(d<.)).
  if lead x < y: return True                                   # E1
  if lead x > y: return False                                  # cannot prove (real false)
  # lead x == y:  x = P y ax sx
  ax, sx = x[1], x[2]
  # olt(x, P y A S) via E4: prove (olt ax A) OR (ax==A and olt sx S)
  if ax == A:
      return Dtail(sx, sib)        # olt sx S, sib is the sibling forest
  return Darg(ax, takeW)           # olt ax A, takeW is a depth-(d+1) block

Darg(t, BLK):  prove olt t (translate BLK), BLK a single block (blockok at head).
  # Use shifted-seqlex if t is a translate of a sub-block of BLK; else structural.
  if t == Z: return translate(BLK) != Z
  # try E2: find witness sub-block K of BLK with translate K = t, shift to BLK head.
  if translate(BLK) == Z: return False
  dBLK = BLK[0][0]
  for K in subblocks(BLK):
      if K and K!=BLK and translate(K)==t:
          dK=K[0][0]; Ksh=shift(K, dBLK-dK)
          if blockok(dBLK,BLK) and blockok(dBLK,Ksh) and seqlex(Ksh,BLK):
              return True
  # fallback: structural like D
  return Dstruct(t, BLK)

Dtail(t, FOR):  prove olt t (translate FOR), FOR a sibling forest (multi-root).
  # recurse with D on FOR (same multi-root handling).
  if t == Z: return translate(FOR) != Z
  if not FOR: return False
  return D(t, FOR)
"""
import sys
sys.path.insert(0,'.')
from fast_pss import Lng
from wfe_explore import translate, olt
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt
from probe_bmocf_ancestor import enum_depth
Z=()
def lead(t): return t[0] if t else -1
def Gterm(u,t):
    if t==(): return []
    a,b,c=t; out=[]
    if u<=a: out.append(b); out+=Gterm(u,b)
    out+=Gterm(u,c); return out
def steps1(B): return all(B[j+1][0]<=B[j][0]+1 for j in range(len(B)-1))
def blockok(d,B):
    if not B: return True
    return B[0][0]==d and all(p[0]>=d for p in B) and steps1(B)
def shift(B,delta): return tuple((p[0]+delta,p[1]) for p in B)
def pairlt(p,q): return p[0]<q[0] or (p[0]==q[0] and p[1]<q[1])
def seqlex(M,N):
    M=list(M);N=list(N);i=0
    while i<len(M) and i<len(N):
        if M[i]!=N[i]: return pairlt(M[i],N[i])
        i+=1
    if i==len(M): return len(N)>len(M)
    return False
def subblocks(B):
    res=[]
    def rec(seg):
        seg=tuple(seg); res.append(seg)
        if not seg: return
        (x,y)=seg[0]; rest=seg[1:]; i=0
        while i<len(rest) and rest[i][0]>x: i+=1
        rec(rest[:i]); rec(rest[i:])
    rec(tuple(B)); return res

def split(B):
    (d,y)=B[0]; rest=B[1:]; i=0
    while i<len(rest) and rest[i][0]>d: i+=1
    return d,y,tuple(rest[:i]),tuple(rest[i:])  # d,y,takeW,sib

import sys as _s; _s.setrecursionlimit(100000)

def D(x, B):
    if not B: return False
    tB=translate(B)
    if tB==Z: return False
    y=tB[0]; A=tB[1]; S=tB[2]
    if lead(x) < y: return True
    if lead(x) > y: return False
    if x==Z: return False
    ax,sx=x[1],x[2]
    d,_,takeW,sib=split(B)
    if ax==A:
        return Dtail(sx,sib)
    return Darg(ax,takeW)

def Darg(t,BLK):
    tBLK=translate(BLK)
    if t==Z: return tBLK!=Z
    if tBLK==Z: return False
    dBLK=BLK[0][0]
    for K in subblocks(BLK):
        if K and K!=BLK and translate(K)==t:
            dK=K[0][0]; Ksh=shift(K,dBLK-dK)
            if blockok(dBLK,BLK) and blockok(dBLK,Ksh) and seqlex(Ksh,BLK):
                return True
    # fallback structural (BLK as a forest)
    return D(t,BLK)

def Dtail(t,FOR):
    tF=translate(FOR)
    if t==Z: return tF!=Z
    if not FOR: return False
    return D(t,FOR)

def main():
    for rounds in (5,6):
        seen=enum_depth(4,(1,2,3),28,rounds)
        hosts=[M for M in seen if Lng(M)<=18 and all(c[1]<=1 for c in M) and M and M[0]==(0,0)]
        md=max(seen.values())
        total=gap=unsound=ok=0
        gap_ex=[]; uns_ex=[]
        for B0 in hosts:
            B=tuple(B0[1:]); tB=translate(B)
            if tB==Z: continue
            for x in Gterm(0,tB):
                total+=1
                real=olt(x,tB)
                got=D(x,B)
                if got and not real:
                    unsound+=1
                    if len(uns_ex)<8: uns_ex.append((B,x))
                elif real and not got:
                    gap+=1
                    if len(gap_ex)<8: gap_ex.append((B,x))
                elif real and got:
                    ok+=1
        print(f'[+{rounds}] maxdepth={md} hosts={len(hosts)} witnesses={total}')
        print(f'  schema proved (real&got)={ok}')
        print(f'  >>> GAP (real olt but schema FAILS)={gap}')
        print(f'  >>> UNSOUND (schema proves but olt FALSE)={unsound}')
        for B,x in gap_ex[:8]: print(f'    GAP B {mfmt(B)} x {tfmt(x)[:34]}')
        for B,x in uns_ex[:8]: print(f'    UNSOUND B {mfmt(B)} x {tfmt(x)[:34]}')

if __name__ == '__main__':
    main()
