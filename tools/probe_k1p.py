#!/usr/bin/env python3
"""K1' : host-free argument domination with a SIMPLE (list-level) side condition.

N in ST_PS,  N = X ++ ((u,w) :: A) ++ Z   with A = arg of the column (u,w),
A = A1 ++ ((u+e,w) :: B) ++ A2  with B = arg of the column (u+e,w), e>0.
SIDE CONDITION (candidate): forall x in A1 with x.1 < u+e :  w <= x.2.
CLAIM:  sle B (shiftr0 e A).
Also tested: T6 = does the side condition hold in the AscArgDom instances?
"""
import sys, collections
sys.path.insert(0, '.')
from probe_bmocf_ancestor import enum_depth
from probe_copycrux import pairlt, seqlex, sle, shiftr0, copies
from fast_pss import le0, Lng, fmt
from probe_ascarg_struct import instances

def arg(N, i):
    lv = N[i][0]; out = []
    for p in N[i+1:]:
        if p[0] > lv: out.append(p)
        else: break
    return out

def run_k1p(vmax, ns, ml, rounds, cond):
    hosts = sorted(set(tuple(M) for M in enum_depth(vmax, ns, ml, rounds)
                       if len(M) >= 2 and M[0] == (0,0)))
    tot = 0; viol = 0; exs = []
    for N in hosts:
        Nl = list(N); n = len(Nl)
        for i in range(n):
            A = arg(Nl, i); u, w = Nl[i]
            for t in range(len(A)):
                if A[t][1] != w: continue
                e = A[t][0] - u
                if e <= 0: continue
                A1 = A[:t]; B = arg(Nl, i+1+t)
                if not cond(A1, u, e, w): continue
                tot += 1
                if not sle(B, shiftr0(e, A)):
                    viol += 1
                    if len(exs) < 4: exs.append((N, i, i+1+t, A1, B, shiftr0(e, A)))
    print(f"  K1' v<={vmax} rounds={rounds} ml={ml}: instances={tot} VIOL={viol}")
    for x in exs: print("     ", fmt(x[0]), "i=",x[1],"j=",x[2], "A1=",x[3], "B=",x[4], "shA=",x[5])

cond_simple = lambda A1,u,e,w: all(x[1] >= w for x in A1 if x[0] < u+e)
cond_none   = lambda A1,u,e,w: True
cond_strict = lambda A1,u,e,w: all(x[1] >= w+1 for x in A1 if x[0] < u+e)

print("== no side condition (expected FALSE) ==");  run_k1p(4,(1,2,3),10,5, cond_none)
print("== simple side condition  w <= x.2 for x in A1 with x.1<u+e ==")
run_k1p(4,(1,2,3),10,5, cond_simple); run_k1p(5,(1,2,3,4,5),11,7, cond_simple)

# T6: does the simple side condition hold on the AscArgDom instances?
tot=0;bad=0;exs=[]
for inst in instances(8,11,5,(1,2,3,4,5)):
    tot+=1
    R=inst['R']; v0=inst['v0']; w0=inst['w0']; d0=inst['d0']
    if not all(x[1]>=w0 for x in R if x[0] < v0+d0):
        bad+=1
        if len(exs)<4: exs.append(inst)
print(f"T6 (side condition on R in AscArgDom instances): {tot} inst, {bad} failures")
for e in exs: print("   ", fmt(e['M']), 'R=',e['R'],'v0,w0,d0=',e['v0'],e['w0'],e['d0'])
