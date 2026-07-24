#!/usr/bin/env python3
"""Are the two side conditions for K1 equivalent on ST_PS?
 (a) le0-form:  every row-0 ancestor k of j with i<k<j has row1(k) >= w
 (b) list-form: every column x strictly between i and j with lvl(x) < lvl(j) has row1(x) >= w
Also: bigger-closure test of T6 (list-form condition on R in AscArgDom instances).
"""
import sys
sys.path.insert(0, '.')
from probe_bmocf_ancestor import enum_depth
from probe_copycrux import sle, shiftr0
from fast_pss import le0, fmt
from probe_ascarg_struct import instances

def arg(N,i):
    lv=N[i][0]; out=[]
    for p in N[i+1:]:
        if p[0]>lv: out.append(p)
        else: break
    return out

def run(vmax, ns, ml, rounds):
    hosts = sorted(set(tuple(M) for M in enum_depth(vmax, ns, ml, rounds)
                       if len(M)>=2 and M[0]==(0,0)))
    ab=ba=both=0; exs_ab=[]; exs_ba=[]
    for N in hosts:
        Nl=list(N); n=len(Nl)
        for i in range(n):
            u,w = Nl[i]
            A = arg(Nl,i)
            for t in range(len(A)):
                if A[t][1]!=w: continue
                e = A[t][0]-u
                if e<=0: continue
                j = i+1+t; A1=A[:t]
                a = all((not le0(N,k,j)) or Nl[k][1]>=w for k in range(i+1,j))
                b = all(x[1]>=w for x in A1 if x[0] < u+e)
                if a and b: both+=1
                elif a and not b:
                    ab+=1
                    if len(exs_ab)<3: exs_ab.append((N,i,j,A1))
                elif b and not a:
                    ba+=1
                    if len(exs_ba)<3: exs_ba.append((N,i,j,A1))
    print(f" v<={vmax} r={rounds}: both={both}  le0only={ab}  listonly={ba}")
    for x in exs_ab: print("   le0only:", fmt(x[0]),"i=",x[1],"j=",x[2],"A1=",x[3])
    for x in exs_ba: print("   listonly:", fmt(x[0]),"i=",x[1],"j=",x[2],"A1=",x[3])

run(4,(1,2,3),10,5)
run(5,(1,2,3,4,5),11,7)

# bigger T6 sweep
for (rounds,ml,vmax,ns) in [(9,13,5,(1,2,3,4,5)),(7,14,6,(1,2,3,4,5,6))]:
    tot=0;bad=0;offspine=0;exs=[]
    for inst in instances(rounds,ml,vmax,ns):
        tot+=1
        R=inst['R'];v0=inst['v0'];w0=inst['w0'];d0=inst['d0']
        low=[x for x in R if x[0]<v0+d0]
        if len(low) > d0-1: offspine+=1
        if not all(x[1]>=w0 for x in low):
            bad+=1
            if len(exs)<3: exs.append(inst)
    print(f"T6 rounds={rounds} ml={ml} vmax={vmax}: inst={tot} FAIL={bad}  (instances with off-spine low columns: {offspine})")
    for e in exs: print("   ",fmt(e['M']),'R=',e['R'],e['v0'],e['w0'],e['d0'])
