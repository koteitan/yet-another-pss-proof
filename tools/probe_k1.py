#!/usr/bin/env python3
"""K1: host-free 'row-1 sibling argument domination'.

For N in ST_PS and indices i<j with
   le0 N i j,  row1(i)=row1(j)=w,  e := lvl(j)-lvl(i) > 0,
   and every strict row-0 ancestor k of j with i<k<j has row1(k) >= w
                       (<=> i and j are row-1 SIBLINGS)
claim:   sle (arg_N j) (shiftr0 e (arg_N i)).
"""
import sys, collections
sys.path.insert(0, '.')
from probe_bmocf_ancestor import enum_depth
from probe_copycrux import pairlt, seqlex, sle, shiftr0, copies
from fast_pss import le0, Lng, fmt

def arg(N, i):
    lv = N[i][0]
    out = []
    for p in N[i+1:]:
        if p[0] > lv: out.append(p)
        else: break
    return out

def run(vmax, ns, ml, rounds, strictver=False):
    hosts = sorted(set(tuple(M) for M in enum_depth(vmax, ns, ml, rounds)
                       if len(M) >= 2 and M[0] == (0,0)))
    tot = 0; viol = 0; exs = []
    for N in hosts:
        Nl = list(N); n = len(Nl)
        for i in range(n):
            for j in range(i+1, n):
                if Nl[i][1] != Nl[j][1]: continue
                if Nl[j][0] <= Nl[i][0]: continue
                if not le0(N, i, j): continue
                w = Nl[i][1]
                # row-1 sibling condition
                ok = True
                for k in range(i+1, j):
                    if le0(N, k, j) and Nl[k][1] < w + (1 if strictver else 0):
                        ok = False; break
                if not ok: continue
                e = Nl[j][0] - Nl[i][0]
                tot += 1
                if not sle(arg(Nl, j), shiftr0(e, arg(Nl, i))):
                    viol += 1
                    if len(exs) < 4: exs.append((N, i, j))
    print(f"  v<= {vmax} rounds={rounds} maxlen={ml} strict={strictver}: instances={tot} VIOL={viol}")
    for (N,i,j) in exs:
        print("     ", fmt(N), " i=",i," j=",j, " arg_j=",arg(list(N),j), " shift arg_i=", shiftr0(list(N)[j][0]-list(N)[i][0], arg(list(N),i)))

for (vm, ns, ml, rd) in [(4,(1,2,3),10,5),(5,(1,2,3,4,5),11,7)]:
    run(vm, ns, ml, rd)
