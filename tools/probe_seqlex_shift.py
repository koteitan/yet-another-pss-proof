#!/usr/bin/env python3
"""DECISIVE seqlex-with-shift test.

translate_shift (Mechanized:337): translate(shift(M,d)) = translate(M).
So olt(translate K)(translate B) = olt(translate(shift K))(translate B).
seqlex_imp_olt needs blockok dB on BOTH and seqlex.  Since dB=1 always, shift K so
its head row0 = 1: delta = 1 - dK.  Need all shifted row0 >= 0 i.e. >=... blockok 1
needs head=1 and all row0>=1 and steps1.

Test, on witnesses K (translate K in Gterm0(translate B)):
  (a) blockok 1 (shift K to head=1)?  (need K's internal steps1 + all-row0>=dK so
      shifted all >=1)
  (b) seqlex (shift K) B ?
  (c) does (a)&(b) hold for ALL witnesses => seqlex_imp_olt closes it.
Also test the SIMPLER possibility: maybe witnesses K satisfy seqlex(K,B) at K's OWN
depth is the wrong frame; the RIGHT frame compares shifted-K vs B.

Adversarial: report exact violation counts @+5 and +6.  One viol = dead.
"""
import sys
sys.path.insert(0, '.')
from fast_pss import Lng
from wfe_explore import translate, olt
from wfe_explore import fmt as tfmt
from fast_pss import fmt as mfmt
from probe_bmocf_ancestor import enum_depth

Z=()
def Gterm(u,t):
    if t==(): return []
    a,b,c=t; out=[]
    if u<=a: out.append(b); out+=Gterm(u,b)
    out+=Gterm(u,c); return out
def head_row0(B): return B[0][0] if B else None
def steps1(B):
    return all(B[j+1][0] <= B[j][0]+1 for j in range(len(B)-1))
def blockok(d, B):
    if not B: return True
    return B[0][0]==d and all(p[0]>=d for p in B) and steps1(B)
def shift(B, delta):
    return tuple((p[0]+delta, p[1]) for p in B)
def pairlt(p,q): return p[0]<q[0] or (p[0]==q[0] and p[1]<q[1])
def seqlex(M,N):
    M=list(M); N=list(N); i=0
    while i<len(M) and i<len(N):
        if M[i]!=N[i]: return pairlt(M[i],N[i])
        i+=1
    if i==len(M): return len(N)>len(M)
    return False
def all_subblocks(B):
    res=[]
    def rec(seg):
        seg=tuple(seg); res.append(seg)
        if not seg: return
        (x,y)=seg[0]; rest=seg[1:]; i=0
        while i<len(rest) and rest[i][0]>x: i+=1
        rec(rest[:i]); rec(rest[i:])
    rec(tuple(B)); return res

def main():
    for rounds in (5,6):
        seen=enum_depth(4,(1,2,3),28,rounds)
        hosts=[M for M in seen if Lng(M)<=18 and all(c[1]<=1 for c in M) and M and M[0]==(0,0)]
        md=max(seen.values())
        chk=0
        blockok_shift_ok=blockok_shift_bad=0
        seqlex_shift_ok=seqlex_shift_bad=0
        route_ok=route_bad=0
        bad=[]
        for B0 in hosts:
            B=tuple(B0[1:]); tB=translate(B)
            if tB==Z: continue
            dB=head_row0(B)   # =1
            okB=blockok(dB,B)
            G0=set(Gterm(0,tB))
            # map translate->subblock witness
            seenK={}
            for K in all_subblocks(B):
                tK=translate(K)
                if tK in G0 and tK not in seenK:
                    seenK[tK]=K
            for tK,K in seenK.items():
                if tK==tB or K==():
                    # empty K -> translate Z; olt(Z,tB) trivially true, skip route
                    continue
                chk+=1
                dK=head_row0(K)
                delta=dB-dK
                Ksh=shift(K,delta)
                bok=blockok(dB,Ksh)
                if bok: blockok_shift_ok+=1
                else: blockok_shift_bad+=1
                sl=seqlex(Ksh,B)
                if sl: seqlex_shift_ok+=1
                else: seqlex_shift_bad+=1
                # the route: blockok dB Ksh & blockok dB B & seqlex Ksh B => olt(tKsh,tB)=olt(tK,tB)
                if bok and okB and sl:
                    route_ok+=1
                else:
                    route_bad+=1
                    if len(bad)<10: bad.append((B,K,Ksh,dK,bok,okB,sl,olt(tK,tB)))
        print(f'[+{rounds}] maxdepth={md} hosts={len(hosts)} witness-checked={chk}')
        print(f'  blockok dB on shifted K: ok={blockok_shift_ok} BAD={blockok_shift_bad}')
        print(f'  seqlex(shifted K, B): ok={seqlex_shift_ok} BAD={seqlex_shift_bad}')
        print(f'  FULL ROUTE (bok & okB & seqlex): ok={route_ok} BAD={route_bad}')
        for B,K,Ksh,dK,bok,okB,sl,realolt in bad[:10]:
            print(f'    ROUTEBAD B {mfmt(B)} K {mfmt(K)} dK={dK} Ksh {mfmt(Ksh)} bok={bok} okB={okB} seqlex={sl} REALolt={realolt}')

if __name__ == '__main__':
    main()
