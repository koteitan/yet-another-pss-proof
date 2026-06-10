#!/usr/bin/env python3
"""Internal-position versions of the class facts: q at ANY position
(not just host end).  Positions: M in ST_PS, i < j < len(M):
pp=M[i], S=M[i+1:j] nonempty all-dominated by pp, q=M[j], fst pp < fst q.

Facts:
  W2 (criterion S-side, internal):  pfire u (NT S) <-> msfx-criterion
  W2q (criterion SQ-side):          same for S@[q]
  W5 (E6 value, both sides)
  V4i (q-cut): both-fire & snd q > maxr1 S ==> msfx S = [last S]
  V5i (iii):   nofire-S & fire-SQ ==> S singleton
  SEAMi: both-fire same-cut ==> INV & INV2 for msfx S vs q
  STSAi: fst q = fst p case is not relevant here (q dominated): skip.
"""
import sys
sys.path.insert(0,'.')
from wfe_explore import translate, fmt, enum_ST
from valnorm import conv, nrm, lt_term, fmtb
from mine_proj import proj
from mine_e6 import NT
from mine_fire4 import msfx
from mine_master import vis, maxr1

def main():
    ST=enum_ST(seed_max_v=4,oper_ns=(1,2,3,4),max_len=12,rounds=7)
    seen=set()
    n=0
    w2=w2q=w5=v4=v5=seam=0
    ex=[]
    ntc={}
    def NTC(S):
        S=tuple(S)
        if S not in ntc: ntc[S]=NT(list(S))
        return ntc[S]
    for M in ST:
        L=len(M)
        for i in range(L-2):
            pp=M[i]
            for j in range(i+2,L):
                S=list(M[i+1:j]); q=M[j]
                if not all(pp[0]<r[0] for r in S): break
                if not pp[0]<q[0]: continue
                key=(pp[1],tuple(S),q)
                if key in seen: continue
                seen.add(key)
                n+=1
                u=pp[1]
                x=NTC(S); x2=NTC(S+[q])
                px=proj(u,x); px2=proj(u,x2)
                fx=(px!=x); fx2=(px2!=x2)
                crit=(msfx(S)!=S) and vis(u,S) and lt_term(x,NTC(msfx(S)))
                S2=S+[q]
                crit2=(msfx(S2)!=S2) and vis(u,S2) and lt_term(x2,NTC(msfx(S2)))
                if fx!=crit: w2+=1; ex.append(('W2',M,i,j))
                if fx2!=crit2: w2q+=1; ex.append(('W2q',M,i,j))
                if fx and px!=NTC(msfx(S)): w5+=1; ex.append(('W5',M,i,j))
                if fx2 and px2!=NTC(msfx(S2)): w5+=1; ex.append(('W5q',M,i,j))
                m=maxr1(S)
                if fx and fx2 and q[1]>m and msfx(S)!=[S[-1]]:
                    v4+=1; ex.append(('V4',M,i,j))
                if (not fx) and fx2 and len(S)>1:
                    v5+=1; ex.append(('V5',M,i,j))
                if fx and fx2 and q[1]<=m:
                    T=msfx(S)
                    if not (T[0][0]<=q[0] and all(T[0][0]<=x_[0] for x_ in T)):
                        seam+=1; ex.append(('SEAM',M,i,j))
    print(f'internal positions={n}')
    print(f'W2={w2} W2q={w2q} W5={w5} V4i={v4} V5i={v5} SEAMi={seam}')
    for t in ex[:8]:
        k,M,i,j=t
        print(f' {k}: i={i} j={j} M={"".join(f"({a},{b})" for a,b in M)}')

if __name__=='__main__':
    main()
