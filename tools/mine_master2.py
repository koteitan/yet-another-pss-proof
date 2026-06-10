#!/usr/bin/env python3
"""E6 on the recursion-closed class: PIECES of dominated runs.

CLS := (u, S):  exists M in ST_PS, i < j <= k:  pp = M[i], u = snd pp,
       S = M[j:k] nonempty, and ALL of M[i+1:k] has row0 > fst pp.
(The translate/E6 induction descends K -> (snd c0, K) with mid=[], and
 T -> (u, T) with mid extended; this class is closed under both.)

Check on every CLS pair:
  C1: no ins-absorb along the NT spine of S; hd-subscript of NT S = snd(hd S)
  C2: pfire u (NT S) <-> msfx S != S  &  vis u S  &  lt(NT S, NT(msfx S))
  C5: fire ==> proj u (NT S) = NT (msfx S)
"""
import sys
sys.path.insert(0,'.')
from wfe_explore import translate, fmt, enum_ST
from valnorm import conv, nrm, lt_term, fmtb
from mine_proj import proj
from mine_e6 import NT
from mine_fire4 import msfx
from mine_master import vis, absorbs, maxr1

def main():
    ST=enum_ST(seed_max_v=4,oper_ns=(1,2,3,4),max_len=12,rounds=7)
    pairs=set()
    for M in ST:
        L=len(M)
        for i in range(L-1):
            a,u=M[i]
            k=i+1
            while k<L and M[k][0]>a: k+=1
            # region M[i+1:k] is the dominated run of M[i]
            for j in range(i+1,k):
                # forest-boundary: skipped columns all at >= level of M[j]
                if not all(M[l][0]>=M[j][0] for l in range(i+1,j)): continue
                for kk in range(j+1,k+1):
                    pairs.add((u,tuple(M[j:kk])))
    print('CLS pairs:',len(pairs),flush=True)
    c1=c2=c5=0
    e1=[];e2=[];e5=[]
    ntc={}
    def NTC(S):
        if S not in ntc: ntc[S]=NT(list(S))
        return ntc[S]
    for (u,S) in pairs:
        Sl=list(S)
        nt=NTC(S)
        if nt[0][1]!=Sl[0][1] or absorbs(Sl):
            c1+=1
            if len(e1)<4: e1.append((u,Sl))
        f=(proj(u,nt)!=nt)
        crit=(msfx(Sl)!=Sl) and vis(u,Sl) and lt_term(nt,NTC(tuple(msfx(Sl))))
        if f!=crit:
            c2+=1
            if len(e2)<6: e2.append((u,Sl,f))
        if f and proj(u,nt)!=NTC(tuple(msfx(Sl))):
            c5+=1
            if len(e5)<4: e5.append((u,Sl))
    print(f'C1 fail={c1}  C2 fail={c2}  C5 fail={c5}')
    for tag,e in (('C1',e1),('C2',e2),('C5',e5)):
        for x in e:
            u,S=x[0],x[1]
            print(f' {tag}: u={u} S={"".join(f"({a},{b})" for a,b in S)}'
                  + (f' fire={x[2]}' if len(x)>2 else ''))

if __name__=='__main__':
    main()
