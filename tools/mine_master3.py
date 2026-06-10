#!/usr/bin/env python3
"""E6 on the EXACT descent closure (= the inductive class dcls planned for
Isabelle):

base:   (snd pp, S) for pre@(pp#S)@post in ST_PS, S nonempty, S all-dominated
        by pp  (post arbitrary: S = M[i+1:k] for any k inside the run)
desc_K: (u, c#rest) -> (snd c, takeWhile (fst c <) rest)    if nonempty
desc_T: (u, c#rest) -> (u, dropWhile (fst c <) rest)        if nonempty

Check C1 (no-absorb + hd subscript), C2 (fire criterion), C5 (proj value),
separately for base pairs and for descended pairs.
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
    base=set()
    for M in ST:
        L=len(M)
        for i in range(L-1):
            a,u=M[i]
            k=i+1
            while k<L and M[k][0]>a:
                base.add((u,tuple(M[i+1:k+1])))
                k+=1
    # closure
    seen=set(base)
    frontier=list(base)
    while frontier:
        nf=[]
        for (u,S) in frontier:
            c,rest=S[0],list(S[1:])
            i=0
            while i<len(rest) and rest[i][0]>c[0]: i+=1
            K,T=tuple(rest[:i]),tuple(rest[i:])
            for p in ((c[1],K) if K else None,(u,T) if T else None):
                if p and p not in seen:
                    seen.add(p); nf.append(p)
        frontier=nf
    print(f'base={len(base)} closure={len(seen)}',flush=True)
    stats={'base':[0,0,0],'desc':[0,0,0]}
    ex=[]
    ntc={}
    def NTC(S):
        if S not in ntc: ntc[S]=NT(list(S))
        return ntc[S]
    for (u,S) in seen:
        kind='base' if (u,S) in base else 'desc'
        Sl=list(S)
        nt=NTC(S)
        bad1=(nt[0][1]!=Sl[0][1]) or absorbs(Sl)
        f=(proj(u,nt)!=nt)
        crit=(msfx(Sl)!=Sl) and vis(u,Sl) and lt_term(nt,NTC(tuple(msfx(Sl))))
        bad2=(f!=crit)
        bad5=f and proj(u,nt)!=NTC(tuple(msfx(Sl)))
        for ix,b in enumerate((bad1,bad2,bad5)):
            if b: stats[kind][ix]+=1
        if (bad1 or bad2 or bad5) and len(ex)<8:
            ex.append((kind,u,Sl,bad1,bad2,bad5))
    print('fails [C1,C2,C5]: base',stats['base'],' desc',stats['desc'])
    for kind,u,S,b1,b2,b5 in ex:
        print(f' {kind} u={u} C1={b1} C2={b2} C5={b5} S={"".join(f"({a},{b})" for a,b in S)}')

if __name__=='__main__':
    main()
