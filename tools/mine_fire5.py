#!/usr/bin/env python3
"""E6 master lemma exactly on the projE class:

segprov positions: M in ST_PS, q = M[-1], pp = M[i], S = M[i+1:-1] nonempty,
all of S dominated by pp, fst pp < fst q, u = snd pp.

Test E6 on BOTH x-side (S, possibly non-maximal: q missing) and x'-side (S@[q],
the maximal dominated segment of pp in M):
   pfire u (NT T) ==> proj u (NT T) = NT (msfx T)
Also: in both-fire cases, classify snd q vs max-row1 of S (for the Einc step):
   m' = max r1 of S@[q]:  q-cut (snd q > m) vs same-cut (snd q <= m, msfx
   extends by q) -- and verify msfx(S@[q]) = msfx(S)@[q] in the latter.
"""
import sys
sys.path.insert(0,'.')
from wfe_explore import translate, fmt, enum_ST
from valnorm import conv, nrm, lt_term, fmtb
from mine_proj import G, proj
from mine_e6 import NT
from mine_fire4 import msfx

def main():
    ST=enum_ST(seed_max_v=4,oper_ns=(1,2,3,4),max_len=13,rounds=7)
    nS=badS=nQ=badQ=0
    both=qcut=qcut_leaf=samecut=scfail=0
    ex=[]
    for M in ST:
        if len(M)<2: continue
        q=M[-1]
        for i in range(len(M)-1):
            pp=M[i]; S=list(M[i+1:-1])
            if not S: continue
            if not all(pp[0]<r[0] for r in S): continue
            if not pp[0]<q[0]: continue
            u=pp[1]
            x=NT(S); x2=NT(S+[q])
            px=proj(u,x); px2=proj(u,x2)
            fx=(px!=x); fx2=(px2!=x2)
            if fx:
                nS+=1
                if px!=NT(msfx(S)):
                    badS+=1
                    if len(ex)<4: ex.append(('S',M,i,px))
            if fx2:
                nQ+=1
                if px2!=NT(msfx(S+[q])):
                    badQ+=1
                    if len(ex)<4: ex.append(('SQ',M,i,px2))
            if fx and fx2:
                both+=1
                m=max(c[1] for c in S)
                if q[1]>m:
                    qcut+=1
                    if len(NT(msfx(S+[q])))==1 and not NT(msfx(S+[q]))[0][2]:
                        qcut_leaf+=1
                else:
                    samecut+=1
                    if msfx(S+[q])!=msfx(S)+[q]:
                        scfail+=1
                        if len(ex)<6: ex.append(('SC',M,i,None))
    print(f'S-side fires={nS} E6-bad={badS}   SQ-side fires={nQ} E6-bad={badQ}')
    print(f'both-fire={both}: q-cut={qcut} (proj-leaf={qcut_leaf})  same-cut={samecut} (msfx-append-fail={scfail})')
    for k,M,i,p in ex:
        print(f' {k}: i={i} M={"".join(f"({x},{y})" for x,y in M)}')
        if p is not None: print('   proj=',fmtb(p)[:70])

if __name__=='__main__':
    main()
