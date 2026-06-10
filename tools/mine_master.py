#!/usr/bin/env python3
"""Final validation suite for the E6 master-lemma campaign, on the class
   CLS = dominated segments arising in segprov positions (both S and S@[q])
         of standard hosts.

V1 (no-absorb / nrm_hd): for class segs, hd subscript of NT S = snd (hd S),
    and at every level of the NT recursion ins never absorbs.
V2 (criterion, host u):  pfire u (NT S) <-> msfx S != S  &  vis u S  &
                         lt_term(NT S, NT(msfx S))      [u = snd pp]
V3 (criterion, all u in 0..6): same, for every u (needed if sibling levels
    differ from host level).
V4 (q-cut shape): both-fire & snd q > maxr1 S  ==>  msfx S = [last col of S]
    (then NT(msfx S) is a leaf with subscript maxr1 S < snd q).
V5 (iii-shape): x-nofire & x'-fire ==> S singleton  OR  msfx S = S.
"""
import sys
sys.path.insert(0,'.')
from wfe_explore import translate, fmt, enum_ST
from valnorm import conv, nrm, lt_term, fmtb
from mine_proj import G, proj
from mine_e6 import NT
from mine_fire4 import msfx

def maxr1(S): return max(c[1] for c in S)

def vis(u,S):
    if not S: return True
    c0,rest=S[0],S[1:]
    i=0
    while i<len(rest) and rest[i][0]>c0[0]: i+=1
    K,T=rest[:i],rest[i:]
    m=maxr1(S)
    if c0[1]==m: return True
    if K and maxr1(K)==m: return c0[1]>=u and vis(u,K)
    return vis(u,T)

def absorbs(S):
    """does ins absorb anywhere along the NT spine of S?"""
    S=list(S)
    while S:
        c0,rest=S[0],S[1:]
        i=0
        while i<len(rest) and rest[i][0]>c0[0]: i+=1
        K,T=rest[:i],rest[i:]
        if K and absorbs(K): return True
        nt_T=NT(T)
        if nt_T:
            a=c0[1]; b=proj(a,NT(K))
            e,f=nt_T[0][1],nt_T[0][2]
            if a<e or (a==e and lt_term(b,f)): return True
        S=T
    return False

def main():
    ST=enum_ST(seed_max_v=4,oper_ns=(1,2,3,4),max_len=13,rounds=7)
    cls={}
    for M in ST:
        if len(M)<2: continue
        q=M[-1]
        for i in range(len(M)-1):
            pp=M[i]; S=tuple(M[i+1:-1])
            if not S: continue
            if not all(pp[0]<r[0] for r in S): continue
            if not pp[0]<q[0]: continue
            cls.setdefault(S,set()).add((pp[1],q,'S'))
            cls.setdefault(S+(q,),set()).add((pp[1],q,'SQ'))
    print('class segments:',len(cls),flush=True)
    v1=v2=v3=v4=v5=0
    e1=[];e2=[];e3=[];e4=[];e5=[]
    for S,ctxs in cls.items():
        S=list(S)
        nt=NT(S)
        if nt[0][1]!=S[0][1] or absorbs(S):
            v1+=1
            if len(e1)<4: e1.append(S)
        crit=lambda u:(msfx(S)!=S) and vis(u,S) and lt_term(nt,NT(msfx(S)))
        for u in range(0,7):
            f=(proj(u,nt)!=nt)
            if f!=crit(u):
                v3+=1
                if len(e3)<4: e3.append((S,u,f))
        for (u,q,kind) in ctxs:
            f=(proj(u,nt)!=nt)
            if f!=crit(u):
                v2+=1
                if len(e2)<4: e2.append((S,u,f))
            if kind=='S':
                x2=NT(S+[q]); fx2=(proj(u,x2)!=x2)
                if f and fx2 and q[1]>maxr1(S):
                    if msfx(S)!=[S[-1]]:
                        v4+=1
                        if len(e4)<4: e4.append((S,q))
                if (not f) and fx2:
                    if len(S)>1 and msfx(S)!=S:
                        v5+=1
                        if len(e5)<4: e5.append((S,q))
    print(f'V1 absorb/hd-fail: {v1}')
    print(f'V2 criterion(host u) fail: {v2}')
    print(f'V3 criterion(all u) fail: {v3}')
    print(f'V4 q-cut not-last-col: {v4}')
    print(f'V5 iii-shape fail: {v5}')
    for tag,e in (('V1',e1),('V2',e2),('V3',e3),('V4',e4),('V5',e5)):
        for x in e:
            print(f' {tag}:',x)

if __name__=='__main__':
    main()
