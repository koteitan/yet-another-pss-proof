#!/usr/bin/env python3
"""Deep (+extra and deep-family) true/false partition of the value-side
'keep candidates' for route A. Checks LITERAL conclusions."""
import sys
sys.path.insert(0, '.')
from fast_pss import oper
from wfe_explore import enum_ST
from valnorm import lt_term
from mine_e6 import NT
from mine_proj import G, proj
from mine_fire4 import msfx

NTC={}
def nt(S):
    S=tuple(S)
    if S not in NTC: NTC[S]=NT(list(S))
    return NTC[S]
def lead(t): return t[0][1] if t else 0   # hdsub; Z repr = ()
def isZ(t): return t==() or t is None or (isinstance(t,(list,tuple)) and len(t)==0)
def ole(a,b): return a==b or lt_term(a,b)
def pfire(u,t): return any(not lt_term(g,t) for g in G(u,t))
def maxr1(S): return max(c[1] for c in S)

def hosts_plus(extra):
    ST=enum_ST(seed_max_v=4,oper_ns=(1,2,3,4),max_len=13,rounds=7)
    out=set(ST); cur=list(out)
    for i in range(extra):
        new=[]
        for M in cur:
            if len(M)<2: continue
            for n in (1,2,3,4):
                t=tuple(oper(list(M),n))
                if t not in out: out.add(t); new.append(t)
        cur=new
    return out
def deepfam():
    seed=[(0,0),(1,1),(2,2),(3,0),(4,1),(5,2),(6,0),(7,1),(8,2),(8,0)]
    fam=set(); fr=[tuple(seed)]
    for _ in range(4):
        nf=[]
        for Sx in fr:
            for n in (1,2,3,4,5):
                T=tuple(oper(list(Sx),n))
                if len(T)<=16 and T not in fam: fam.add(T); nf.append(T)
        fr=nf
    return fam

def dsegs(H):
    lh=len(H)
    for ppi in range(lh):
        lv=H[ppi][0]; dend=ppi+1
        while dend<lh and H[dend][0]>lv: dend+=1
        for k in range(ppi+2,dend+1):
            yield (H[ppi][1], tuple(H[ppi+1:k]))
def segprovs(H):
    """(u, S, q): pp#S@[q] dominated, fst pp<fst q."""
    lh=len(H)
    for ppi in range(lh):
        lv=H[ppi][0]; dend=ppi+1
        while dend<lh and H[dend][0]>lv: dend+=1
        # q is at position dend (first <= lv) OR any pos; require fst pp<fst q
        for k in range(ppi+1,dend):       # S = H[ppi+1:k+1], q=H[k+1]
            qi=k+1
            if qi>=lh: continue
            S=tuple(H[ppi+1:qi]); q=H[qi]
            if not S: continue
            if lv<q[0]:
                yield (H[ppi][1],S,q)

def audit(HS,label):
    c=dict(g6=0,smin=0,sinv=0,qdiag=0,fbs=0,top=0,tie=0)
    b=dict(g6=0,smin=0,sinv=0,qdiag=0,fbs=0,top=0,tie=0)
    ex={}
    seen=set()
    for H in HS:
        # dseg-based: G6
        for (u,S) in dsegs(H):
            if ('d',u,S) in seen: continue
            seen.add(('d',u,S)); Sl=list(S)
            tS=nt(Sl); m=maxr1(Sl); tm=nt(msfx(Sl))
            for g in G(u,tS):
                if isZ(g): continue
                if lead(g)!=m: continue
                c['g6']+=1
                if not ole(g,tm):
                    b['g6']+=1; ex.setdefault('g6',(u,S))
            # tie (NT_tie_resolved)
            c0=Sl[0]; rest=Sl[1:]
            i=0
            while i<len(rest) and rest[i][0]>c0[0]: i+=1
            K,T=rest[:i],rest[i:]
            if T and T[0][1]==c0[1]:
                c1=T[0]; rest1=T[1:]
                j=0
                while j<len(rest1) and rest1[j][0]>c1[0]: j+=1
                K1=rest1[:j]
                A=proj(c0[1],nt(K)) if K else proj(c0[1],())
                A1=proj(c1[1],nt(K1)) if K1 else proj(c1[1],())
                c['tie']+=1
                if lt_term(A,A1): b['tie']+=1; ex.setdefault('tie',(u,S))
        # segprov-based: seam_MIN/INV, QDIAG, FBS
        for (u,S,q) in segprovs(H):
            if ('s',u,S,q) in seen: continue
            seen.add(('s',u,S,q)); Sl=list(S)
            tS=nt(Sl); tSq=nt(Sl+[q]); m=maxr1(Sl); ms=msfx(Sl)
            fS=pfire(u,tS); fSq=pfire(u,tSq)
            if fS:
                c['smin']+=1
                if not all(ms[0][0]<=x[0] for x in ms):
                    b['smin']+=1; ex.setdefault('smin',(u,S,q))
            if fS and q[1]<=m:
                c['sinv']+=1
                if not ms[0][0]<=q[0]:
                    b['sinv']+=1; ex.setdefault('sinv',(u,S,q))
            if fSq and m<q[1]:
                for ii in range(len(Sl)-1):
                    c['qdiag']+=1
                    if not Sl[ii][1]<Sl[ii+1][1]:
                        b['qdiag']+=1; ex.setdefault('qdiag',(u,S,q)); break
            if len(Sl)>=2 and fSq:
                c['fbs']+=1
                if not fS:
                    b['fbs']+=1; ex.setdefault('fbs',(u,S,q))
    print(f'== {label} ==')
    for k in c:
        print('  %-6s %8d inst  %5d viol  %s'%(k,c[k],b[k],ex.get(k,'')))

for e in (3,):
    audit(hosts_plus(e),f'+{e}')
audit(deepfam(),'deepfam')
