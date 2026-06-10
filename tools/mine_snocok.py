#!/usr/bin/env python3
"""Port snocok to python and evaluate on (butlast M, last M) for all standard M.
Validates the three leaf obligations ST_snoc_A/B/C empirically."""
import sys
sys.path.insert(0,'.')
from wfe_explore import translate, fmt, enum_ST
from valnorm import conv, nrm, lt_term, fmtb
from mine_proj import proj

def trans(C): return nrm(conv(translate(list(C))))

def hdsub(t): return t[0][1] if t else 0
def hdarg(t): return t[0][2] if t else ()

def snocok(C,q,trace):
    if not C: return False
    p,rest=C[0],C[1:]
    i=0
    while i<len(rest) and rest[i][0]>p[0]: i+=1
    K,T=rest[:i],rest[i:]
    if not T:
        if p[0]<q[0]:
            ok=lt_term(proj(p[1],trans(rest)),proj(p[1],trans(list(rest)+[q])))
            if not ok: trace.append(('C',C,q))
            return ok
        else:
            ok=q[1]<=p[1]
            if not ok: trace.append(('A',C,q))
            return ok
    else:
        pb=proj(p[1],trans(K))
        t1,t2=trans(T),trans(list(T)+[q])
        na1=not(p[1]<hdsub(t1) or (p[1]==hdsub(t1) and lt_term(pb,hdarg(t1))))
        na2=not(p[1]<hdsub(t2) or (p[1]==hdsub(t2) and lt_term(pb,hdarg(t2))))
        if not na1: trace.append(('B1',C,q))
        if not na2: trace.append(('B2',C,q))
        return snocok(T,q,trace) and na1 and na2

def main():
    ST=enum_ST(seed_max_v=4,oper_ns=(1,2,3,4),max_len=13,rounds=7)
    tot=ok=0; bad=[]
    for M in ST:
        if len(M)<2: continue
        C,q=list(M[:-1]),M[-1]
        tr=[]
        tot+=1
        if snocok(C,q,tr): ok+=1
        else: bad.append((M,tr))
    print(f'standard hosts: {tot}, snocok holds: {ok}, fails: {len(bad)}')
    kinds={}
    for M,tr in bad:
        for k,_,_ in tr: kinds[k]=kinds.get(k,0)+1
    print('violation kinds:',kinds)
    for M,tr in bad[:5]:
        print(' M=',''.join(f'({x},{y})' for x,y in M),' viol:',[k for k,_,_ in tr])

if __name__=='__main__':
    main()
