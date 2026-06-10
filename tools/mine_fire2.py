#!/usr/bin/env python3
"""E6': uniform characterization of proj on hereditary standard dominated segs.

  maxsfx(seg) = seg[j0:] where j0 = first index with row1 = max(row1 of seg)

  Claim A: pfire u (NT seg)  <->  j0 > 0  and  lt_term(NT seg, NT seg[j0:])
  Claim B: pfire -> proj u (NT seg) = NT(seg[j0:])     (E6, known)
  Claim C: does the u-condition (max row1 >= u?) ever bite, i.e. is there a
           position with j0>0 and lt_term but NO fire because levels < u?
"""
import sys
sys.path.insert(0,'.')
from wfe_explore import translate, fmt, enum_ST
from valnorm import conv, nrm, lt_term, fmtb
from mine_proj import G, proj
from mine_e5 import segments, trans_abs
from mine_e6 import NT, decomp_all

def j0(seg):
    r1=[c[1] for c in seg]
    m=max(r1)
    return r1.index(m)

def main():
    ST=enum_ST(seed_max_v=4,oper_ns=(1,2,3,4),max_len=13,rounds=7)
    NF=sorted({tuple(M) for M in ST},key=str)
    tot=0; a_ok=0; exa=[]
    ufail=0; exu=[]
    for M in NF:
        pairs=[]
        decomp_all(list(M),pairs)
        for (col,seg) in pairs:
            if not seg: continue
            u=col[1]
            nt=NT(seg)
            f=(proj(u,nt)!=nt)
            tot+=1
            j=j0(seg)
            cand = (j>0) and lt_term(nt, NT(seg[j:]))
            if f==cand: a_ok+=1
            elif len(exa)<8:
                exa.append((M,col,seg,f,cand))
            if cand and not f:
                ufail+=1
                if len(exu)<5: exu.append((M,col,seg))
    print(f'positions={tot}  ClaimA correct={a_ok} wrong={tot-a_ok}  cand-but-nofire={ufail}')
    for M,col,seg,f,cand in exa:
        r1=[c[1] for c in seg]
        print(f' fire={f} cand={cand} u={col[1]} seg={"".join(f"({x},{y})" for x,y in seg)}')
        print(f'   NTseg={fmtb(NT(seg))[:60]}  NTsfx={fmtb(NT(seg[j0(seg):]))[:60]}')

if __name__=='__main__':
    main()
