#!/usr/bin/env python3
"""Find the row-level criterion for pfire u (NT seg) on hereditary standard
dominated segments (col, seg) from the translate decomposition.

Candidates:
  C1: fire <-> max(row1 of seg) >= row1 of seg[0]  ... i.e. some later column
      reaches/exceeds the head's row1
  C2: fire <-> max(row1 of seg[1:]) >= row1 of seg[0]
  C3: fire <-> exists j>0 with row1_j >= row1_0 and ... (dump mismatches)
Also: does u (= host col row1) matter at all?  (u <= all row1 in seg? since
dominated segments have row0 > host row0, but row1 vs u unclear -> check)
"""
import sys
sys.path.insert(0,'.')
from wfe_explore import translate, fmt, enum_ST
from valnorm import conv, nrm, lt_term, fmtb
from mine_proj import G, proj
from mine_e5 import segments, trans_abs
from mine_e6 import NT, decomp_all

def main():
    ST=enum_ST(seed_max_v=4,oper_ns=(1,2,3,4),max_len=13,rounds=7)
    NF=sorted({tuple(M) for M in ST},key=str)
    tot=0
    c1_ok=c2_ok=0
    ulow=0   # positions where u > min(row1 of seg)
    ex1=[];ex2=[]
    for M in NF:
        pairs=[]
        decomp_all(list(M),pairs)
        for (col,seg) in pairs:
            if not seg: continue
            u=col[1]
            nt=NT(seg)
            f=(proj(u,nt)!=nt)
            tot+=1
            r1=[c[1] for c in seg]
            p1 = (max(r1) >= r1[0]) if len(r1)>0 else False
            p1 = (len(r1)>=2 and max(r1[1:])>=r1[0]) or False
            c2 = (len(r1)>=2 and max(r1[1:])>=r1[0])
            c1 = (max(r1)>=r1[0]+0 and len(r1)>=2 and max(r1[1:])>=r1[0])
            if f==c2: c2_ok+=1
            elif len(ex2)<6: ex2.append((M,col,seg,f))
            if u>min(r1): ulow+=1
            if len(ex1)<0: pass
    print(f'positions={tot} C2(max tail row1 >= head row1) correct={c2_ok} wrong={tot-c2_ok}')
    print(f'u>min(row1) positions: {ulow}')
    for M,col,seg,f in ex2:
        r1=[c[1] for c in seg]
        print(f' fire={f} u={col[1]} seg={"".join(f"({x},{y})" for x,y in seg)} r1={r1}')

if __name__=='__main__':
    main()
