#!/usr/bin/env python3
"""E6'': fire <-> j0>0 and lt_term(NT seg, NT seg[j0:]) and visible(u, seg, j0)
where visible = every ancestor of j0 in the row0-forest of seg has row1 >= u.

ancestors(j) = k < j with row0_k < row0_i for all i in (k, j]   (the columns
whose dominated segment contains column j).

Also re-verify E6 (proj = NT suffix) on fire cases, and dump the relation of
j0 to its ancestors (is the cut a clean forest point: does seg[j0:] start a
fresh tree at top level of seg? i.e. ancestors(j0) = {} ?).
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
    return r1.index(max(r1))

def ancestors(seg,j):
    out=[]
    for k in range(j):
        if all(seg[k][0]<seg[i][0] for i in range(k+1,j+1)):
            out.append(k)
    return out

def main():
    ST=enum_ST(seed_max_v=4,oper_ns=(1,2,3,4),max_len=13,rounds=7)
    NF=sorted({tuple(M) for M in ST},key=str)
    tot=0; ok=0; ex=[]
    e6bad=0; anc_hist={}
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
            anc=ancestors(seg,j)
            cand=(j>0) and lt_term(nt,NT(seg[j:])) and all(seg[k][1]>=u for k in anc)
            if f==cand: ok+=1
            elif len(ex)<8: ex.append((M,col,seg,f,cand,anc))
            if f:
                if NT(seg[j:])!=proj(u,nt): e6bad+=1
                anc_hist[len(anc)]=anc_hist.get(len(anc),0)+1
    print(f'positions={tot}  E6pp correct={ok} wrong={tot-ok}   E6-suffix-bad={e6bad}')
    print('fire-case ancestor-count hist:',anc_hist)
    for M,col,seg,f,cand,anc in ex:
        print(f' fire={f} cand={cand} u={col[1]} anc={anc} seg={"".join(f"({x},{y})" for x,y in seg)}')
        j=j0(seg)
        print(f'   NTseg={fmtb(NT(seg))[:70]}')
        print(f'   NTsfx={fmtb(NT(seg[j:]))[:70]}')

if __name__=='__main__':
    main()
