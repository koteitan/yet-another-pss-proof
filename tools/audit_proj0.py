#!/usr/bin/env python3
"""Self-contained audit in the Lean Three (a,b,c) encoding.
Confirms (on NF args):
  - pfire 0 b characterization
  - proj0_fireprop_NF : olt b f -> pfire 0 b -> pfire 0 f
  - proj0_bothfire_NF : olt b f -> pfire 0 b -> pfire 0 f -> olt (proj0 b)(proj0 f)
  - structural key proj 0 (P 1 b' c') = proj 0 b'
NF args = the b in P 0 b c that are NF (i.e. translate ST_PS terms of shape P 0 b c).
"""
import sys
sys.path.insert(0,'.')
from wfe_explore import translate, enum_ST, spine, maxsub, olt
Z=()

def le(s,t): return s==t or olt(s,t)

def Gterm(u,t):
    """matches Lean Gterm u (Three)."""
    if t==Z: return []
    a,b,c=t
    out=[]
    if u<=a:
        out.append(b); out+=Gterm(u,b)
    out+=Gterm(u,c)
    return out

def pfire(u,b):
    return any(not olt(g,b) for g in Gterm(u,b))

def proj(u,b):
    while True:
        bad=[g for g in Gterm(u,b) if not olt(g,b)]
        if not bad: return b
        m=bad[0]
        for h in bad[1:]:
            if olt(m,h): m=h
        b=m

def lead(t): return 0 if t==Z else t[0]

def main():
    ST=enum_ST(seed_max_v=4,oper_ns=(1,2,3,4),max_len=13,rounds=7)
    NF=sorted({translate(M) for M in ST},key=str)
    # collect NF args b: those appearing as the argument of P 0 b c in some NF term,
    # AND b itself in NF? The Lean statement requires P 0 b c in NF and P 0 f g in NF.
    nfargs=[]  # (b, full P0 term)
    for t in NF:
        if t==Z: continue
        a,b,c=t
        if a==0:
            nfargs.append((b,t))
    # characterization of pfire 0 b on these args
    chk_charac={}
    miss=[]
    for b,_ in nfargs:
        f=pfire(0,b)
        # candidate: ascent = maxsub b > lead b
        cand = (maxsub(b) > lead(b))
        chk_charac[id(b)]=(f,cand)
        if f!=cand and len(miss)<8: miss.append((b,f,cand,spine(b),lead(b),maxsub(b)))
    nbad=sum(1 for b,_ in nfargs if pfire(0,b)!=(maxsub(b)>lead(b)))
    print(f"NF args(P0): {len(nfargs)}  pfire0<->maxsub>lead mismatches: {nbad}")
    for m in miss: print("  CHARAC MISS",m)

    # spine shifted-inv2 of args: spine(b) == list(range(lead?+1.. )) consecutive from lead b?
    # plan: whole term P 0 b c spine = 0::spine(b) and is inv2 = [0,1,...,maxsub]
    # so spine(b) = [1,2,...] consecutive +1. check spine of FULL P0 terms.
    sbad=0
    for b,t in nfargs:
        s=spine(t)  # = 0::spine(b)
        exp=list(range(0,max(s)+1)) if s else []
        if s!=exp:
            sbad+=1
    print(f"NF P0-term spine == [0..maxspine] (inv2): mismatches {sbad}/{len(nfargs)}")

    # residual 1: fire propagation among NF P0 args
    pairs=[(bx,by) for (bx,_) in nfargs for (by,_) in nfargs]
    fp_bad=[]
    fp_tot=0
    for bx,by in pairs:
        if olt(bx,by) and pfire(0,bx):
            fp_tot+=1
            if not pfire(0,by): fp_bad.append((bx,by))
    print(f"fireprop: tot {fp_tot} viol {len(fp_bad)}")
    for v in fp_bad[:8]: print("  FP VIOL",v)

    # residual 2: bothfire comparison
    bf_bad=[]; bf_tot=0
    for bx,by in pairs:
        if olt(bx,by) and pfire(0,bx) and pfire(0,by):
            bf_tot+=1
            if not olt(proj(0,bx),proj(0,by)): bf_bad.append((bx,by,proj(0,bx),proj(0,by)))
    print(f"bothfire: tot {bf_tot} viol {len(bf_bad)}")
    for v in bf_bad[:8]: print("  BF VIOL",v)

    # structural key: proj 0 (P 1 b' c') = proj 0 b'   over all subterms appearing
    allsub=set()
    def collect(t):
        if t==Z: return
        a,b,c=t
        allsub.add(t); collect(b); collect(c)
    for t in NF: collect(t)
    sk_bad=[]; sk_tot=0
    for t in allsub:
        a,b,c=t
        if a==1:
            sk_tot+=1
            if proj(0,t)!=proj(0,b): sk_bad.append((t,proj(0,t),proj(0,b)))
    print(f"structural proj0(P1 b' c')=proj0 b': tot {sk_tot} viol {len(sk_bad)}")
    for v in sk_bad[:8]: print("  SK VIOL",v)

if __name__=="__main__": main()
