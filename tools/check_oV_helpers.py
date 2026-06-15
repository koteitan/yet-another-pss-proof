#!/usr/bin/env python3
"""Verify the two helper facts for oV_nrm in the GENUINE finite ordinal collapse
model (cset_remark_check.py), deeply:

  H1 (proj preserves oV):   oV (proj a b) = oV b
  H2 (ins is principal-add): oV (ins a b c) = psi(oV b) a (+) oV c
  H0 (composite):            oV (nrm t) = oV t

proj/ins/nrm are the three-level defs from nrm.thy.  oV(P a b c)=psi(oV b) a (+) oV c.
Subscripts limited to {0,1,2} (model range); we test all model-feasible NF subterms.
"""
import sys, importlib.util; sys.setrecursionlimit(1000000); sys.path.insert(0,'.')
spec=importlib.util.spec_from_file_location("crc","cset_remark_check.py")
crc=importlib.util.module_from_spec(spec); spec.loader.exec_module(crc)
from wfe_explore import translate, enum_ST, olt, fmt

Z=()
def Gterm(u,t):
    if t==Z: return []
    a,b,c=t; r=[]
    if u<=a: r.append(b); r+=Gterm(u,b)
    r+=Gterm(u,c); return r
def proj(u,b):
    while True:
        bad=[g for g in Gterm(u,b) if not olt(g,b)]
        if not bad: break
        g=bad[0]
        for h in bad[1:]:
            if olt(g,h): g=h
        b=g
    return b
def ins(a,b,t):
    if t==Z: return (a,b,Z)
    e,f,g=t
    if a<e or (a==e and olt(b,f)): return t
    return (a,b,t)
def nrm3(t):
    if t==Z: return Z
    a,b,c=t
    return ins(a, proj(a, nrm3(b)), nrm3(c))

def oV(t):
    if t==Z: return crc.ZERO
    a,b,c=t
    p=crc.psi(oV(b),a)
    if p is None: raise ValueError
    return crc.oadd(p, oV(c))

def maxsub_all(t):
    if t==Z: return 0
    a,b,c=t; return max(a,maxsub_all(b),maxsub_all(c))

def main():
    ST=enum_ST(seed_max_v=3,oper_ns=(1,2,3,4),max_len=14,rounds=7)
    NF=[t for t in set(translate(M) for M in ST) if maxsub_all(t)<=2]
    allt=set()
    def subs(t):
        allt.add(t)
        if t!=Z:
            a,b,c=t; subs(b); subs(c)
    for t in NF: subs(t)
    # also include all proj/ins intermediate forms
    feas=[]
    for t in allt:
        try: oV(t); feas.append(t)
        except ValueError: pass
    print(f"#NF(subs<=2)={len(NF)}  #subterms={len(allt)}  #oV-feasible={len(feas)}")

    # H1: oV(proj a b)=oV b  for a in {0,1,2}, b ranging over feasible subterms
    h1=0; h1t=0; ex1=[]
    for b in feas:
        for a in (0,1,2):
            pb=proj(a,b)
            try:
                if oV(pb)!=oV(b):
                    h1+=1
                    if len(ex1)<8: ex1.append((a,b,pb))
                h1t+=1
            except ValueError: pass
    print(f"H1 oV(proj a b)=oV b : tested={h1t}  VIOL={h1}")
    for a,b,pb in ex1:
        print(f"   H1VIOL a={a} b={fmt(b)} proj={fmt(pb)} oVb={crc.to_str(oV(b))} oVproj={crc.to_str(oV(pb))}")

    # H2: oV(ins a b c)=psi(oV b) a (+) oV c   for feasible b,c and a
    h2=0; h2t=0; ex2=[]
    bs=feas if len(feas)<400 else feas[:400]
    for b in bs:
        for c in bs:
            for a in (0,1,2):
                try:
                    lhs=oV(ins(a,b,c))
                    p=crc.psi(oV(b),a)
                    if p is None: continue
                    rhs=crc.oadd(p, oV(c))
                    h2t+=1
                    if lhs!=rhs:
                        h2+=1
                        if len(ex2)<8: ex2.append((a,b,c,lhs,rhs))
                except ValueError: pass
    print(f"H2 oV(ins a b c)=psi(oV b)a + oV c : tested={h2t}  VIOL={h2}")
    for a,b,c,l,r in ex2:
        print(f"   H2VIOL a={a} b={fmt(b)} c={fmt(c)} lhs={crc.to_str(l)} rhs={crc.to_str(r)}")

    # H0: composite
    h0=0; h0t=0
    for t in feas:
        try:
            if oV(nrm3(t))!=oV(t): h0+=1
            h0t+=1
        except ValueError: pass
    print(f"H0 oV(nrm t)=oV t : tested={h0t}  VIOL={h0}")

if __name__=="__main__":
    main()
