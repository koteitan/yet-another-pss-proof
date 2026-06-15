#!/usr/bin/env python3
"""Pin down the correct ins value-identity.  ins a b (P e f g):
  if a<e or (a=e and olt b f):  returns P e f g  (ABSORB)
  else:                          returns P a b (P e f g)  (PREPEND)
Conjecture H2A (the real invariant, only needs nrm/wf3 context):
  When b is the proj-normalized arg and c=nrm c' is in OT/cnf, the ABSORB branch
  fires EXACTLY when psi(oV b) a + oV c = oV c (ordinal left-absorption), and the
  PREPEND branch gives oV = psi(oV b) a + oV c.  So in BOTH branches
      oV(ins a b c) = psi(oV b) a (+) oV c
  PROVIDED the principal psi(oV b) a is compared correctly.  H2 failed because we
  fed arbitrary b,c.  Re-test restricted to the nrm-context: b=proj a (nrm b0),
  c=nrm c0, with the WHOLE thing a genuine principal-of-NF.  i.e. test on actual
  P a b0 c0 subterms of NF: oV(ins a (proj a (nrm b0)) (nrm c0)) =?= oV(nrm(P a b0 c0)) [trivially]
  and =?= psi(oV(proj a (nrm b0))) a (+) oV(nrm c0).
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
    feas=[]
    for t in allt:
        try: oV(t); feas.append(t)
        except ValueError: pass
    # KEY test: for every principal subterm P a b0 c0 of (feasible) NF,
    #   with bb = proj a (nrm b0), cc = nrm c0,
    #   does  oV(ins a bb cc) = psi(oV bb) a (+) oV cc ?
    # i.e. H2 RESTRICTED to nrm-context principals.
    tot=0; viol=0; ex=[]
    absorb=0; prepend=0
    for t in feas:
        # iterate principals of t
        stack=[t]
        seen=set()
        while stack:
            s=stack.pop()
            if s==Z or s in seen: continue
            seen.add(s)
            a,b0,c0=s
            stack.append(b0); stack.append(c0)
            bb=proj(a,nrm3(b0)); cc=nrm3(c0)
            try:
                lhs=oV(ins(a,bb,cc))
                p=crc.psi(oV(bb),a)
                if p is None: continue
                rhs=crc.oadd(p,oV(cc))
                tot+=1
                # branch
                if cc!=Z and (a<cc[0] or (a==cc[0] and olt(bb,cc[1]))):
                    absorb+=1
                else: prepend+=1
                if lhs!=rhs:
                    viol+=1
                    if len(ex)<8: ex.append((a,bb,cc,lhs,rhs))
            except ValueError: pass
    print(f"H2-restricted-to-nrm-context: tested={tot} (absorb={absorb}, prepend={prepend}) VIOL={viol}")
    for a,bb,cc,l,r in ex:
        print(f"   VIOL a={a} bb={fmt(bb)} cc={fmt(cc)} lhs={crc.to_str(l)} rhs={crc.to_str(r)}")

    # Also: in the ABSORB branch, is psi(oV bb) a (+) oV cc == oV cc ? (left-absorption)
    tot2=0; viol2=0; ex2=[]
    for t in feas:
        stack=[t]; seen=set()
        while stack:
            s=stack.pop()
            if s==Z or s in seen: continue
            seen.add(s)
            a,b0,c0=s; stack.append(b0); stack.append(c0)
            bb=proj(a,nrm3(b0)); cc=nrm3(c0)
            if cc==Z: continue
            if not (a<cc[0] or (a==cc[0] and olt(bb,cc[1]))): continue  # only absorb branch
            try:
                p=crc.psi(oV(bb),a)
                if p is None: continue
                tot2+=1
                if crc.oadd(p,oV(cc))!=oV(cc):
                    viol2+=1
                    if len(ex2)<8: ex2.append((a,bb,cc,p))
            except ValueError: pass
    print(f"ABSORB-branch left-absorption psi(oV bb)a + oV cc = oV cc: tested={tot2} VIOL={viol2}")
    for a,bb,cc,p in ex2:
        print(f"   ABSVIOL a={a} psi={crc.to_str(p)} oVcc={crc.to_str(oV(cc))}")

if __name__=="__main__":
    main()
