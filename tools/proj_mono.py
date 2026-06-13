import sys; sys.path.insert(0,'.'); sys.setrecursionlimit(100000)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term, le_term, G
from fast_pss import oper

# proj from valnorm? nrm uses an internal projection loop. Replicate proj(a,x):
def proj(a,x):
    bb=x
    while True:
        bad=[g for g in G(a,bb) if not lt_term(g,bb)]
        if not bad: break
        g=bad[0]
        for h in bad[1:]:
            if lt_term(g,h): g=h
        bb=g
    return bb

# collect NF args: arguments b of principals D_a(b) hereditarily in translates (these are the sub-translates)
def args_with_sub(t):       # yield (a,b) principal-arg pairs hereditarily
    for p in t:
        _,a,b=p
        yield (a,b)
        yield from args_with_sub(b)

ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=13, rounds=6)
extra=set(tuple(M) for M in ST); cur=list(extra)
for _ in range(1):
    new=[]
    for M in cur:
        if len(M)<2: continue
        for n in (1,2,3,4):
            tt=tuple(oper(list(M),n))
            if tt not in extra: extra.add(tt); new.append(tt)
    cur=new
terms=set(conv(translate(list(M))) for M in extra)
# group args by subscript a
from collections import defaultdict
bysub=defaultdict(set)
for c in terms:
    for (a,b) in args_with_sub(c):
        bysub[a].add(b)
print("subscripts:",sorted(bysub)[:8],"... sizes:",{a:len(bysub[a]) for a in sorted(bysub)[:6]})

# TEST principal-arg monotonicity: for same a, olt b f => olt(proj a (nrm b))(proj a (nrm f))
import itertools, random
rng=random.Random(5)
tot=0; nonstrict=0; reversal=0; exNS=[]; exR=[]
for a, S in bysub.items():
    S=list(S)
    if len(S)>400: S=rng.sample(S,400)
    for b in S:
        for f in S:
            if b is f: continue
            if lt_term(b,f):     # olt b f
                tot+=1
                pb=proj(a,nrm(b)); pf=proj(a,nrm(f))
                if lt_term(pf,pb):       # strict reversal!
                    reversal+=1
                    if len(exR)<5: exR.append((a,b,f))
                elif not lt_term(pb,pf): # equal (collapse, non-strict)
                    nonstrict+=1
                    if len(exNS)<5: exNS.append((a,b,f))
print(f"principal-arg pairs (olt b f, same a): {tot}")
print(f"  REVERSALS (olt(proj f)(proj b)): {reversal}")
print(f"  NON-STRICT (proj a nrm b == proj a nrm f): {nonstrict}")
for a,b,f in exNS[:5]: print("   NONSTRICT a=",a,"b=",b,"f=",f)
