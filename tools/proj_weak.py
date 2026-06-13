import sys; sys.path.insert(0,'.'); sys.setrecursionlimit(100000)
from valnorm import nrm, lt_term, le_term, G, in_OT
import random
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
# generate arbitrary three-terms (conv form) then nrm -> wf3
def randprinc(d,rng):
    a=rng.randint(0,3); b=randterm(d-1,rng); return ('D',a,b)
def randterm(d,rng):
    if d<=0 or rng.random()<0.35: return ()
    k=rng.randint(1,3)
    return tuple(randprinc(d,rng) for _ in range(k))
rng=random.Random(11)
W=set()
while len(W)<6000:
    t=nrm(randterm(4,rng))      # wf3 by construction
    if in_OT(t): W.add(t)
W=list(W)
print("wf3 terms:",len(W))
# P-ole on ALL wf3 pairs (sample), all subscripts a in 0..4
tot=0; reversal=0; nonstrict=0; exR=[]
sample=rng.sample(W,min(900,len(W)))
for a in range(5):
    for x in sample:
        for y in sample:
            if x is y: continue
            if lt_term(x,y):
                px=proj(a,x); py=proj(a,y)
                tot+=1
                if lt_term(py,px):
                    reversal+=1
                    if len(exR)<6: exR.append((a,x,y,px,py))
                elif not lt_term(px,py):
                    nonstrict+=1
print(f"P-ole on arbitrary wf3: tested={tot}")
print(f"  REVERSALS (proj breaks order on wf3!): {reversal}")
print(f"  non-strict collapses: {nonstrict}")
for a,x,y,px,py in exR[:6]:
    print("  REV a=",a,"x=",x,"y=",y,"-> px=",px,"py=",py)
