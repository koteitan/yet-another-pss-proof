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
# r1ok(parent_sub, t): every principal D_a(b) in t has a <= parent_sub+1, recursively
# top-level: parent_sub from context. We'll define r1ok with an explicit cap = allowed max subscript.
def r1ok(t, cap):
    for p in t:
        _,a,b=p
        if a>cap: return False
        if not r1ok(b, a+1): return False    # inside arg, cap = a+1
    return True
# generate r1ok terms via random with cap discipline
def gen(cap,d,rng):
    if d<=0 or rng.random()<0.4: return ()
    k=rng.randint(1,3); out=[]
    for _ in range(k):
        a=rng.randint(0,cap)
        b=gen(a+1,d-1,rng)
        out.append(('D',a,b))
    return tuple(out)
rng=random.Random(21)
R=set()
while len(R)<5000:
    t=gen(3,4,rng)
    if r1ok(t,3): R.add(t)
R=list(R)
print("r1ok terms:",len(R))
# proj-monotone+strict on r1ok: for valid subscript a (<= cap), olt x y => olt(proj a x)(proj a y)?
# Use a from 0..3. Both x,y must be r1ok under cap>=a so that proj a is "in-context".
sample=rng.sample(R,min(700,len(R)))
tot=0; rev=0; ns=0; exR=[]
for a in range(4):
    for x in sample:
        if not r1ok(x,a): continue        # x must be r1ok with cap a (subscript a context)
        for y in sample:
            if x is y: continue
            if not r1ok(y,a): continue
            if lt_term(x,y):
                tot+=1
                px=proj(a,x); py=proj(a,y)
                if lt_term(py,px): rev+=1; (exR.append((a,x,y,px,py)) if len(exR)<5 else None)
                elif not lt_term(px,py): ns+=1
print(f"proj on r1ok (in-context cap=a): tested={tot} REVERSAL={rev} NONSTRICT={ns}")
for a,x,y,px,py in exR[:5]: print("  REV a=",a,"x=",x,"->",px,"  y=",y,"->",py)
