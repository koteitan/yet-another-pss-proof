import sys, random; sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from valnorm import lt_term, fmtb
Z=()
def Glist(u,x):
    if x==(): return []
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    head=([b]+Glist(u,b)) if u<=a else []
    return head+Glist(u,c)
def Gterm(u,x): return Glist(u,x)
def leadof(x): return 0 if x==() else x[0][1]
def maxo(x,ys):
    m=x
    for y in ys:
        if lt_term(m,y): m=y
    return m
def proj(u,x):
    while True:
        gs=[g for g in Glist(u,x) if not lt_term(g,x)]
        if not gs: return x
        x=maxo(gs[0],gs[1:])
# Random three-terms (arbitrary, not necessarily wf3) to stress the ABSTRACT implication:
#   proj a hb = hb  &  a < lead hb  =>  every g in Glist 0 hb is <o hb
def randterm(d):
    if d<=0 or random.random()<0.35: return Z
    sub=random.randint(0,4)
    b=randterm(d-1)
    c=randterm(d-1)
    return ((0,sub,b),)+c
random.seed(1)
tot=0; applic=0; fail=0; samples=[]
for _ in range(200000):
    hb=randterm(4)
    if hb==(): continue
    L=leadof(hb)
    for a in range(0,L):  # a < lead hb
        if proj(a,hb)==hb:  # a-canonical
            applic+=1
            bad=[g for g in Glist(0,hb) if not lt_term(g,hb)]
            if bad:
                fail+=1
                if len(samples)<6: samples.append((fmtb(hb)[:30],a,fmtb(bad[0])[:20]))
            break
    tot+=1
print(f"random terms={tot} applicable(a-canon & a<lead)={applic} FAIL={fail}")
for s in samples: print("   ",s)
