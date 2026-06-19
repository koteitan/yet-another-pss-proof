import sys, random; sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from valnorm import lt_term as olt, fmtb
Z=()
def Glist(u,x):
    if x==(): return []
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    head=([b]+Glist(u,b)) if u<=a else []
    return head+Glist(u,c)
def leadof(x): return 0 if x==() else x[0][1]
def maxo(x,ys):
    m=x
    for y in ys:
        if olt(m,y): m=y
    return m
def proj(u,x):
    while True:
        gs=[g for g in Glist(u,x) if not olt(g,x)]
        if not gs: return x
        x=maxo(gs[0],gs[1:])
def hdle(s,t):
    if s==(): return True
    if t==(): return False
    a=s[0][1]; b=s[0][2]; e=t[0][1]; f=t[0][2]
    return a<e or (a==e and (olt(b,f) or b==f))
def wf3(x):
    if x==(): return True
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    if not wf3(b) or not wf3(c): return False
    for g in Glist(a,b):
        if not olt(g,b): return False
    # OT2 head non-increasing on spine: hdle(c, P a b Z)
    if c!=():
        if not hdle(c,((0,a,b),)): return False
    return True
def randterm(d):
    if d<=0 or random.random()<0.35: return Z
    sub=random.randint(0,4)
    b=randterm(d-1)
    c=randterm(d-1)
    return ((0,sub,b),)+c
random.seed(7)
tot=0; applic=0; fail=0; samples=[]
for _ in range(400000):
    hb=randterm(4)
    if hb==() or not wf3(hb): continue
    L=leadof(hb)
    for a in range(0,L):
        if proj(a,hb)==hb:
            applic+=1
            bad=[g for g in Glist(0,hb) if not olt(g,hb)]
            if bad:
                fail+=1
                if len(samples)<8: samples.append((fmtb(hb)[:32],a,L,fmtb(bad[0])[:22]))
            break
    tot+=1
print(f"wf3 terms={tot} applicable(a-canon & a<lead)={applic} FAIL={fail}")
for s in samples: print("   hb=",s[0]," a=",s[1]," leadhb=",s[2]," bad=",s[3])
