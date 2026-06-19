import sys, random, itertools; sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
random.seed(7)
from valnorm import nrm, lt_term, fmtb, conv
from wfe_explore import translate
Z=()
def Glist(u,x):
    if x==(): return []
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    head=([b]+Glist(u,b)) if u<=a else []
    return head+Glist(u,c)
def fires(u,x): return any(not lt_term(g,x) for g in Glist(u,x))
def proj0(x):
    bb=x
    while True:
        V=[g for g in Glist(0,bb) if not lt_term(g,bb)]
        if not V: break
        m=V[0]
        for g in V[1:]:
            if lt_term(m,g): m=g
        bb=m
    return bb
def harg(x): return () if x==() else x[0][2]
def leadof(x): return 0 if x==() else x[0][1]

# (A) random SEQUENCES (non-standard): random pair lists, translate, nrm, check harg 0-canon on firing
print("=== (A) random non-standard sequences: harg(nrm(translate seq)) 0-canonical? ===")
tot=0; canon_fail=0; lead_dist={}; ex=[]
for _ in range(200000):
    L=random.randint(1,7)
    # random arg-zone-like: positive row0, arbitrary row1
    seq=[(random.randint(1,5), random.randint(0,4)) for _ in range(L)]
    X=nrm(conv(translate(seq)))
    if X==() or not fires(0,X): continue
    tot+=1
    hb=harg(X); lead_dist[leadof(X)]=lead_dist.get(leadof(X),0)+1
    if proj0(hb)!=hb:
        canon_fail+=1
        if len(ex)<8: ex.append((fmtb(X)[:48],fmtb(hb)[:48]))
print(f"firing={tot}  harg NOT 0-canonical = {canon_fail}")
print(f"leadX dist = {dict(sorted(lead_dist.items()))}")
for e in ex: print("   NONcanon:",e)

# (B) random WF3 TERMS directly (not via nrm): does harg fire & is it 0-canonical?
print("\n=== (B) random trees directly (not nrm-images): harg 0-canonical on firing? ===")
def randtree(depth):
    if depth<=0 or random.random()<0.3: return Z
    n=random.randint(1,3); ps=[]
    for _ in range(n):
        a=random.randint(0,4); ps.append((0,a,randtree(depth-1)))
    return tuple(ps)
tot2=0; cf2=0; ex2=[]
for _ in range(200000):
    X=randtree(4)
    if X==() or not fires(0,X): continue
    tot2+=1
    hb=harg(X)
    if proj0(hb)!=hb:
        cf2+=1
        if len(ex2)<8: ex2.append((fmtb(X)[:48],fmtb(hb)[:48]))
print(f"firing={tot2}  harg NOT 0-canonical = {cf2}")
for e in ex2: print("   NONcanon:",e)
