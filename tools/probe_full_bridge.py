import sys; sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term, fmtb
Z=()
def Glist(u,x):
    if x==(): return []
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    head=([b]+Glist(u,b)) if u<=a else []
    return head+Glist(u,c)
def fires(u,x): return any(not lt_term(g,x) for g in Glist(u,x))
def leadof(x): return 0 if x==() else x[0][1]
def harg(x): return () if x==() else x[0][2]
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
def takeW(r):
    out=[]
    for p in r:
        if p[0]>0: out.append(p)
        else: break
    return out
def NT(S): return nrm(conv(translate(list(S))))
# FULL claim as a single GENERAL lemma (no ST induction):
#   Given X=P a hb hc, proj a hb = hb (head a-canon, a=lead X), and a < lead hb (lead gap),
#   then for EVERY g in Gterm 0 hb: olt g hb. Hence proj 0 hb = hb.
# Verify on firing arg-zone images (the use site) AND check the abstract implication holds.
base=enum_ST(seed_max_v=6,oper_ns=(1,2,3,4),max_len=16,rounds=7)
forms=list(set(base))
chk=0; imp_fail=0; hyp_fail=0
for M in forms:
    M=list(M)
    if not M or M[0][0]!=0: continue
    W=takeW(M[1:])
    if not W: continue
    X=NT(tuple(W))
    if X==() or not fires(0,X): continue
    a=X[0][1]; hb=harg(X)
    chk+=1
    # check hypotheses hold (sanity)
    H1 = (proj(a,hb)==hb)   # head a-canon
    H2 = (a < leadof(hb))   # lead gap
    if not (H1 and H2): hyp_fail+=1
    # the abstract implication: H1 & H2 => all g in Glist 0 hb are <o hb
    if H1 and H2:
        for g in Glist(0,hb):
            if not lt_term(g,hb):
                imp_fail+=1
                break
print(f"firing X checked={chk}")
print(f"  hypotheses (a-canon & lead gap) fail = {hyp_fail}")
print(f"  IMPLICATION (H1&H2 => 0-dominance) fail = {imp_fail}")
