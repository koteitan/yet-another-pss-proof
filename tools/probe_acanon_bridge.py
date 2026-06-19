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
def harg(x): return () if x==() else x[0][2]
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
def takeW(r):
    out=[]
    for p in r:
        if p[0]>0: out.append(p)
        else: break
    return out
def NT(S): return nrm(conv(translate(list(S))))
base=enum_ST(seed_max_v=5,oper_ns=(1,2,3,4),max_len=14,rounds=6)
forms=list(set(base))
chk=0
# TWO sub-claims to verify constitute the reduction:
#  (A) proj a hb = hb   where a=lead X        [a-canonicity, from nrm]
#  (B) for every g in Glist 0 hb: lead g >= a  OR  olt g hb
#     i.e. every G_0-critical with lead < a is <o hb (non-tied-below)
# If (A)&(B) then proj0 hb=hb because: 0-criticals split into those with lead>=a (= a-criticals, killed by A)
#   and those with lead<a (killed by B as non-violators).
failA=0; failB=0; both_ok=0; target_fail=0
for M in forms:
    M=list(M)
    if not M or M[0][0]!=0: continue
    W=takeW(M[1:])
    if not W: continue
    X=NT(tuple(W))
    if X==() or not fires(0,X): continue
    a=X[0][1]; hb=harg(X)
    chk+=1
    okA = (proj(a,hb)==hb)
    okB = all(leadof(g)>=a or lt_term(g,hb) for g in Glist(0,hb))
    if not okA: failA+=1
    if not okB: failB+=1
    if proj(0,hb)!=hb: target_fail+=1
    # confirm: G_a criticals of hb = G_0 criticals of hb with lead>=a
print(f"firing X checked={chk}")
print(f"  (A) proj a hb != hb fails = {failA}")
print(f"  (B) some 0-crit lead<a NOT <o hb fails = {failB}")
print(f"  target proj0 hb != hb = {target_fail}")
