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
def maxsub(x):
    if x==(): return 0
    return max(x[0][1], maxsub(x[0][2]), maxsub(tuple(x[1:])))
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
# Deeper: X=P a hb hc fires under proj 0.
#  - relation lead X (=a) vs lead hb
#  - the firing critical = harg X (the head) ?  i.e. proj 0 X = hb (already known argzone_proj_head)
#  - KEY structural: hb = proj a (nrm b') from nrm. Conjecture: lead hb > a always (so 0-criticals of hb at lead hb dominate)
base=enum_ST(seed_max_v=5,oper_ns=(1,2,3,4),max_len=14,rounds=6)
forms=list(set(base))
chk=0; lead_hb_le_a=0; samples=[]
# the real question: for hb itself, why is proj0 hb=hb?  Because hb has NO 0-critical >= itself.
# hb=proj a (nrm b'): a-stable. Its 0-criticals with lead in [0,a) are extra.
# Conjecture KEY: every 0-critical g of hb with lead g < a (i.e. < lead X) has olt g hb.  (these are the "extra" ones proj a ignores)
extra_bad=0
for M in forms:
    M=list(M)
    if not M or M[0][0]!=0: continue
    W=takeW(M[1:])
    if not W: continue
    X=NT(tuple(W))
    if X==() or not fires(0,X): continue
    a=X[0][1]; hb=harg(X)
    chk+=1
    lhb=leadof(hb)
    if lhb<=a: 
        lead_hb_le_a+=1
        if len(samples)<8: samples.append((fmtb(X)[:30],a,lhb))
    # extra 0-criticals (lead<a) that are NOT <o hb
    for g in Glist(0,hb):
        if leadof(g)<a and not lt_term(g,hb):
            extra_bad+=1
print(f"firing X checked={chk}")
print(f"  lead hb <= a (=lead X) count={lead_hb_le_a}")
print(f"  extra 0-criticals of hb (lead<a) NOT <o hb: {extra_bad}")
for s in samples: print("   ",s)
