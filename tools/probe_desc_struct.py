import sys; sys.path.insert(0,'.')
from wfe_explore import enum_ST, translate, olt, maxsub
Z=()
def lead(t): return 0 if t==Z else t[0]
def Gterm(u,t):
    if t==Z: return []
    a,b,c=t;o=[]
    if u<=a:o.append(b);o+=Gterm(u,b)
    o+=Gterm(u,c);return o
def pfire(u,b): return any(not olt(g,b) for g in Gterm(u,b))
def maxr1(M): return max(p[1] for p in M) if M else 0
def takeWhile(p,l):
    o=[]
    for x in l:
        if p(x): o.append(x)
        else: break
    return o
def dropWhile(p,l):
    i=0
    while i<len(l) and p(l[i]): i+=1
    return l[i:]
out=open('/home/koteitan/proofs/lean-yapss/git/tools/ds_result.txt','w')
def w(s): out.write(s+"\n"); out.flush()
ST=[list(M) for M in enum_ST(seed_max_v=4,oper_ns=(1,2,3,4),max_len=14,rounds=8)]
def nodes(M):
    res=[]
    def rec(L):
        if not L: return
        p=L[0]; rest=L[1:]
        d=takeWhile(lambda q:p[0]<q[0],rest); s=dropWhile(lambda q:p[0]<q[0],rest)
        res.append((p,d))
        rec(d); rec(s)
    rec(list(M)); return res
# desc of a row-1=0 root: structure. translate desc fires iff? Let me find the
# MINIMAL fact. desc head row-1? desc could itself fire (firing NF args exist).
# (★) says it DOESN'T fire when the ROOT is row-1=0. So the root being row-1=0
# constrains desc. KEY: desc's columns row-1 <= root row-1 + climbing? root row-1=0,
# so desc's row-1 <= 1 (climb by 1 from 0). And desc head row-0 = root.0+1.
# Hmm. Let me reconsider: maybe (★) reduces to: desc is the child block of a row-1=0
# parent => translate desc = a NON-FIRING form. via z0ok: desc columns with row-0
# ... actually let me just check: do desc blocks (of row-1=0 roots) have a clean
# property like maxr1(desc) such that translate doesn't fire?
seen=set()
firing_desc=[]
for M in ST:
    if maxr1(M)>1: continue
    for (p,d) in nodes(M):
        if p[1]!=0 or not d: continue
        key=tuple(d)
        if key in seen: continue
        seen.add(key)
        # does translate d fire? (★) says no.
        if pfire(0,translate(d)): firing_desc.append((p,d))
w(f"firing desc of row-1=0 roots: {len(firing_desc)} (should be 0)")
# So no desc fires. The structural reason: ALL desc of row-1=0 roots have translate
# non-firing. What distinguishes from a firing block? Let me compare with desc of
# row-1=1 roots (which CAN fire).
seen=set(); r1_fire=0; r1_tot=0
for M in ST:
    if maxr1(M)>1: continue
    for (p,d) in nodes(M):
        if p[1]!=1 or not d: continue
        key=tuple(d)
        if key in seen: continue
        seen.add(key)
        r1_tot+=1
        if pfire(0,translate(d)): r1_fire+=1
w(f"firing desc of row-1=1 roots: {r1_fire}/{r1_tot}")
# So the ROOT's row-1 (0 vs 1) controls whether desc fires! row-1=0 root => desc
# non-firing. This is exactly (★). The reason: desc's row-1 climbs from the root's
# row-1. root row-1=0 => desc row-1 bounded by 1, AND the structure is 'fresh'.
out.close()
