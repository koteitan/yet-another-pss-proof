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
def proj(u,b):
    while True:
        bad=[g for g in Gterm(u,b) if not olt(g,b)]
        if not bad: return b
        m=bad[0]
        for h in bad[1:]:
            if olt(m,h):m=h
        b=m
def maxsub_all(t):
    if t==Z: return 0
    return max(t[0], maxsub_all(t[1]), maxsub_all(t[2]))
def climb_(t):
    s=[];cur=t
    while cur!=Z: s.append(cur[0]); cur=cur[1]
    return max(s) if s else 0
out=open('/home/koteitan/proofs/lean-yapss/git/tools/descok_result.txt','w')
def w(s): out.write(s+"\n"); out.flush()

# CLEAN RECURSIVE descok (Lean-friendly):
#   descok Z = False  (or vacuous; firing args are nonZ)
#   descok (P a x y):
#     if a == maxsub(P a x y):   -- top node
#        True   (lead = maxsub)
#     else:    -- not top: must descend into x
#        lead x == a+1  AND  maxsub y < maxsub x  AND  descok x
# Equivalent to: consecutive-lead chain to maxsub, tails below.
def descok(t):
    if t==Z: return False
    a,x,y=t
    if a==maxsub_all(t):
        return True
    # not top
    return lead(x)==a+1 and maxsub_all(y)<maxsub_all(x) and descok(x)

ST=enum_ST(seed_max_v=4,oper_ns=(1,2,3,4),max_len=14,rounds=8)
NF=sorted({translate(list(M)) for M in ST},key=str)
args=sorted({t[1] for t in NF if t!=Z and t[0]==0},key=str)
fire=[b for b in args if pfire(0,b)]
fok=sum(1 for b in fire if descok(b))
w(f"recursive descok: firing NF args satisfy: {fok}/{len(fire)}")

# collect descok nodes
nodes=set()
for b in fire:
    cur=b
    while cur!=Z:
        if descok(cur): nodes.add(cur)
        if lead(cur)==maxsub_all(cur): break
        cur=cur[1]
nodes=list(nodes)
w(f"descok nodes: {len(nodes)}")

# MAIN: olt(proj0 x)(proj0 y) for descok same-lead eqmaxsub olt pairs
ok=tot=0;bad=[]
for x in nodes:
    px=proj(0,x)
    for y in nodes:
        if not olt(x,y) or maxsub_all(x)!=maxsub_all(y) or lead(x)!=lead(y): continue
        tot+=1
        if olt(px,proj(0,y)): ok+=1
        elif len(bad)<4: bad.append((x,y))
w(f"MAIN olt(proj0 x)(proj0 y) on descok same-lead eqmaxsub olt: {ok}/{tot}")
for b_ in bad: w("  BAD "+str(b_))

# STEP: descok(P a x y) & not top => descok x (recursive def gives directly)
# BASE: descok t & lead t = maxsub t (top) => not pfire 0 t
bt=bok=0;bbad=[]
for t in nodes:
    if lead(t)==maxsub_all(t):
        bt+=1
        if not pfire(0,t): bok+=1
        elif len(bbad)<4: bbad.append(t)
w(f"BASE: descok top node (lead=maxsub) => not pfire: {bok}/{bt}")
for b_ in bbad: w("  BBAD "+str(b_))
out.close()
