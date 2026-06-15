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
# chain from t descending .b UNTIL lead == maxsub_all(t). leads must be consecutive
# [lead t, lead t+1, ..., maxsub], AND tails strictly below at each step.
def descok(t):
    if t==Z: return False
    k=maxsub_all(t); cur=t; expect=lead(t)
    while True:
        if cur==Z: return False
        L,x,y=cur
        if L!=expect: return False
        if L==k:  # reached top
            return True
        # not top: need to descend, head arg must have lead L+1, tail below
        if maxsub_all(y) >= maxsub_all(x): return False
        cur=x; expect=L+1
out=open('/home/koteitan/proofs/lean-yapss/git/tools/rec_result.txt','w')
def w(s): out.write(s+"\n"); out.flush()
ST=enum_ST(seed_max_v=4,oper_ns=(1,2,3,4),max_len=14,rounds=8)
NF=sorted({translate(list(M)) for M in ST},key=str)
args=sorted({t[1] for t in NF if t!=Z and t[0]==0},key=str)
fire=[b for b in args if pfire(0,b)]
fok=sum(1 for b in fire if descok(b))
w(f"firing NF args satisfy descok(chain-to-maxsub consec): {fok}/{len(fire)}")
nodes=set()
for b in fire:
    cur=b
    while cur!=Z:
        if descok(cur): nodes.add(cur)
        if lead(cur)==maxsub_all(cur): break
        cur=cur[1]
nodes=list(nodes)
w(f"descok nodes: {len(nodes)}")
ok=tot=0;bad=[]
for x in nodes:
    px=proj(0,x)
    for y in nodes:
        if not olt(x,y) or maxsub_all(x)!=maxsub_all(y) or lead(x)!=lead(y): continue
        tot+=1
        if olt(px,proj(0,y)): ok+=1
        elif len(bad)<4: bad.append((x,y))
w(f"DESCOK(chain-to-maxsub) same-lead eqmaxsub olt: olt(proj0 x)(proj0 y): {ok}/{tot}")
for b_ in bad: w("  BAD "+str(b_))
out.close()
