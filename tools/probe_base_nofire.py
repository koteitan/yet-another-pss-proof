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
def maxsub_all(t):
    if t==Z: return 0
    return max(t[0], maxsub_all(t[1]), maxsub_all(t[2]))
def gen(depth,ms):
    if depth==0: yield Z; return
    yield Z
    for a in range(ms+1):
        for b in gen(depth-1,ms):
            for c in gen(depth-1,ms):
                yield (a,b,c)
out=open('/home/koteitan/proofs/lean-yapss/git/tools/rec_result.txt','w')
def w(s): out.write(s+"\n"); out.flush()
# GENERAL: lead t = maxsub t  =>  ¬ pfire 0 t ?  (a critical can't exceed when
# lead already = max subscript). Test on all terms.
terms=list(gen(3,4))
ok=tot=0;bad=[]
for t in terms:
    if t==Z: continue
    if lead(t)!=maxsub_all(t): continue
    tot+=1
    if not pfire(0,t): ok+=1
    elif len(bad)<6: bad.append((t,lead(t),maxsub_all(t)))
w(f"GENERAL: lead t = maxsub t => not pfire 0 t: {ok}/{tot}")
for b_ in bad: w("  BAD "+str(b_))
out.close()
