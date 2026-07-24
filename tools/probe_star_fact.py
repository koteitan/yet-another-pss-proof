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
def H0clause(t):
    if t==Z: return True
    a,b,c=t
    cond = all(olt(x,b) for x in Gterm(0,b)) if a==0 else True
    return cond and H0clause(b) and H0clause(c)
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
out=open('/home/koteitan/proofs/lean-yapss/git/tools/sf_result.txt','w')
def w(s): out.write(s+"\n"); out.flush()
ST=[list(M) for M in enum_ST(seed_max_v=4,oper_ns=(1,2,3,4),max_len=14,rounds=8)]
# (★): at a row-1=0 root p in M (M ST_PS, maxr1<=1), the descendant block
# desc=takeWhile(p.1<.1) of rest has translate desc with no exceeding critical.
# i.e. forall x in Gterm 0 (translate desc), olt x (translate desc) = ¬pfire(translate desc).
# Collect all such (p, desc) from maxr1<=1 ST_PS via the translate recursion.
def nodes(M):
    res=[]
    def rec(L):
        if not L: return
        p=L[0]; rest=L[1:]
        d=takeWhile(lambda q:p[0]<q[0],rest); s=dropWhile(lambda q:p[0]<q[0],rest)
        res.append((p,d))
        rec(d); rec(s)
    rec(list(M)); return res
star_ok=star_bad=0; bad=[]; seen=set()
for M in ST:
    if maxr1(M)>1: continue
    for (p,d) in nodes(M):
        if p[1]!=0: continue  # row-1=0 root only
        key=tuple(d)
        if key in seen: continue
        seen.add(key)
        td=translate(d)
        if not pfire(0,td): star_ok+=1
        else: star_bad+=1; (bad.append((p,d)) if len(bad)<5 else None)
w(f"(★) on maxr1<=1 ST_PS row-1=0 roots: ¬pfire(translate desc): {star_ok}/{star_ok+star_bad}")
for b_ in bad: w("  STARBAD "+str(b_))
# Now: does (★) reduce to H0clause(translate desc) + something? Actually if translate
# desc is NON-FIRING that's exactly what we want. Let me check what desc looks like:
# desc head has row-0 > p.0 (descendant). For row-1=0 root p with p.0=v, desc starts
# at row-0 = v+1. The desc block is the 'children' of p. 
out.close()
