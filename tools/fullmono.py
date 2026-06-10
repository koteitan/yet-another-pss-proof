import sys, itertools
sys.path.insert(0,'.')
from wfe_explore import translate, fmt, enum_ST
from valnorm import conv, nrm, lt_term, fmtb
from mine_proj import G, proj
ST=enum_ST(seed_max_v=4,oper_ns=(1,2,3,4),max_len=14,rounds=8)
NF={translate(M) for M in ST}
def sub3(t):
    if t==(): return
    a,b,c=t
    yield t; yield from sub3(b); yield from sub3(c)
blocks=set()
for w in NF:
    for s in sub3(w): blocks.add(s)
ncache={}
def N(w):
    if w not in ncache: ncache[w]=nrm(conv(w))
    return ncache[w]
A={}
for w in blocks:
    a,b,c=w
    A.setdefault(a,set()).add(N(b))
def lead(x): return x[0][1] if x else None
for a in sorted(A):
    leads={}
    for x in A[a]: leads[lead(x)]=leads.get(lead(x),0)+1
    print(f'a={a} |A|={len(A[a])} leads={sorted(leads.items(), key=lambda kv:(kv[0] is None, kv[0]))}',flush=True)
for a in sorted(A):
    xs=sorted(A[a],key=str)
    pcache={x:proj(a,x) for x in xs}
    viol=0; ex=[]
    for x,y in itertools.combinations(xs,2):
        if lt_term(x,y): lo,hi=x,y
        elif lt_term(y,x): lo,hi=y,x
        else: continue
        if not lt_term(pcache[lo],pcache[hi]):
            viol+=1
            if len(ex)<3: ex.append((lo,hi))
    print(f'FULL proj-mono a={a}: n={len(xs)} violations={viol}',flush=True)
    for lo,hi in ex:
        print('  lo',fmtb(lo)[:70]); print('  hi',fmtb(hi)[:70])
        print('  pl',fmtb(pcache[lo])[:70]); print('  ph',fmtb(pcache[hi])[:70])
