import sys; sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term, fmtb
from fast_pss import oper
def Glist(u,x):
    if x==(): return []
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    head=([b]+Glist(u,b)) if u<=a else []
    return head+Glist(u,c)
def maxo(x,ys):
    m=x
    for y in ys:
        if lt_term(m,y): m=y
    return m
def proj(a,x):
    bb=x
    while True:
        gs=[g for g in Glist(a,bb) if not lt_term(g,bb)]
        if not gs: break
        bb=maxo(gs[0],gs[1:])
    return bb
def takeW(r):
    out=[]
    for p in r:
        if p[0]>0: out.append(p)
        else: break
    return out
def NT(S): return nrm(conv(translate(list(S))))
def harg(x): return () if x==() else x[0][2]
base=enum_ST(seed_max_v=5,oper_ns=(1,2,3,4,5),max_len=16,rounds=8)
extra=set(base); cur=list(extra)
for _ in range(5):
    new=[]
    for M in cur:
        M=list(M)
        if len(M)<2: continue
        for n in (1,2,3,4,5):
            tt=tuple(oper(M,n))
            if len(tt)<=22 and tt not in extra: extra.add(tt); new.append(tt)
    cur=new
    if not cur: break
seen=set(); imgs=[]
for M in extra:
    M=list(M)
    if not M or M[0][0]!=0: continue
    aM=tuple(takeW(M[1:]))
    if not aM: continue
    B=NT(aM)
    if B in seen: continue
    seen.add(B); imgs.append(B)
nfire=0; bad_projharg=0; bad_maxviol=0; exs=[]
for X in imgs:
    viol=[g for g in Glist(0,X) if not lt_term(g,X)]
    if not viol: continue   # not firing
    nfire+=1
    p=proj(0,X); hb=harg(X)
    if p!=hb:
        bad_projharg+=1
        if len(exs)<6: exs.append((fmtb(X),fmtb(p),fmtb(hb)))
    mv=maxo(viol[0],viol[1:])
    if mv!=hb: bad_maxviol+=1
print(f'distinct images={len(imgs)} firing={nfire}')
print(f'proj 0 X != harg X   = {bad_projharg}   <-- if >0, harg identity FALSE on ya-pss class')
print(f'maxo(violators)!=harg = {bad_maxviol}')
for e in exs: print('  EX X=%s  proj0X=%s  hargX=%s'%e)
print('DONE')
