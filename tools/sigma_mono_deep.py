import sys; sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term
from fast_pss import oper

def untr(t,d):
    out=[]
    for (_,a,b) in t:
        out.append((d,a)); out+=untr(b,d+1)
    return out
def sigma(M): return untr(nrm(conv(translate(list(M)))), 0)

def pairlt(p,q): return p[0]<q[0] or (p[0]==q[0] and p[1]<q[1])
def seqlex(M,N):
    # iterative to avoid recursion depth
    i=0; lm=len(M); ln=len(N)
    while i<lm and i<ln:
        if M[i]!=N[i]: return pairlt(M[i],N[i])
        i+=1
    return lm<ln
def blockok(d,B):
    if not B: return True
    if B[0][0]!=d: return False
    if any(p[0]<d for p in B): return False
    for j in range(len(B)-1):
        if B[j+1][0] > B[j][0]+1: return False
    return True

# DEEP closure: more seeds, more ns, longer, more rounds, then +extra oper rounds
ST = enum_ST(seed_max_v=5, oper_ns=(1,2,3,4,5), max_len=16, rounds=8)
extra=set(tuple(M) for M in ST); cur=list(extra)
for r in range(5):  # +5 deeper closure rounds
    new=[]
    for M in cur:
        if len(M)<2: continue
        for n in (1,2,3,4,5):
            tt=tuple(oper(list(M),n))
            if tt not in extra:
                extra.add(tt); new.append(tt)
    cur=new
    if not cur: break
ST=[list(M) for M in extra]
print(f"closure size = {len(ST)}")

import random; rng=random.Random(7)

# round-trip + blockok preservation on a big sample
rt_bad=0; blk_bad=0; checked=0
for M in (ST if len(ST)<20000 else rng.sample(ST,20000)):
    sM=sigma(M); checked+=1
    if conv(translate(sM))!=nrm(conv(translate(M))): rt_bad+=1
    if not blockok(0,sM): blk_bad+=1
print(f"checked={checked} roundtrip-bad={rt_bad} blockok(sigma M)-bad={blk_bad}")

# seqlex-monotonicity over a large random sample of ordered pairs
samp = ST if len(ST)<1400 else rng.sample(ST,1400)
sig = {tuple(M): sigma(M) for M in samp}
tot=0; viol=0; eq=0; ex=[]
for M in samp:
    sM=sig[tuple(M)]
    for N in samp:
        if M is N: continue
        if seqlex(M,N):
            tot+=1
            sN=sig[tuple(N)]
            if sM==sN:
                eq+=1
            elif not seqlex(sM,sN):
                viol+=1
                if len(ex)<8: ex.append((M,N,sM,sN))
print(f"seqlex-monotone: tot={tot} viol={viol} collapse-eq={eq}")
def fmt(M): return ''.join('(%d,%d)'%(a,b) for a,b in M)
for (M,N,sM,sN) in ex:
    print("VIOL M=",fmt(M)," N=",fmt(N)," sM=",fmt(sM)," sN=",fmt(sN))
