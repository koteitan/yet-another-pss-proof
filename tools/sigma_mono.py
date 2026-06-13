import sys; sys.path.insert(0,'.'); sys.setrecursionlimit(100000)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term
from fast_pss import oper

def untr(t,d):
    out=[]
    for (_,a,b) in t:
        out.append((d,a)); out+=untr(b,d+1)
    return out
def sigma(M): return untr(nrm(conv(translate(list(M)))), 0)

# seqlex on pairseq (column-lex): pairlt then recurse
def pairlt(p,q): return p[0]<q[0] or (p[0]==q[0] and p[1]<q[1])
def seqlex(M,N):
    if not M: return N!=[]
    if not N: return False
    p,q=M[0],N[0]
    if p!=q: return pairlt(p,q)
    return seqlex(M[1:],N[1:])
# blockok d
def blockok(d,B):
    if not B: return True
    if B[0][0]!=d: return False
    if any(p[0]<d for p in B): return False
    for j in range(len(B)-1):
        if B[j+1][0] > B[j][0]+1: return False
    return True

ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=12, rounds=6)
extra=set(tuple(M) for M in ST); cur=list(extra)
for _ in range(1):
    new=[]
    for M in cur:
        if len(M)<2: continue
        for n in (1,2,3,4):
            tt=tuple(oper(list(M),n))
            if tt not in extra: extra.add(tt); new.append(tt)
    cur=new
ST=[list(M) for M in extra]
# round-trip check + blockok preservation
import random; rng=random.Random(2)
rt_bad=0; blk_bad=0; checked=0
for M in ST[:4000]:
    sM=sigma(M); checked+=1
    if translate(sM)!=translate(M) and conv(translate(sM))!=nrm(conv(translate(M))):
        # sigma should satisfy translate(sM)=nrm(translate M)
        if conv(translate(sM))!=nrm(conv(translate(M))): rt_bad+=1
    if not blockok(0,sM): blk_bad+=1
print(f"checked={checked} roundtrip-bad={rt_bad} blockok(sigma M)-bad={blk_bad}")

# seqlex-monotonicity: seqlex M N => seqlex (sigma M)(sigma N), on standard pairs
samp = ST if len(ST)<800 else rng.sample(ST,800)
tot=0; viol=0; ex=[]
for M in samp:
    sM=sigma(M)
    for N in samp:
        if M is N: continue
        if seqlex(M,N):
            tot+=1
            sN=sigma(N)
            if not (seqlex(sM,sN) or sM==sN):  # allow equal (collapse) ? check strict separately
                viol+=1
                if len(ex)<5: ex.append((M,N))
print(f"seqlex-monotone (seqlex M N => seqlex sM sN or eq): tot={tot} viol={viol}")
# strict version (no collapse to equal)
tot2=0; eq=0
for M in samp:
    sM=sigma(M)
    for N in samp:
        if M is N: continue
        if seqlex(M,N):
            tot2+=1; sN=sigma(N)
            if sM==sN: eq+=1
print(f"strict: collapses to equal sM==sN: {eq}/{tot2}")
