import sys; sys.path.insert(0,'.'); sys.setrecursionlimit(100000)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm
from fast_pss import oper

# untranslate: three (conv form: tuple of ('D',a,b)) -> pairseq, at depth d
def untranslate(t, d):
    out=[]
    for p in t:
        _,a,b=p
        out.append((d,a))
        out += untranslate(b, d+1)
    return out
# but conv produces nested; translate's three is (y, b, c) tuples. conv gives ('D',a,b) list.
# untranslate from conv-list form:
def untr(t,d):  # t = tuple of ('D',a,b)
    out=[]
    for (_,a,b) in t:
        out.append((d,a)); out+=untr(b,d+1)
    return out

def sigma(M):
    return untr(nrm(conv(translate(list(M)))), 0)

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
def maxr1(M): return max((p[1] for p in M),default=0)
def fmt(M): return ''.join('(%d,%d)'%(a,b) for a,b in M)

# show sigma on some maxr1>=2 examples (where nrm acts nontrivially)
shown=0
print("=== M  -->  sigma(M)  (maxr1>=2 examples) ===")
for M in ST:
    if maxr1(M)<2: continue
    sM=sigma(M)
    if sM!=M:
        print(f"M    ={fmt(M)}")
        print(f"sig  ={fmt(sM)}")
        print()
        shown+=1
        if shown>=12: break
# stats: how often sigma changes only by truncation/suffix?
chg=0; tot=0; prefix_of=0; suffix_drop=0
for M in ST:
    sM=sigma(M); tot+=1
    if sM!=M:
        chg+=1
