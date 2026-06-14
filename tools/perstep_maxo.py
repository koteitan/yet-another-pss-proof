import sys; sys.path.insert(0,'.'); sys.setrecursionlimit(100000)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term, G
from fast_pss import oper
def maxo(x, ys):
    for y in ys:
        if lt_term(x,y): x=y
    return x
def val_principal(a,b): return nrm(((('D',a,b)),))
def principals(t):
    for p in t:
        _,a,b=p; yield (a,b); yield from principals(b)
ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=13, rounds=6)
extra=set(tuple(M) for M in ST); cur=list(extra)
for _ in range(2):
    new=[]
    for M in cur:
        if len(M)<2: continue
        for n in (1,2,3,4):
            tt=tuple(oper(list(M),n))
            if tt not in extra: extra.add(tt); new.append(tt)
    cur=new
terms=set(conv(translate(list(M))) for M in extra)
seen=set(); tot=0; bad=0; ex=[]; steps=0
for c in terms:
    for (a,b0) in principals(c):
        if (a,b0) in seen: continue
        seen.add((a,b0))
        b=nrm(b0)
        # iterate proj one maxo-step at a time, checking each step preserves psi value
        while True:
            badset=[g for g in G(a,b) if not lt_term(g,b)]
            if not badset: break
            m=maxo(badset[0], badset[1:])
            steps+=1
            tot+=1
            # A1: psi_a(oV b) == psi_a(oV m)  (single maxo step)
            if val_principal(a,b) != val_principal(a,m):
                bad+=1
                if len(ex)<8: ex.append((a,b,m))
            b=m
print(f"A1 single maxo-step: tested steps={tot}")
print(f"  ★ psi_a(oV b) != psi_a(oV m) FAILS: {bad}")
for a,b,m in ex[:8]: print("   FAIL a=",a)
