import sys; sys.path.insert(0,'.')
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term, in_OT
from fast_pss import oper, Lng

# sanity: known identity V4 nrm(D0(D1(D2 0))) = D0(D2 0)
t = ('D',0,(('D',1,(('D',2,()),)),))
print("V4 nrm(D0 D1 D2 0) =", nrm((t,)), "(expect D0(D2()))")

ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=14, rounds=7)
extra=set(tuple(M) for M in ST)
cur=list(extra)
for _ in range(2):
    new=[]
    for M in cur:
        if len(M)<2: continue
        for n in (1,2,3,4):
            tt=tuple(oper(list(M),n))
            if tt not in extra: extra.add(tt); new.append(tt)
    cur=new
ST=[list(M) for M in extra]
print("forms:",len(ST))

def maxr1(M): return max((p[1] for p in M), default=0)

# test: oV(translate(M[n])) < oV(translate(M)) via nrm value order
tot={}; bad={}; ex={}
for M in ST:
    if Lng(M)<2: continue
    for n in (1,2,3):
        Mn=oper(list(M),n)
        if Mn==M: continue
        a=nrm(conv(translate(Mn))); b=nrm(conv(translate(M)))
        L=maxr1(M)
        tot[L]=tot.get(L,0)+1
        dec = lt_term(a,b)
        if not dec:
            bad[L]=bad.get(L,0)+1
            if L not in ex: ex[L]=(M,n,a,b)
print("maxr1 : tested steps / oV-NOT-decreasing")
for L in sorted(tot):
    print(f"  maxr1={L}: {tot[L]:6d} steps, {bad.get(L,0):6d} NON-decreasing")
for L in sorted(ex):
    M,n,a,b=ex[L]
    print(f"  ex maxr1={L} n={n}: {''.join('(%d,%d)'%(x,y) for x,y in M)}")
