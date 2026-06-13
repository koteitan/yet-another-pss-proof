import sys; sys.path.insert(0,'.')
from wfe_explore import translate, enum_ST, maxsub
from valnorm import conv, in_OT

ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=14, rounds=7)
ST = [list(M) for M in set(tuple(M) for M in ST)]
print("ST_PS forms:", len(ST))

# also push one more oper round for depth
from fast_pss import oper
extra=set(tuple(M) for M in ST)
cur=list(extra)
for _ in range(2):
    new=[]
    for M in cur:
        if len(M)<2: continue
        for n in (1,2,3,4):
            t=tuple(oper(list(M),n))
            if t not in extra: extra.add(t); new.append(t)
    cur=new
ST=[list(M) for M in extra]
print("with extra opers:", len(ST))

def maxr1(M): return max((p[1] for p in M), default=0)

bad_by_level={}
tot_by_level={}
examples={}
for M in ST:
    t=translate(M)
    c=conv(t)
    ok=in_OT(c)
    L=maxr1(M)
    tot_by_level[L]=tot_by_level.get(L,0)+1
    if not ok:
        bad_by_level[L]=bad_by_level.get(L,0)+1
        if L not in examples:
            examples[L]=M
print("maxr1 level : total / NOT-wf3")
for L in sorted(tot_by_level):
    print(f"  maxr1={L}: {tot_by_level[L]:6d} total, {bad_by_level.get(L,0):6d} not-wf3")
print("\nfirst non-wf3 example per level:")
for L in sorted(examples):
    M=examples[L]
    print(f"  maxr1={L}: {''.join('(%d,%d)'%(a,b) for a,b in M)}")
