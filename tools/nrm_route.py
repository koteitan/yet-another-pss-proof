import sys; sys.path.insert(0,'.')
from wfe_explore import translate, enum_ST, olt
sys.setrecursionlimit(100000)
from valnorm import conv, nrm, lt_term, in_OT
from fast_pss import oper, Lng

# reconstruct three-term from conv-form to compare olt? We'll compare via lt_term on conv.
# olt on three (wfe_explore) vs lt_term on conv should agree. We work in conv space.

ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=14, rounds=7)
extra=set(tuple(M) for M in ST); cur=list(extra)
for _ in range(2):
    new=[]
    for M in cur:
        if len(M)<2: continue
        for n in (1,2,3,4):
            tt=tuple(oper(list(M),n))
            if tt not in extra: extra.add(tt); new.append(tt)
    cur=new
ST=[list(M) for M in extra]
print("forms",len(ST))

# N1: nrm in OT ; N2: oV-preserve can't test directly (need ordinals) -> proxy: nrm idempotent & =id on OT
# N3: olt(s,t) => lt_term(nrm s, nrm t)  on STEP pairs (the only ones we need)
n1=n3=tested=0; ex3=[]
for M in ST:
    if Lng(M)<2: continue
    for n in (1,2,3):
        Mn=oper(list(M),n)
        if Mn==M: continue
        cs=conv(translate(Mn)); ct=conv(translate(M))
        # m_step_decreases guarantees olt(translate Mn, translate M):
        assert lt_term(cs,ct), ("step not olt-dec?!",M,n)
        ns=nrm(cs); nt=nrm(ct)
        if not in_OT(ns): n1+=1
        tested+=1
        if not lt_term(ns,nt):
            n3+=1
            if len(ex3)<5: ex3.append((M,n,ns,nt))
print(f"step pairs tested={tested}")
print(f"N1 nrm(translate Mn) notin OT: {n1}")
print(f"N3 nrm does NOT preserve olt on step pair: {n3}")
for M,n,ns,nt in ex3:
    print("  N3 VIOL n=",n,''.join('(%d,%d)'%(x,y) for x,y in M))
