import sys; sys.path.insert(0,'.'); sys.setrecursionlimit(100000)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term, G
from fast_pss import oper
# full proj following maxo discipline (olt-max of bad set), as in nrm.thy
def maxo(x, ys):
    for y in ys:
        if lt_term(x,y): x=y
    return x
def proj(a,b):
    while True:
        bad=[g for g in G(a,b) if not lt_term(g,b)]
        if not bad: break
        b=maxo(bad[0], bad[1:])
    return b
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
seen=set(); tot=0; bad=0; ex=[]
for c in terms:
    for (a,b) in principals(c):
        if (a,b) in seen: continue
        seen.add((a,b))
        tot+=1
        pb=proj(a, nrm(b))                 # proj a (nrm b) as in nrm
        # psi_proj: psi_a(oV b) == psi_a(oV(proj a (nrm b)))
        if val_principal(a,b) != val_principal(a, pb):
            bad+=1
            if len(ex)<6: ex.append((a,b,pb))
print(f"psi_proj (full proj, maxo): tested principals={tot}")
print(f"  ★ psi_a(oV b) != psi_a(oV(proj a (nrm b))) FAILS: {bad}")
for a,b,pb in ex[:6]: print("   FAIL a=",a,"b=",b)
