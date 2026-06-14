import sys; sys.path.insert(0,'.'); sys.setrecursionlimit(100000)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term, G
from fast_pss import oper
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
# oV-value proxy: nrm canonical form of the term equals oV-value iff same nrm.
# Test: is oV(proj a b) == oV b ?  Proxy: nrm(proj a (nrm b)) == nrm(nrm b)?
# Better proxy for "same oV value": nrm(D_a(proj a b)) vs nrm(D_a(b)) already = psi_proj (true).
# Direct oV equality proxy: compare nrm(b) vs nrm(proj a (nrm b)) as terms (oV injective on nrm forms? no).
# Use: two wf3 terms have equal oV iff equal (oV order-embeds wf3, strict). proj a (nrm b) and nrm b both wf3.
# So oV(proj a (nrm b)) == oV(nrm b)  iff  proj a (nrm b) == nrm b (as terms), since oV strict-mono on wf3.
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
seen=set(); tot=0; changed=0; ex=[]
for c in terms:
    for (a,b0) in principals(c):
        if (a,b0) in seen: continue
        seen.add((a,b0))
        nb=nrm(b0)
        pb=proj(a,nb)
        tot+=1
        if pb != nb:   # proj changed the term
            changed+=1
            # since both wf3, pb != nb implies oV differs (oV strict-mono on wf3)
            if len(ex)<5: ex.append((a,nb,pb))
print(f"tested principals={tot}, proj changed the (wf3) term in {changed} cases")
print(f"  => oV(proj a (nrm b)) {'!=' if changed else '=='} oV(nrm b) in those (oV strict-mono on wf3)")
for a,nb,pb in ex[:5]: print("   a=",a,"changed")
