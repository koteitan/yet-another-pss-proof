import sys; sys.path.insert(0,'.'); sys.setrecursionlimit(100000)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term, le_term, G
from fast_pss import oper
# psi_a(oV b) proxy = nrm(P a b Z) as normal form; equality of values = equal normal forms
def Pterm(a,b): return ((('D',a,b)))   # principal D_a(b) as a 1-principal term tuple
def val_principal(a,b): return nrm(((('D',a,b)),))  # nrm of [D_a(b)]
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
seen=set(); tot=0; bad=0; ge=0; lt=0; ex=[]
for c in terms:
    for (a,b) in principals(c):
        if (a,b) in seen: continue
        seen.add((a,b))
        for g in set(map(tuple, [list(x) for x in G(a,b)])):
            g=tuple(g)
            if lt_term(g,b): continue        # only the projected-away ones: NOT olt g b
            tot+=1
            # value direction
            if le_term(b,g): ge+=1
            else: lt+=1
            # per-step collapse: psi_a(oV b) == psi_a(oV g) ?
            vb=val_principal(a,b); vg=val_principal(a,g)
            if vb!=vg:
                bad+=1
                if len(ex)<6: ex.append((a,b,g))
print(f"per-step (g in Gterm a b, NOT olt g b): tested={tot}")
print(f"  value direction: oV b<=oV g (ge): {ge}   oV b> oV g (lt): {lt}")
print(f"  ★ psi_a(oV b) != psi_a(oV g)  [per-step collapse FAILS]: {bad}")
for a,b,g in ex[:6]: print("   FAIL a=",a)
