import sys; sys.path.insert(0,'.'); sys.setrecursionlimit(100000)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term, G
from fast_pss import oper

# semantic OT3 on NF: for each principal D_a(b) hereditarily in a translate,
# for all x in Gterm a b:  oV x < oV b   (proxy: lt_term(nrm x, nrm b))
def principals(t):           # yield (a,b) for every principal hereditarily
    for p in t:
        _,a,b=p
        yield (a,b)
        yield from principals(b)
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
terms=set(conv(translate(list(M))) for M in extra)
print("terms:",len(terms))
sem=0; tot=0; synfail=0; collapse=0; ex=[]
seen=set()
for c in terms:
    for (a,b) in principals(c):
        key=(a,b)
        if key in seen: continue
        seen.add(key)
        for x in G(a,b):
            tot+=1
            nx,nb=nrm(x),nrm(b)
            semok = lt_term(nx,nb)           # oV x < oV b ?
            synok = lt_term(x,b)             # olt x b ?
            if not synok: synfail+=1
            if not synok and semok: collapse+=1   # OT3 syn fails but sem holds (collapse)
            if not semok:
                sem+=1
                if len(ex)<6: ex.append((a,b,x))
print(f"principal-Gterm checks: {tot}  distinct principals: {len(seen)}")
print(f"  syntactic OT3 fails (not olt x b): {synfail}")
print(f"  COLLAPSE (syn fail but sem holds): {collapse}")
print(f"  ★ semantic OT3 FAILS (oV x >= oV b): {sem}")
for a,b,x in ex: print("   SEMVIOL a=",a)
