import sys; sys.path.insert(0,'.'); sys.setrecursionlimit(100000)
from wfe_explore import translate, enum_ST
from valnorm import conv, lt_term, le_term, G
from fast_pss import oper

# conv-form: tuple of ('D',a,term). term=tuple of principals.
def OT2(t):  # spine principals non-increasing (a[i] >= a[i+1] as principals), recursively in args
    for i in range(len(t)-1):
        p=t[i]; q=t[i+1]
        # p>=q as principal? principal order: subscript-first
        _,u,a=p; _,v,b=q
        ge = (v<u) or (v==u and (lt_term(b,a) or a==b))
        if not ge: return False
    return all(OT2(p[2]) for p in t)
def OT3(t):  # every principal: all g in G_a(arg) are < arg
    for p in t:
        _,a,b=p
        if not all(lt_term(g,b) for g in G(a,b)): return False
        if not OT3(b): return False
    return True

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
print("distinct translate terms:",len(terms))
ot2bad=ot3bad=both=0
for c in terms:
    o2=OT2(c); o3=OT3(c)
    if not o2: ot2bad+=1
    if not o3: ot3bad+=1
print(f"OT2 (spine non-incr) FAILS on {ot2bad} / {len(terms)} translates")
print(f"OT3 (Gterm<arg)      FAILS on {ot3bad} / {len(terms)} translates")
