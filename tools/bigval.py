import sys, itertools, random
sys.path.insert(0,'.')
from wfe_explore import translate, olt, maxsub, fmt, enum_ST
from argsa_check import topsummands, sargs
from valnorm import conv, nrm, lt_term, fmtb
random.seed(7)
ST = enum_ST(seed_max_v=5, oper_ns=(1,2,3,4,5), max_len=16, rounds=9)
print('corpus', len(ST), flush=True)
NF = {translate(M) for M in ST}
# hereditary blocks: all subterm spine-blocks (args at any depth)
def blocks(t, acc):
    if t == (): return
    a,b,c = t
    acc.add(t)
    blocks(b, acc); blocks(c, acc)
B = set()
for w in NF: blocks(w, B)
print('NF', len(NF), 'hereditary blocks', len(B), flush=True)
pool = list(NF) + random.sample(sorted(B, key=str), min(1500, len(B)))
pool = random.sample(pool, min(2300, len(pool)))
ncache = {}
def N(w):
    if w not in ncache: ncache[w] = nrm(conv(w))
    return ncache[w]
eq=rev=tot=0; ex=[]
for s,t in itertools.combinations(pool,2):
    if olt(s,t): lo,hi = s,t
    elif olt(t,s): lo,hi = t,s
    else: continue
    tot += 1
    nl,nh = N(lo),N(hi)
    if nl == nh:
        # cross-level collapse is allowed ONLY if levels differ? record all
        eq += 1
        if len(ex)<8: ex.append(('EQ',lo,hi))
    elif lt_term(nh,nl):
        rev += 1
        if len(ex)<8: ex.append(('REV',lo,hi))
print(f'pairs={tot} collapse={eq} reversals={rev}', flush=True)
for tag,lo,hi in ex:
    print(f'{tag}: {fmt(lo)} (lv{maxsub(lo)}) <o {fmt(hi)} (lv{maxsub(hi)})')
    print(f'   {fmtb(N(lo))} vs {fmtb(N(hi))}')
