#!/usr/bin/env python3
"""Sound-gate + structural probe for sigma_seqlex_mono (nrm_order_pres).

Target (term-side, the proxy used throughout this repo: nrm-image term order
== ordinal value order, since nrm lands in OT):
    v,u in NF, olt v u  ==>  nrm v <T nrm u   (strict, no collapse, no reversal)

Also tests candidate structural sub-lemmas for the SEQUENCE-side block
induction, to find a provable decomposition:
  (D1) value preservation:   nrm v <T nrm u  iff  oV v < oV u  -- here proxied
       by: is the term order of nrm-images consistent with a strict total order
       refining olt on NF? (we test transitivity-free: no collapse/reversal)
  (D2) compositional nrm on zones: with the seqlex zone split of a NF block,
       does nrm act zone-locally up to the ins-absorption seam?
"""
import sys, itertools, random
sys.path.insert(0, '.')
sys.setrecursionlimit(1000000)
from wfe_explore import translate, olt, maxsub, fmt, enum_ST
from valnorm import conv, nrm, lt_term, fmtb

random.seed(11)

# ---- corpus: ST_PS closure, reasonably deep but FAST ----
ST = enum_ST(seed_max_v=5, oper_ns=(1,2,3,4,5), max_len=15, rounds=8)
print('ST_PS corpus =', len(ST), flush=True)

NF = [translate(M) for M in ST]
NFset = set(NF)
print('distinct NF =', len(NFset), flush=True)

ncache = {}
def N(w):
    if w not in ncache: ncache[w] = nrm(conv(w))
    return ncache[w]

# ---- MAIN: nrm strict-monotone on NF ----
pool = sorted(NFset, key=lambda w: (maxsub(w), len(fmt(w))))
# cap pairs but sample widely across levels
if len(pool) > 1400:
    pool = random.sample(pool, 1400)
eq = rev = tot = 0
ex = []
for s, t in itertools.combinations(pool, 2):
    if olt(s, t): lo, hi = s, t
    elif olt(t, s): lo, hi = t, s
    else: continue
    tot += 1
    nl, nh = N(lo), N(hi)
    if nl == nh:
        eq += 1
        if len(ex) < 6: ex.append(('COLLAPSE', lo, hi))
    elif lt_term(nh, nl):
        rev += 1
        if len(ex) < 6: ex.append(('REVERSAL', lo, hi))
print(f'MAIN nrm-mono on NF: ordered_pairs={tot} collapse={eq} reversal={rev}', flush=True)
for tag, lo, hi in ex:
    print(f'  {tag}: {fmt(lo)} (lv{maxsub(lo)}) <o {fmt(hi)} (lv{maxsub(hi)})')
    print(f'     nrm: {fmtb(N(lo))}   vs   {fmtb(N(hi))}')

# ---- D2: zone-local action of nrm on the FIRST principal of a NF block ----
# For NF term w = P a b c (= conv form): nrm w = ins a (proj a (nrm b)) (nrm c).
# Question: is nrm a "function of (nrm b, nrm c, a)" i.e. does the head's
# normalization only need the normalized argument and normalized tail? (true by
# def) -- the real question for the block induction is whether olt is decided by
# the FIRST differing zone AFTER normalization, the same way seqlex decides it
# before.  Test: for NF pairs lo<hi sharing the same lead subscript a and same
# nrm(tail), is the order decided by nrm(arg)?  And conversely.
def head(w):
    if w == (): return None
    a, b, c = w
    return a, b, c

dec_bad = 0; dec_tot = 0
for s, t in itertools.combinations(pool, 2):
    if not olt(s, t): continue
    hs, ht = head(s), head(t)
    if hs is None or ht is None: continue
    as_, bs, cs = hs; at_, bt, ct = ht
    if as_ != at_: continue          # same lead subscript
    ns, nt = N(s), N(t)
    if ns == nt: continue
    # nrm s, nrm t are ins a (proj a (nrm bs)) (nrm cs) etc.
    nbs, nbt = nrm(conv(bs)), nrm(conv(bt))
    pbs = None  # we don't replicate proj here; just check arg/tail decision
    ncs, nct = nrm(conv(cs)), nrm(conv(ct))
    dec_tot += 1
    # claim: olt s t  ==> (olt-on-args bs,bt)  OR (bs==bt and tail decides)
    # measured at the *normalized* level via lt_term on nrm
    arg_lt = lt_term(nbs, nbt)
    arg_eq = (nbs == nbt)
    tail_lt = lt_term(ncs, nct)
    if not (arg_lt or (arg_eq and tail_lt)):
        dec_bad += 1
        if dec_bad <= 5:
            print(f'  D2-miss: {fmt(s)} <o {fmt(t)}  nbs={fmtb(nbs)} nbt={fmtb(nbt)} ncs={fmtb(ncs)} nct={fmtb(nct)}')
print(f'D2 (same-lead, arg-or-tail decides nrm-order): tot={dec_tot} miss={dec_bad}', flush=True)

print('DONE', flush=True)
