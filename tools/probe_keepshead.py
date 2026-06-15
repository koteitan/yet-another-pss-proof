#!/usr/bin/env python3
"""Probe keeps_head_ST_PS structure.

keeps_head M: M=(_,y)#r, A=proj y (nrm(translate aM)), C=nrm(translate tM),
  aM=takeWhile(0<fst) r, tM=dropWhile(0<fst) r.
  if C=P e f g: require NOT (y<e or (y=e and olt A f)), i.e. e<=y and
  (e<y or not olt A f).
Break down:
  - e vs y distribution (how often e<y, e=y, e>y).
  - in the e=y tied case, how often olt A f holds (the bad/absorbing case).
"""
import sys, itertools
sys.path.insert(0,'.'); sys.setrecursionlimit(1000000)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm

Z=()
def proj_three(a, t):
    # proj a t on three-terms. Need the Isabelle proj. We mirror via nrm-on-Buchholz?
    pass

# Work in conv/Buchholz land for nrm; but A=proj y(...) and f are three-terms in
# Isabelle. Simpler: replicate via the python three-term proj if available.
# We approximate using the buchholz nrm structure: top subscript e of nrm(tM).
def tw(r): return [p for p in itertools.takewhile(lambda q:0<q[0],r)]
def dw(r): return list(itertools.dropwhile(lambda q:0<q[0],r))

def top_subscript_nrm(seq):
    """top principal subscript e of nrm(translate seq), or None if Z."""
    t=translate(list(seq))
    b=nrm(conv(t))   # tuple of ('D',a,arg) principals, highest first
    if not b: return None
    return b[0][1]  # subscript of leading principal

ST=list(enum_ST(seed_max_v=6,oper_ns=(1,2,3,4,5),max_len=16,rounds=9))
print('corpus',len(ST),flush=True)
elt=eeq=egt=zero=0
tied=0; ex=[]
for M in ST:
    if not M or M[0][0]!=0: continue
    y=M[0][1]; r=list(M[1:])
    tM=dw(r)
    e=top_subscript_nrm(tM)
    if e is None: zero+=1; continue
    if e<y: elt+=1
    elif e==y: eeq+=1; tied+=1;
    else:
        egt+=1
        if len(ex)<10: ex.append((M,y,e))
print(f'e<y:{elt}  e==y:{eeq}  e>y:{egt}  C=Z:{zero}',flush=True)
print('VIOLATIONS (e>y, would absorb head subscript):')
for M,y,e in ex[:10]: print('  y=',y,'e=',e,'M=',M)
print('DONE',flush=True)
