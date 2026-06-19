#!/usr/bin/env python3
"""Test sufficient invariants for tied_crit_lt_hb on ST images.

We want a STRUCTURAL invariant I(hb) such that:
  (A) I(hb) holds for every firing arg-zone head argument hb  (deep 0-fail)
  (B) I + wf3 + (maxsub hb = lead hb) PROVES olt g hb for tied criticals,
      ideally by a clean induction.

Candidate invariants tested on real hb:
  INV-ARGLEAD: every principal D_a(arg)+... node N inside hb has lead(arg) <= a
               (argument never lead-exceeds its own subscript)
  INV-D0LEAD : every D0(arg) node inside hb has lead(arg) < lead hb
               (buried-under-0 args have strictly smaller lead than hb)
  INV-HARGLT : for hb=P L B C, every tied G0 critical g!=hb has olt (harg g) B
               OR harg g == B with tail strictly less  -- i.e. lex via harg.
  Also re-check on the wf3 COUNTEREXAMPLE that each invariant FAILS there
  (so it's class-essential, distinguishing real hb from the cex).
"""
import sys
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term as olt
from fast_pss import oper

def Glist(u,x):
    if x==(): return []
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    head = ([b]+Glist(u,b)) if u<=a else []
    return head+Glist(u,c)
def Gset(u,x): return set(Glist(u,x))
def fires(a,x): return any(not olt(g,x) for g in Glist(a,x))
def harg(x): return () if x==() else x[0][2]
def leadof(x): return 0 if x==() else x[0][1]
def maxsub(x):
    if x==(): return 0
    return max(x[0][1], max(maxsub(x[0][2]), maxsub(tuple(x[1:]))))
def takeW(r):
    out=[]
    for p in r:
        if p[0]>0: out.append(p)
        else: break
    return out
def NT(S): return nrm(conv(translate(list(S))))

def allnodes(x):
    # yield every principal-list subterm's leading principal (a,arg,rest)
    if x==(): return
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    yield (a,b,c)
    yield from allnodes(b)
    yield from allnodes(c)

def inv_arglead(hb):
    return all(leadof(b) <= a for (a,b,c) in allnodes(hb))
def inv_d0lead(hb):
    L=leadof(hb)
    return all((a>0) or (leadof(b) < L) for (a,b,c) in allnodes(hb))

# wf3 counterexample
Zc=()
cex = ((('D',2,((('D',1,((('D',2,((('D',2,()),('D',2,()),('D',2,()))),)),)),)),)),)
# build cleanly: D2(D1(D2(D2+D2+D2)))
sum3=(('D',2,Zc),('D',2,Zc),('D',2,Zc))
inner=(('D',2,sum3),)
d1=(('D',1,inner),)
cex=(('D',2,d1),)

base=enum_ST(seed_max_v=5,oper_ns=(1,2,3,4,5),max_len=16,rounds=8)
extra=set(base); cur=list(extra)
for _ in range(5):
    new=[]
    for M in cur:
        M=list(M)
        if len(M)<2: continue
        for n in (1,2,3,4,5):
            tt=tuple(oper(M,n))
            if len(tt)<=22 and tt not in extra: extra.add(tt); new.append(tt)
    cur=new
    if not cur: break
print('deep ST closure =',len(extra),flush=True)
seen=set(); imgs=[]
for M in extra:
    M=list(M)
    if not M or M[0][0]!=0: continue
    aM=tuple(takeW(M[1:]))
    if not aM: continue
    X=NT(aM)
    if X in seen: continue
    seen.add(X); imgs.append(X)
print('distinct images=',len(imgs),flush=True)

nfire=0
f_arglead=0; f_d0lead=0
ex_al=None; ex_dl=None
for X in imgs:
    if X==(): continue
    if not fires(0,X): continue
    nfire+=1
    hb=harg(X)
    if hb==(): continue
    if not inv_arglead(hb):
        f_arglead+=1
        if ex_al is None: ex_al=hb
    if not inv_d0lead(hb):
        f_d0lead+=1
        if ex_dl is None: ex_dl=hb
print('firing images =',nfire)
print('INV-ARGLEAD fails on real hb =',f_arglead,' (want 0)')
print('INV-D0LEAD  fails on real hb =',f_d0lead,' (want 0)')
print('--- class-essential check on wf3 cex hb=D2(D1(D2(D2+D2+D2))) ---')
print('  cex wf3-ish maxsub=',maxsub(cex),'lead=',leadof(cex))
print('  cex INV-ARGLEAD =',inv_arglead(cex),'(want False = class-essential)')
print('  cex INV-D0LEAD  =',inv_d0lead(cex),'(want False)')
if ex_al: print('  ARGLEAD failing real hb ex:',ex_al)
if ex_dl: print('  D0LEAD failing real hb ex:',ex_dl)
print('DONE',flush=True)
