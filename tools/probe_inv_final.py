#!/usr/bin/env python3
"""Confirm the invariant I and that proj-mono holds under I.

Candidate I on a wf3 term t at collapse point y:
  I_lead:  y < lead(t)            (head sub strictly below leading sub)
  I_allsub: every subscript in t is > y   (y below ALL subscripts)
  I_topge:  y <= every TOP subscript

Test: build the wf3 pool, partition by (y,t) satisfying each candidate,
re-run proj-mono ONLY on pairs where BOTH lo,hi satisfy I, count reversals.
Goal: find an I with 0 reversals that the arg-zone class provably satisfies.
"""
import sys, itertools, random
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
random.seed(55)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term, fmtb, G
from fast_pss import oper

def proj(a,x):
    bb=x
    while True:
        bad=[g for g in G(a,bb) if not lt_term(g,bb)]
        if not bad: break
        g=bad[0]
        for h in bad[1:]:
            if lt_term(g,h): g=h
        bb=g
    return bb

def lead(t): return t[0][1] if t else -1
def allsubs(t):
    out=[]
    for p in t:
        out.append(p[1]); out+=allsubs(p[2])
    return out
def topsubs(t): return [p[1] for p in t]
def subterms(t):
    out=set()
    def rec(s):
        out.add(s)
        for p in s: rec(p[2])
        for i in range(1,len(s)+1): out.add(s[i:])
    rec(t); return out

base=enum_ST(seed_max_v=5,oper_ns=(1,2,3,4,5),max_len=16,rounds=8)
extra=set(base); cur=list(extra)
for _ in range(5):
    new=[]
    for M in cur:
        M=list(M)
        if len(M)<2: continue
        for n in (1,2,3,4,5):
            tt=tuple(oper(M,n))
            if len(tt)<=22 and tt not in extra:
                extra.add(tt); new.append(tt)
    cur=new
    if not cur: break
print('deep ST closure =',len(extra),flush=True)

# wf3 pool from a sample
exl=list(extra); random.shuffle(exl)
wf3=set()
for M in exl[:40000]:
    c=conv(translate(list(M)))
    for s in subterms(c):
        wf3.add(nrm(s))
        if len(wf3)>250000: break
    if len(wf3)>250000: break
wf3=list(wf3); random.shuffle(wf3); wf3=wf3[:1000]
print('wf3 pool tested size=',len(wf3))

def Ilead(t,y):  return t!=() and y < lead(t)
def Iall(t,y):   return all(s>y for s in allsubs(t)) and t!=()
def Itop(t,y):   return t!=() and all(s>=y for s in topsubs(t))

def run(I,name):
    tot=rev=coll=0; ex=[]
    for y in range(0,7):
        sub=[t for t in wf3 if I(t,y)]
        for p,q in itertools.combinations(sub,2):
            if lt_term(p,q): lo,hi=p,q
            elif lt_term(q,p): lo,hi=q,p
            else: continue
            tot+=1
            pl,ph=proj(y,lo),proj(y,hi)
            if lt_term(ph,pl):
                rev+=1
                if len(ex)<5: ex.append((y,lo,hi))
            elif pl==ph: coll+=1
    print(f'[{name}] pairs={tot} reversals={rev} collapses={coll}')
    for y,lo,hi in ex[:4]:
        print(f'   REV y={y}: {fmtb(lo)} <o {fmtb(hi)} -> {fmtb(proj(y,lo))} vs {fmtb(proj(y,hi))}')

run(Ilead,'I_lead: y<lead(t)')
run(Iall,'I_allsub: all subs > y')
run(Itop,'I_top: all topsubs >= y')
print('DONE')
