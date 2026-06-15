#!/usr/bin/env python3
"""Pin the EXACT resisting step of clause 2.
For firing arg-zone X = ins y1 (proj y1 (nrm arg)) (nrm tail), hb=harg X=proj y1(nrm arg).
proj_G (FREE) gives: all g in Gterm y1 hb : olt g hb.
T_allGhb NEEDS:      all g in Gterm 0  hb : olt g hb.
The gap is Gterm 0 hb \\ Gterm y1 hb (criticals visible at 0 but not at y1=lead X).

Check:
 A : lead X == 1 on all firing images (so y1=1).         (known)
 B : Gterm 0 hb == Gterm y1 hb  ?  (if equal, proj_G closes it FREE; if not, gap is real)
     gap_nonempty = images where Gterm 0 hb strictly bigger.
 C : among gap criticals g in Gterm0 hb \\ Gterm(leadX) hb, are they all olt hb? (must be, T_allGhb holds)
     and are they witnessed by a principal of subscript < y1 inside hb?
 D : is hb proj-(lead X)-stable but NOT trivially proj-0-stable?
     count: hb fires at 0 ? (should be 0)  vs  gap_nonempty (>0 means the free proj_G is insufficient)
"""
import sys
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
from wfe_explore import translate, enum_ST
from valnorm import conv, nrm, lt_term
from fast_pss import oper
def Glist(u,x):
    if x==(): return []
    a=x[0][1]; b=x[0][2]; c=tuple(x[1:])
    head = ([b]+Glist(u,b)) if u<=a else []
    return head+Glist(u,c)
def Gset(u,x): return set(Glist(u,x))
def fires(a,x): return any(not lt_term(g,x) for g in Glist(a,x))
def harg(x): return () if x==() else x[0][2]
def leadof(x): return 0 if x==() else x[0][1]
def takeW(r):
    out=[]
    for p in r:
        if p[0]>0: out.append(p)
        else: break
    return out
def NT(S): return nrm(conv(translate(list(S))))
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
nfire=0; leadne1=0; gap_nonempty=0; gap_total_crit=0; gap_crit_not_olt=0
hb_fire0=0; proj_leadhb_stable_fail=0
for X in imgs:
    if not fires(0,X): continue
    nfire+=1
    L=leadof(X)
    if L!=1: leadne1+=1
    hb=harg(X)
    G0=Gset(0,hb); GL=Gset(L,hb)
    gap=G0-GL
    if gap: gap_nonempty+=1
    gap_total_crit+=len(gap)
    for g in gap:
        if not lt_term(g,hb): gap_crit_not_olt+=1
    if fires(0,hb): hb_fire0+=1
    # is hb proj-L-stable? (proj_G says Gterm L hb all < hb i.e. not pfire L hb)
    if any(not lt_term(g,hb) for g in GL): proj_leadhb_stable_fail+=1
print(f'firing images = {nfire}')
print(f'A lead X != 1 = {leadne1}')
print(f'B images with Gterm0 hb STRICTLY bigger than Gterm(leadX) hb = {gap_nonempty}')
print(f'  total gap criticals = {gap_total_crit}, of those NOT olt hb = {gap_crit_not_olt} (want 0)')
print(f'C hb fires at 0 = {hb_fire0} (want 0)')
print(f'D proj_G insufficiency: pfire(leadX) hb (should be 0, free from proj_G) = {proj_leadhb_stable_fail}')
print('--- interpretation ---')
print('If B>0 and C=0: the FREE proj_G(subscript leadX) does NOT cover Gterm0;')
print('  the extra gap criticals being <o hb is the class-essential residue.')
print('DONE')
