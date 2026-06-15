#!/usr/bin/env python3
"""Find a per-nextrel0-step value relation provable for ST_PS that yields INV2.
Candidates:
 S1: nextrel0 M a b => e1(b) >= e1(a)          (general; expect FALSE)
 S2: nextrel0 M a b => e0(b) > e0(a) (def, trivially true) -- not value
 S3: 'minval below' : let f(j) = min over le0-ancestors-with-row0=0 of e1.
     Actually test: nextrel0 M a b => (e1(b) >= e1(a)) OR (e0(a) < e0(b) AND ???)
 Focus: WHEN does e1(b) < e1(a) for nextrel0 a b?  characterize the failures.
"""
import sys
sys.path.insert(0,'.')
sys.setrecursionlimit(1000000)
from wfe_explore import enum_ST
from fast_pss import oper

def Lng(M): return len(M)
def e0(M,j): return M[j][0]
def e1(M,j): return M[j][1]
def nextrel0(M,j0,j1):
    if not (j0<Lng(M) and j1<Lng(M) and j0<j1): return False
    if not (e0(M,j0)<e0(M,j1)): return False
    for j in range(j0+1,j1):
        if e0(M,j) < e0(M,j1): return False
    return True

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

# characterize nextrel0 a b with e1(b)<e1(a)
tot=0; bad=0; badex=[]
# property to test: when e1(b)<e1(a), is e0(a)>0 always? (i.e. a not an anchor)
anchorbad=0
for M in extra:
    M=list(M)
    n=len(M)
    for a in range(n):
        for b in range(a+1,n):
            if nextrel0(M,a,b):
                tot+=1
                if e1(M,b)<e1(M,a):
                    bad+=1
                    if e0(M,a)==0: anchorbad+=1; badex.append((a,b,M)) if len(badex)<8 else None
print(f'nextrel0 pairs={tot}, e1(b)<e1(a): {bad}, of which row0(a)=0: {anchorbad}')
for x in badex: print('  ANCHORBAD',x)

# Now: the climb structure. INV2 proof idea via induction on (j - a).
# At each climb step from j to its nextrel0-parent p:
#   we have e1 relation? climbing j->p where p=parent. p<j, e0(p)<e0(j), valley.
#   For INV2 we go anchor a -> ... -> j.  The KEY question: is the parent chain
#   from j down to the row0=0 anchor monotone NONincreasing in e1?
# Test: nextrel0 M p j (p is A parent of j) => e1(p) <= e1(j) WHEN e0(p)>0 too?
# i.e. is e1 nondecreasing along the SPECIFIC parent chain from any j to its floor?
# Build floor-parent: parent(j) = max p<j with nextrel0 M p j? (nextrel0 parent unique-ish)
def parents(M,j):
    return [p for p in range(j) if nextrel0(M,p,j)]
# test parent chain monotonicity in e1
totC=okC=0; exC=[]
for M in extra:
    M=list(M)
    n=len(M)
    for j in range(n):
        ps=parents(M,j)
        for p in ps:
            totC+=1
            # climbing p->j (p parent). claim e1(j) >= e1(p)? general
            if e1(M,j)>=e1(M,p): okC+=1
            elif len(exC)<8: exC.append((p,j,M))
print(f'parent step e1(j)>=e1(p): {okC}/{totC}')
for x in exC: print('  PC',x)
print('DONE')
