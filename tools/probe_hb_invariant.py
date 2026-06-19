import sys; sys.setrecursionlimit(1000000)
from valnorm import nrm, lt_term, fmtb, conv
from wfe_explore import translate
from try_proj import Glist, parse_seq, proj as projfun

Z=()
def lead(t): return 0 if t==() else t[0][1]
def harg(t): return () if t==() else t[0][2]
def is_fire(u,t):
    res,_=projfun(u,t); return res!=t

# enumerate ST_PS standard forms by BFS from diag, using bms expansion? Simpler: reuse a generator.
# Build standard forms via the oper expansion using bms binary.
import subprocess, re
BMS="/home/koteitan/proofs/yaBMS/c/bms"
def expand(M,n):
    s="".join(f"({a},{b})" for a,b in M)
    out=subprocess.run([BMS,f"{s}[{n}]"],capture_output=True,text=True).stdout.strip()
    return parse_seq(out) if out else None

# BFS closure from diagSeq 0 v
def diag(v): return [(j,j) for j in range(v+1)]
seen=set(); forms=[]
from collections import deque
dq=deque()
for v in range(5): 
    d=tuple(diag(v)); 
    if d not in seen: seen.add(d); dq.append(list(d)); forms.append(list(d))
steps=0
while dq and len(seen)<8000:
    M=dq.popleft()
    if len(M)<=1: continue
    for n in (1,2,3):
        N=expand(M,n)
        if N and 1<len(N)<=14:
            t=tuple(N)
            if t not in seen:
                seen.add(t); dq.append(N); forms.append(N)
print(f"forms={len(forms)}")

# For each form (0,*)#r, arg-zone, X, hb; check tied criticals
tot=0; tiedtot=0; viol_tied=0; hb_0canon=0; hb_total=0
badexamples=[]
for M in forms:
    if not M or M[0][0]!=0: continue
    r=M[1:]
    # arg-zone = takeWhile 0<fst
    W=[]
    for q in r:
        if q[0]>0: W.append(q)
        else: break
    if not W: continue
    X=nrm(conv(translate([ (a,b) for a,b in W ])))
    if not is_fire(0,X): continue
    tot+=1
    hb=harg(X)
    hb_total+=1
    # 0-canonical?
    p0,_=projfun(0,hb)
    if p0==hb: hb_0canon+=1
    # tied criticals of hb
    for g in Glist(0,hb):
        if lead(g)==lead(hb):
            tiedtot+=1
            if not lt_term(g,hb):
                viol_tied+=1
                if len(badexamples)<5: badexamples.append((fmtb(X),fmtb(hb),fmtb(g)))
print(f"firing X={tot}  hb 0-canonical={hb_0canon}/{hb_total}")
print(f"tied criticals of hb={tiedtot}  NOT <hb (violations)={viol_tied}")
for X,hb,g in badexamples: print("  VIOL X=",X," hb=",hb," g=",g)
# sample hb structures
print("--- sample hb shapes (first 12 firing) ---")
c=0
for M in forms:
    if not M or M[0][0]!=0: continue
    r=M[1:]; W=[]
    for q in r:
        if q[0]>0: W.append(q)
        else: break
    if not W: continue
    X=nrm(conv(translate([(a,b) for a,b in W])))
    if not is_fire(0,X): continue
    hb=harg(X)
    subs=set()
    def collect(t):
        if t==(): return
        subs.add(t[0][1]); collect(t[0][2]); 
        for p in t[1:]: subs.add(p[1]); collect(p[2])
    collect(hb)
    print(f"  X={fmtb(X)[:40]:40} hb={fmtb(hb)[:40]:40} lead(hb)={lead(hb)} subs(hb)={sorted(subs)}")
    c+=1
    if c>=12: break
