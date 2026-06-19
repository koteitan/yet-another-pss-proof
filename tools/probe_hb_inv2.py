import sys; sys.setrecursionlimit(1000000)
from valnorm import nrm, lt_term, fmtb, conv
from wfe_explore import translate
from try_proj import Glist, parse_seq, proj as projfun
import subprocess
from collections import deque
BMS="/home/koteitan/proofs/yaBMS/c/bms"
Z=()
def lead(t): return 0 if t==() else t[0][1]
def harg(t): return () if t==() else t[0][2]
def is_fire(u,t):
    res,_=projfun(u,t); return res!=t
def expand(M,n):
    s="".join(f"({a},{b})" for a,b in M)
    out=subprocess.run([BMS,f"{s}[{n}]"],capture_output=True,text=True).stdout.strip()
    return parse_seq(out) if out else None
def diag(v): return [(j,j) for j in range(v+1)]
def all_subs(t):
    s=set()
    def go(t):
        if t==(): return
        for p in t: s.add(p[1]); go(p[2])
    go(t); return s
def is_single_principal(t): return t!=() and len(t)==1

# DEEP closure BFS
LIMIT=int(sys.argv[1]) if len(sys.argv)>1 else 60000
MAXLEN=int(sys.argv[2]) if len(sys.argv)>2 else 20
seen=set(); dq=deque()
for v in range(7):
    d=tuple(diag(v))
    if d not in seen: seen.add(d); dq.append(list(d))
forms=[]
while dq and len(seen)<LIMIT:
    M=dq.popleft(); forms.append(M)
    if len(M)<=1: continue
    for n in (1,2,3):
        N=expand(M,n)
        if N and 1<len(N)<=MAXLEN:
            t=tuple(N)
            if t not in seen: seen.add(t); dq.append(N)
print(f"ST forms explored={len(forms)} (limit {LIMIT}, maxlen {MAXLEN})")

tot=0; hb_0canon=0
i1_fail=0; i2_fail=0; sp_fail=0
i1_ex=[]; i2_ex=[]; sp_ex=[]
leadX_vals={}
for M in forms:
    if not M or M[0][0]!=0: continue
    r=M[1:]; W=[]
    for q in r:
        if q[0]>0: W.append(q)
        else: break
    if not W: continue
    X=nrm(conv(translate([(a,b) for a,b in W])))
    if not is_fire(0,X): continue
    tot+=1
    hb=harg(X); lX=lead(X)
    leadX_vals[lX]=leadX_vals.get(lX,0)+1
    p0,_=projfun(0,hb)
    if p0==hb: hb_0canon+=1
    # I1: hb has no subscript-0 principal
    subs=all_subs(hb)
    if 0 in subs:
        i1_fail+=1
        if len(i1_ex)<6: i1_ex.append((fmtb(X)[:50],fmtb(hb)[:50],sorted(subs)))
    # I2: lead X == 1
    if lX!=1:
        i2_fail+=1
        if len(i2_ex)<6: i2_ex.append((fmtb(X)[:60],lX))
    # SP: hb single principal
    if not is_single_principal(hb):
        sp_fail+=1
        if len(sp_ex)<6: sp_ex.append((fmtb(X)[:50],fmtb(hb)[:50]))
print(f"firing X={tot}")
print(f"hb 0-canonical: {hb_0canon}/{tot}  (FAIL={tot-hb_0canon})")
print(f"(I1) hb no subscript-0 principal: FAIL={i1_fail}/{tot}")
for e in i1_ex: print("   I1-fail:",e)
print(f"(I2) lead X == 1: FAIL={i2_fail}/{tot}   leadX dist={leadX_vals}")
for e in i2_ex: print("   I2-fail:",e)
print(f"(SP) hb single principal: FAIL={sp_fail}/{tot}")
for e in sp_ex: print("   SP-fail:",e)
