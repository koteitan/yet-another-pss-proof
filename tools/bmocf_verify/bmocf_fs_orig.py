"""BMOCF native fundamental sequence t[n] (2-row), tested against bms expansion.
Term rep (v.py compatible): 0 | ('D', sub, inner) | (p0,p1,...) sum.
sub is an Idx = tuple of positive ints (non-increasing). v's int a -> () if 0 else (a,).
"""
import importlib.util, re, subprocess
spec=importlib.util.spec_from_file_location("v","v.py"); v=importlib.util.module_from_spec(spec); spec.loader.exec_module(v)
BMS="/home/koteitan/proofs/yaBMS/c/bms"

ZERO=0
def _norm(sub):
    sub=tuple(sub)
    while sub and sub[-1]==0: sub=sub[:-1]
    return sub
def D(sub,inner): return ('D',_norm(sub),inner)
def isD(t): return isinstance(t,tuple) and len(t)==3 and t[0]=='D'
def princs(t):  # list of principal terms in sum
    if t==ZERO: return []
    if isD(t): return [t]
    return list(t)
def mk(ps):
    ps=[p for p in ps if p!=ZERO]
    if not ps: return ZERO
    return ps[0] if len(ps)==1 else tuple(ps)

def conv(t):  # v's int-subscript term -> Idx-subscript term
    if t==ZERO: return ZERO
    if isD(t):
        _,a,inner=t
        sub=() if a==0 else (a,)
        return D(sub,conv(inner))
    return tuple(conv(p) for p in t)

# ---- Idx ops ----
def idx_lt(a,b):  # Cofinality '<' on Idx
    if len(b)==0: return False
    m=min(len(a),len(b))
    for i in range(1,m):       # i in N_+, i<min
        if not (a[i]<b[i]): return False
    return True
def idx_add(a,b):
    n=max(len(a),len(b))
    return tuple((a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(n))
def idx_scale(m,a): return tuple(m*x for x in a)
def is_idx(a): return all(x>0 for x in a) and all(a[i]>=a[i+1] for i in range(len(a)-1))

# ---- Ancestor on M = list of Idx ----
def Mij(M,i,j): 
    return M[j][i] if (0<=j<len(M) and 0<=i<len(M[j])) else 0
def next_M(M,i0,j0,i1,j1):
    if i0!=i1 or not(j0<j1): return False
    for i in range(i1):
        if not le_M(M,i,j0,i,j1): return False
    if not (Mij(M,i1,j0)<Mij(M,i1,j1)): return False
    for j in range(j0+1,j1+1):
        if all(le_M(M,i,j,i,j1) for i in range(i1)):
            if not (Mij(M,i1,j)>=Mij(M,i1,j1)): return False
    return True
def le_M(M,i0,j0,i1,j1):
    if i0!=i1: return False
    if j0==j1: return True
    if j0>j1: return False
    # exists chain j0=J0<..<Jn=j1 with consecutive next_M at row i1
    reach={j0}
    for _ in range(j1-j0+1):
        new=set(reach)
        for jk in list(reach):
            for jn in range(jk+1,j1+1):
                if next_M(M,i1,jk,i1,jn): new.add(jn)
        if new==reach: break
        reach=new
    return j1 in reach

def Ascend(M,t,Delta):
    if len(Delta)==0 or t==ZERO: return t
    ps=princs(t)
    if len(ps)>1:
        return mk([Ascend(M,p,Delta) for p in ps])
    _,a,tp=ps[0]
    Mp=M+[a]; j1=len(Mp)-1; i1=len(Delta)-1
    if le_M(Mp,0,0,0,j1):
        cand=[i for i in range(i1+1) if le_M(Mp,i,0,i,j1)]
        i0=max(cand) if cand else 0
        Dp=Delta[:i0+1]
        return D(idx_add(a,Dp), Ascend(Mp,tp,Delta))
    return D(a, Ascend(Mp,tp,Delta))

# ---- cof ----
EMPTY=('cof','empty'); SUCC=('cof','succ'); NT=('cof','nt')
def TB(b): return ('cof','tb',tuple(b))
def cof(t):
    if t==ZERO: return EMPTY
    ps=princs(t)
    if len(ps)>1: return cof(ps[-1])
    _,a,tp=ps[0]; c=cof(tp)
    if c==EMPTY: return SUCC if len(a)==0 else TB(a)
    if c==SUCC: return NT
    if c==NT: return NT
    # c == TB(b)
    b=c[2]
    if idx_lt(a,b): return NT
    i1=len(b)-1
    cands=[i for i in range(1,min(len(a)-1,i1)) if a[i]>=b[i]]
    i0=min(cands)  # may KeyError if empty -> spec assumes exists
    cc=tuple(a[:i0])+tuple(b[i0:i1+1])
    return TB(cc)

def nat_term(n): return ZERO if n==0 else mk([D((),ZERO)]*n)  # ⌜n⌝ = n copies of psi(0)

def leftmost_sub(t):
    ps=princs(t)
    return ps[0][1]  # subscript of leftmost principal

def fs(t,z):
    ps=princs(t)
    if len(ps)>1:
        t0=mk(ps[:-1]); t1=ps[-1]
        r=fs(t1,z)
        return t0 if r==ZERO else mk(princs(t0)+princs(r))
    _,a,tp=ps[0]; c=cof(tp)
    if c==EMPTY: return z
    if c==SUCC:
        base=D(a,fs(tp,ZERO))
        # times z : z is ⌜n⌝ -> n copies
        n=len(princs(z))
        return mk([base]*n) if n>0 else ZERO
    if c==NT: return D(a,fs(tp,z))
    # c==TB(b), the hard collapse case
    b=c[2]; i1=len(b)-1
    if idx_lt(a,b):
        ap=leftmost_sub(tp); i0=len(ap)-1
        if i0<i1:
            bp=tuple(a_i+(b[i0]-(a[i0] if i0<len(a) else 0))-1 for i,a_i in enumerate([ (a[k] if k<len(a) else 0) for k in range(i0+1)]))
        else:
            bp=tuple((a[k] if k<len(a) else 0)+(b[i1]-(a[i1] if i1<len(a) else 0))-1 for k in range(i0+1))
        Delta=tuple(b[i]-bp[i] for i in range(i1))   # i=0..i1-1
        Dp=Delta[:i0+1]
        if not is_idx(Delta): return None
        n=len(princs(z))  # z=⌜n⌝
        def tau(nn,mm):
            asc=Ascend([bp],tp,idx_scale(mm,Delta))
            if nn==0:
                return fs(asc,ZERO)
            inner=D(idx_add(bp,Dp),tau(nn-1,mm+1))
            return fs(asc,inner)
        return D(a,tau(n,0))
    return D(a,fs(tp,z))

# ---- formatting ----
def fmt(t):
    if t==ZERO: return "0"
    if isD(t):
        _,a,inner=t
        s="ψ"+("" if len(a)==0 else "_"+("("+",".join(map(str,a))+")" if len(a)>1 else str(a[0])))
        return f"{s}({fmt(inner)})"
    return "+".join(fmt(p) for p in t)

def vterm(M):  # M pss string -> Idx-subscript term
    return conv(v.v(M))
def bexp(M,n):
    out=subprocess.run([BMS,f"{M}[{n}]"],capture_output=True,text=True).stdout.strip()
    return out

if __name__=="__main__":
    tests=["(0,0)(1,1)(2,2)(3,3)","(0,0)(1,1)(2,2)","(0,0)(1,1)(2,2)(2,2)","(0,0)(1,1)(1,1)",
           "(0,0)(1,1)(2,2)(3,3)(4,4)","(0,0)(1,1)(2,0)(3,1)"]
    for M in tests:
        t=vterm(M); c=cof(t)
        print(f"\nM={M}  v={fmt(t)}  cof={c[1:]}")
        for n in range(4):
            try: ft=fs(t,nat_term(n))
            except Exception as e: ft=f"ERR:{e}"
            be=bexp(M,n); vbe=fmt(vterm(be)) if be else "(0)"
            print(f"  t[⌜{n}⌝]={fmt(ft) if not isinstance(ft,str) else ft}    | bms[{n}]={be} -> v={vbe}")
