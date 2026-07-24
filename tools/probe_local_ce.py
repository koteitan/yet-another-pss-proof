"""Is ArgDomCore derivable from the LOCAL invariants (steps1, z0ok, r1ok, cnf)?
NO: the sequence below satisfies all four and violates ArgDomCore.
(Faithful re-implementations of the Lean definitions.)"""
import sys
sys.path.insert(0,'.')
from probe_copycrux import sle, shiftr0
from probe_bmocf_ancestor import enum_depth

def steps1(M): return all(M[j+1][0] <= M[j][0]+1 for j in range(len(M)-1))
def z0ok(M):   return all(p[1]==0 for p in M if p[0]==0)
def r1ok(M):
    for j in range(len(M)):
        if M[j][0] == 0: continue
        ok=False
        for k in range(j):
            if M[k][0]+1==M[j][0] and all(M[j][0] <= M[l][0] for l in range(k+1,j)) \
               and M[j][1] <= M[k][1]+1:
                ok=True; break
        if not ok: return False
    return True
# translate / olt / cnf, 1:1 with Mechanized.lean
def translate(M):
    if not M: return None                      # Z
    p=M[0]; rest=M[1:]; i=0
    while i<len(rest) and rest[i][0]>p[0]: i+=1
    return (p[1], translate(rest[:i]), translate(rest[i:]))
def olt(x,y):
    if x is None: return y is not None
    if y is None: return False
    a,b,c=x; e,f,g=y
    return a<e or (a==e and olt(b,f)) or (a==e and b==f and olt(c,g))
def cnf(t):
    if t is None: return True
    a,b,c=t
    if c is None: return cnf(b)
    e,f,g=c
    return cnf(b) and not olt((a,b,None),(e,f,None)) and cnf(c)
def arg(N,i):
    lv=N[i][0]; out=[]
    for p in N[i+1:]:
        if p[0]>lv: out.append(p)
        else: break
    return out
def c4(A1,u,e,w):
    return all(x[1]>=w for t,x in enumerate(A1)
               if x[0]<u+e and all(y[0]>x[0] for y in A1[t+1:]))

N=[(0,0),(1,1),(2,1),(3,2),(2,1),(3,2)]
print("N =", N)
print(" steps1",steps1(N)," z0ok",z0ok(N)," r1ok",r1ok(N)," cnf",cnf(translate(N)))
i=1; u,w=N[i]; A=arg(N,i); t=2; e=A[t][0]-u; A1=A[:t]; B=arg(N,i+1+t)
print(f" i={i} (u,w)={(u,w)} A={A} t={t} e={e} A1={A1} SpineOK={c4(A1,u,e,w)} B={B}")
print(" shiftr0 e A =", shiftr0(e,A))
print(" sle B (shiftr0 e A) =", sle(B,shiftr0(e,A)), "   <-- ArgDomCore VIOLATED")
seen=set()
for (vmax,ns,ml,rounds) in [(5,(1,2,3,4,5),12,8),(4,(1,2,3),16,10),(3,(1,2,3,4,5),14,9)]:
    seen |= set(tuple(M) for M in enum_depth(vmax,ns,ml,rounds))
print(" reachable (ST_PS) in the union of three closures:", tuple(N) in seen)
