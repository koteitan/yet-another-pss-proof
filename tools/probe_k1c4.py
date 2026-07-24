"""K1' with the RIGHT-VISIBLE (spine-only) side condition (c4):
   for every split A1 = U ++ x :: V with x.1 < u+e and every y in V having y.1 > x.1,
   require w <= x.2.
Check: (a) 0 violations, (b) same instance count as the le0-ancestor form."""
import sys
sys.path.insert(0,'.')
from probe_bmocf_ancestor import enum_depth
from probe_copycrux import sle, shiftr0
from fast_pss import le0, fmt

def arg(N,i):
    lv=N[i][0]; out=[]
    for p in N[i+1:]:
        if p[0]>lv: out.append(p)
        else: break
    return out

def c4(A1,u,e,w):
    for t,x in enumerate(A1):
        if x[0] < u+e and all(y[0] > x[0] for y in A1[t+1:]):
            if x[1] < w: return False
    return True

def run(vmax,ns,ml,rounds):
    hosts=sorted(set(tuple(M) for M in enum_depth(vmax,ns,ml,rounds) if len(M)>=2 and M[0]==(0,0)))
    tot=0;viol=0;exs=[]; mismatch=0
    for N in hosts:
        Nl=list(N);n=len(Nl)
        for i in range(n):
            u,w=Nl[i]; A=arg(Nl,i)
            for t in range(len(A)):
                if A[t][1]!=w: continue
                e=A[t][0]-u
                if e<=0: continue
                j=i+1+t; A1=A[:t]
                cc=c4(A1,u,e,w)
                le=all((not le0(N,k,j)) or Nl[k][1]>=w for k in range(i+1,j))
                if cc!=le: mismatch+=1
                if not cc: continue
                tot+=1
                if not sle(arg(Nl,j), shiftr0(e,A)):
                    viol+=1
                    if len(exs)<3: exs.append((N,i,j))
    print(f" c4  v<={vmax} r={rounds} ml={ml}: instances={tot} VIOL={viol}  (c4 vs le0 mismatches={mismatch})")
    for x in exs: print("   ",fmt(x[0]),x[1],x[2])

run(4,(1,2,3),10,5)
run(5,(1,2,3,4,5),11,7)
run(3,(1,2,3,4,5),14,9)
