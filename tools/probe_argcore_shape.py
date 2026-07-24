"""Does ArgDomCore need REACHABILITY, or only cnf/r1ok/steps1/z0ok?

Candidate local-only counterexample shape (e=1, SpineOK vacuous):
   ... (u,w) (u+1,w) (u+2,w+1) (u+1,w) (u+2,w+1) ...
Here A = the argument of (u,w); its first root (u+1,w) has argument [(u+2,w+1)],
the second root (u+1,w) is the `j` column with B = [(u+2,w+1)];
B = (u+2,w+1) exceeds (shiftr0 1 A).head = (u+2,w).  CNF/r1ok/steps1/z0ok all hold.
Is any such N reachable?
"""
import sys
sys.path.insert(0,'.')
from probe_bmocf_ancestor import enum_depth
from fast_pss import fmt

def arg(N,i):
    lv=N[i][0]; out=[]
    for p in N[i+1:]:
        if p[0]>lv: out.append(p)
        else: break
    return out

def roots(A, lv):
    """indices (within A) of the level-(lv) columns = forest roots of A"""
    out=[]; i=0
    while i < len(A):
        if A[i][0]==lv: out.append(i)
        i+=1
    # only those not nested: a level-lv column is a root iff nothing before it in A has level < lv
    res=[]
    for i in out:
        if all(A[t][0] >= lv for t in range(i)): res.append(i)
    return res

target = ((0,0),(1,1),(2,1),(3,2),(2,1),(3,2))
found=False
hits=0; exs=[]
for (vmax,ns,ml,rounds) in [(5,(1,2,3,4,5),11,7),(3,(1,2,3,4,5),14,9),(4,(1,2,3),16,9)]:
    hosts=sorted(set(tuple(M) for M in enum_depth(vmax,ns,ml,rounds) if len(M)>=2 and M[0]==(0,0)))
    hs=set(hosts)
    if target in hs: found=True
    # search: column (u,w) whose argument has >=2 roots with subscript w, the later with nonempty arg
    for N in hosts:
        Nl=list(N)
        for i in range(len(Nl)):
            u,w=Nl[i]; A=arg(Nl,i)
            rs=[t for t in roots(A,u+1)]
            same=[t for t in rs if A[t][1]==w]
            if len(same)>=2:
                t=same[-1]
                if arg(Nl,i+1+t):
                    hits+=1
                    if len(exs)<5: exs.append((N,i,t))
    print(f"vmax={vmax} r={rounds} ml={ml}: hosts={len(hosts)}  target-reachable={found}  two-same-subscript-roots(2nd nonempty)={hits}")
for e in exs: print("   ",fmt(e[0]),"i=",e[1],"t=",e[2])
