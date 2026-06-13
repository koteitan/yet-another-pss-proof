import sys; sys.path.insert(0,'.'); sys.setrecursionlimit(100000)
from wfe_explore import translate
from valnorm import conv, nrm, lt_term, in_OT
import itertools
def blockok(d,B):
    if not B: return True
    if B[0][0]!=d: return False
    if any(p[0]<d for p in B): return False
    return all(B[j+1][0]<=B[j][0]+1 for j in range(len(B)-1))
def seqlex(M,N):
    if not M: return N!=[]
    if not N: return False
    p,q=M[0],N[0]
    if p!=q: return p[0]<q[0] or (p[0]==q[0] and p[1]<q[1])
    return seqlex(M[1:],N[1:])
def olt_via(M,N):  # olt(translate M)(translate N) via lt_term on conv
    return lt_term(conv(translate(M)), conv(translate(N)))
def nrm_olt(M,N):
    return lt_term(nrm(conv(translate(M))), nrm(conv(translate(N))))

# enumerate ALL blockok 0 forms (not just ST_PS) with small bound
cols=[(a,b) for a in range(5) for b in range(3)]
B=[]
for L in range(1,6):
    for M in itertools.product(cols,repeat=L):
        M=list(M)
        if blockok(0,M): B.append(M)
print("blockok 0 forms:",len(B))
import random; rng=random.Random(0)
samp=B if len(B)<700 else rng.sample(B,700)
# Test 1: olt_iff_seqlex on blockok (should hold - proven)
# Test 2: nrm_order_pres on blockok: seqlex M N => nrm_olt M N
tot=0; viol=0; ex=[]
for M in samp:
    for N in samp:
        if M==N: continue
        if seqlex(M,N):
            tot+=1
            if not nrm_olt(M,N):
                viol+=1
                if len(ex)<8: ex.append((M,N))
print(f"nrm_order_pres on BLOCKOK: tested={tot}  VIOL={viol}")
for M,N in ex[:8]:
    fm=lambda X:''.join('(%d,%d)'%(a,b) for a,b in X)
    print("  VIOL M=",fm(M)," N=",fm(N))
