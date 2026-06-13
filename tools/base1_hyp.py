import sys; sys.path.insert(0,'.'); sys.setrecursionlimit(100000)
from wfe_explore import translate, enum_ST
from valnorm import conv, in_OT
from fast_pss import oper, reduced
# is (0,0)(1,0)(2,1) reduced? in ST_PS closure?
cex=[(0,0),(1,0),(2,1)]
print("cex=(0,0)(1,0)(2,1): reduced?", reduced(cex), " translate wf3?", in_OT(conv(translate(cex))))
# blockok 0?
def blockok(d,B):
    if not B: return True
    if B[0][0]!=d: return False
    if any(p[0]<d for p in B): return False
    return all(B[j+1][0]<=B[j][0]+1 for j in range(len(B)-1))
print("cex blockok 0?", blockok(0,cex))

ST = enum_ST(seed_max_v=5, oper_ns=(1,2,3,4,5), max_len=14, rounds=8)
STset=set(tuple(M) for M in ST)
print("cex in ST_PS closure?", tuple(cex) in STset)

# Test: does "blockok 0 ∧ maxr1<=1 ⟹ wf3(translate)" hold for reduced (not nec ST_PS) forms?
from fast_pss import enum_reduced_tiling
def maxr1(M): return max((p[1] for p in M),default=0)
bad_blockok=0; bad_ST=0; n_blockok=0; n_ST=0
# enumerate small reduced forms with maxr1<=1
import itertools
cols=[(a,b) for a in range(6) for b in range(2)]  # row-1 in {0,1}
exs=[]
for L in range(1,6):
    for M in itertools.product(cols,repeat=L):
        M=list(M)
        if not blockok(0,M): continue
        if maxr1(M)>1: continue
        if not reduced(M): continue
        n_blockok+=1
        if not in_OT(conv(translate(M))):
            bad_blockok+=1
            if len(exs)<8: exs.append(M)
print(f"reduced+blockok0+maxr1<=1 forms: {n_blockok}, translate-NOT-wf3: {bad_blockok}")
for M in exs[:8]:
    print("  notwf3:",''.join('(%d,%d)'%(a,b) for a,b in M), " inST?", tuple(M) in STset)
