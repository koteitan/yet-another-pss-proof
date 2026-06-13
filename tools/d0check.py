import sys; sys.path.insert(0,'.'); sys.setrecursionlimit(100000)
from fast_pss import oper, Lng, entry, idx1, hasParent1, parent1, hasParent0, parent0
from wfe_explore import enum_ST
# replicate oper's j0,j1,d0 to classify steps and check snd lp vs block row-1
def step_info(M):
    j1=Lng(M)-1
    if j1==0: return None
    if entry(M,0,j1)==0 and entry(M,1,j1)==0: return None
    i1=idx1(M,j1)
    if i1==1:
        if not hasParent1(M,j1): return None
        j0=parent1(M,j1)
    else:
        if not hasParent0(M,j1): return None
        j0=parent0(M,j1)
    d0=(entry(M,0,j1)-entry(M,0,j0)) if i1>0 else 0
    lp=M[j1]; block=M[j0:j1]   # block = [j0,j1)
    return dict(j0=j0,j1=j1,i1=i1,d0=d0,lp=lp,block=block,w0=M[j0][1])

ST = enum_ST(seed_max_v=4, oper_ns=(1,), max_len=14, rounds=7)  # n=1 just to enumerate hosts
hosts=set(tuple(M) for M in ST)
# also more hosts
ST2=enum_ST(seed_max_v=5, oper_ns=(1,2,3), max_len=14, rounds=7)
hosts|=set(tuple(M) for M in ST2)
print("hosts:",len(hosts))
d0pos=0; d0zero=0
sndlp_strict_max=0; sndlp_not_strict=0; ex=[]
for Mt in hosts:
    M=list(Mt)
    if Lng(M)<2: continue
    info=step_info(M)
    if info is None: continue
    if info['d0']>0:
        d0pos+=1
        blk_r1=[c[1] for c in info['block']]
        if all(r < info['lp'][1] for r in blk_r1):
            sndlp_strict_max+=1
        else:
            sndlp_not_strict+=1
            if len(ex)<8: ex.append((M,info))
    else:
        d0zero+=1
print(f"d0>0 steps: {d0pos}  (d0=0: {d0zero})")
print(f"  d0>0 & all block row-1 < snd lp (subscript-jump works): {sndlp_strict_max}")
print(f"  d0>0 & some block row-1 >= snd lp (jump insufficient): {sndlp_not_strict}")
for M,info in ex[:5]:
    fm=lambda X:''.join('(%d,%d)'%(a,b) for a,b in X)
    print("   NOTSTRICT block=",fm(info['block'])," lp=",info['lp'])
