"""Where is ArgDomCore's comparison decided?  And is the head-column sub-lemma
   S1:  B.head.2 <= A.head.2   (levels always agree) always true?"""
import sys, collections
sys.path.insert(0,'.')
from probe_bmocf_ancestor import enum_depth
from probe_copycrux import sle, seqlex, shiftr0
from fast_pss import fmt

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

st=collections.Counter(); exs=[]; s1bad=0; s1n=0
for (vmax,ns,ml,rounds) in [(5,(1,2,3,4,5),11,7),(3,(1,2,3,4,5),14,9)]:
    hosts=sorted(set(tuple(M) for M in enum_depth(vmax,ns,ml,rounds) if len(M)>=2 and M[0]==(0,0)))
    for N in hosts:
        Nl=list(N)
        for i in range(len(Nl)):
            u,w=Nl[i]; A=arg(Nl,i)
            for t in range(len(A)):
                if A[t][1]!=w: continue
                e=A[t][0]-u
                if e<=0: continue
                A1=A[:t]; B=arg(Nl,i+1+t)
                if not c4(A1,u,e,w): continue
                SA=shiftr0(e,A)
                if not B: st['B empty']+=1; continue
                s1n+=1
                if B[0][0]!=SA[0][0]: st['head level differs!']+=1
                if B[0][1] > SA[0][1]:
                    s1bad+=1
                    if len(exs)<3: exs.append((N,i,i+1+t))
                elif B[0][1] < SA[0][1]: st['head row1 strictly less']+=1
                else: st['head equal -> recurse']+=1
                # first difference position
                k=0
                while k<len(B) and k<len(SA) and B[k]==SA[k]: k+=1
                if k>=len(B): st['B is a prefix']+=1
                st[f'decided at depth {min(k,5)}']+=1
    print(f"vmax={vmax}: {dict(st)}  S1-violations={s1bad}/{s1n}")
    for x in exs: print("   ",fmt(x[0]),x[1],x[2])
