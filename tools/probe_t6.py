import sys, collections
sys.path.insert(0,'.')
from probe_ascarg_struct import instances
from fast_pss import fmt
for (rounds,ml,vmax,ns) in [(9,13,5,(1,2,3,4,5)),(8,15,4,(1,2,3,4))]:
    c=collections.Counter(); nontriv=0; bad=0; exs=[]
    for inst in instances(rounds,ml,vmax,ns):
        d0=inst['d0']; R=inst['R']; v0=inst['v0']; w0=inst['w0']
        low=[x for x in R if x[0]<v0+d0]
        c[(w0>=1, d0>=2)]+=1
        if w0>=1 and low:
            nontriv+=1
            if len(exs)<5: exs.append(inst)
            if not all(x[1]>=w0 for x in low): bad+=1
    print(f"rounds={rounds} ml={ml} vmax={vmax}: (w0>=1,d0>=2) counts={dict(c)}  NONTRIVIAL-T6={nontriv} FAIL={bad}")
    for e in exs: print("   ", fmt(e['M']), "v0,w0,d0=",e['v0'],e['w0'],e['d0'],"R=",e['R'])
