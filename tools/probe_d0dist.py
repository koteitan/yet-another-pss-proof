import sys, collections
sys.path.insert(0,'.')
from probe_ascarg_struct import instances
from fast_pss import fmt
c=collections.Counter(); low=collections.Counter(); ex={}
for inst in instances(9,13,5,(1,2,3,4,5)):
    d0=inst['d0']; R=inst['R']; v0=inst['v0']; w0=inst['w0']
    c[d0]+=1
    nlow=len([x for x in R if x[0]<v0+d0])
    low[(d0,nlow)]+=1
    if d0>=2 and (d0,nlow) not in ex: ex[(d0,nlow)]=inst
print("d0 distribution:", dict(sorted(c.items())))
print("(d0, #low cols in R):", dict(sorted(low.items())))
for k,v in sorted(ex.items()):
    print(k, fmt(v['M']), "| v0,w0,d0=",v['v0'],v['w0'],v['d0'],"R=",v['R'])
