#!/usr/bin/env python3
"""Study the d0=0 (exact-copy, i1=0) value decrease NT(M[n]) <o NT(M).
For small reachable d0=0 bad-branch hosts, print NT(M), NT(M[1]), NT(M[2])
and the first-difference structure, to find the proof pattern."""
import sys
sys.path.insert(0, '.')
from fast_pss import oper
from wfe_explore import enum_ST
from valnorm import lt_term, fmtb
from mine_e6 import NT
from mine_sibm2 import bad_params

def nt(S): return NT(list(S))
def sh(t):
    try: return fmtb(t)
    except: return str(t)
def olt(a,b): return lt_term(a,b)

def main():
    ST = enum_ST(seed_max_v=3, oper_ns=(1,2,3), max_len=11, rounds=6)
    seen=set(); shown=0
    for Mt in sorted(ST, key=lambda x:(len(x),x)):
        if shown>=12: break
        M=list(Mt)
        bp=bad_params(M)
        if bp is None: continue
        j0,j1,i1,d0=bp
        if i1!=0 or d0!=0: continue
        # only show ones with a block of length>=2 (nontrivial copy)
        if j1-j0 < 2: continue
        key=(j0,j1,tuple(M[j0:j1+1]))
        if key in seen: continue
        seen.add(key)
        M1=oper(list(M),1); M2=oper(list(M),2)
        tM=nt(M); t1=nt(M1); t2=nt(M2)
        print('M   =', ''.join('(%d,%d)'%p for p in M), ' j0=%d j1=%d'%(j0,j1))
        print('  block B=[j0,j1) =', ''.join('(%d,%d)'%p for p in M[j0:j1]), ' lp=M[j1]=%s'%(M[j1],))
        print('  NT(M)    =', sh(tM))
        print('  NT(M[1]) =', sh(t1), '  <o NT(M):', olt(t1,tM))
        print('  NT(M[2]) =', sh(t2), '  <o NT(M):', olt(t2,tM), ' NT(M[2])<o NT(M[1]):', olt(t2,t1))
        print()
        shown+=1

if __name__=='__main__':
    main()
