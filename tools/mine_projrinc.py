#!/usr/bin/env python3
import sys, random
sys.path.insert(0,'.')
from wfe_explore import translate, fmt, enum_ST
from valnorm import conv, nrm, lt_term, fmtb, in_OT
from mine_proj import proj
random.seed(11)

def size(t): return sum(1+size(p[2]) for p in t)

def leaf_inserts(t):
    out=[]
    for w in range(4):
        out.append(t+(('D',w,()),))
    for i,p in enumerate(t):
        _,v,a=p
        for a2 in leaf_inserts(a):
            out.append(t[:i]+(('D',v,a2),)+t[i+1:])
    return out

def leaf_flips(t):
    out=[]
    for i,p in enumerate(t):
        _,v,a=p
        if a==():
            for w in range(v+1,v+3):
                out.append(t[:i]+(('D',w,()),)+t[i+1:])
        else:
            for a2 in leaf_flips(a):
                out.append(t[:i]+(('D',v,a2),)+t[i+1:])
    return out

def classify(x,y):
    """diff-based: y = x + one leaf at z-position -> 'lext';
       y = x with one leaf subscript raised -> 'lflip'; else None."""
    if x==y: return 'eq'
    dx=size(y)-size(x)
    def walk(x,y):
        # return list of diff descriptors
        ds=[]
        n=max(len(x),len(y))
        i=0
        # align from front
        while i<min(len(x),len(y)) and x[i]==y[i]: i+=1
        # try end-aligned for single insertion in list
        if len(y)==len(x)+1 and x[i:]==y[i+1:]:
            p=y[i]
            if p[2]==(): return ds+[('ins',)]
            return ds+[('bad',)]
        if len(x)==len(y):
            if i>=len(x): return ds
            if x[i+1:]!=y[i+1:]: return ds+[('bad',)]
            _,u,a=x[i]; _,v,b=y[i]
            if u==v: return ds+walk(a,b)
            if a==() and b==() and u<v and x[i][2]==() :
                return ds+[('flip',)]
            return ds+[('bad',)]
        return ds+[('bad',)]
    ds=walk(x,y)
    if ds==[('ins',)] and dx==1: return 'lext'
    if ds==[('flip',)] and dx==0: return 'lflip'
    return None

def main():
    ST=enum_ST(seed_max_v=3,oper_ns=(1,2,3),max_len=11,rounds=6)
    base=set()
    def sub(t):
        for p in t:
            _,v,a=p
            base.add(a); sub(a)
    for M in ST:
        w=nrm(conv(translate(M)))
        base.add(w); sub(w)
    base.discard(())
    base=[b for b in base if in_OT(b)]
    base=random.sample(base,min(400,len(base)))
    print('wf3 base:',len(base),flush=True)
    stats={}; ex=[]
    tot=0
    pc={}
    def P(a,t):
        if (a,t) not in pc: pc[(a,t)]=proj(a,t)
        return pc[(a,t)]
    for x in base:
        for x2 in set(leaf_inserts(x)+leaf_flips(x)):
            if not in_OT(x2): continue
            for a in range(3):
                px,px2=P(a,x),P(a,x2)
                tot+=1
                if px==px2: k='EQ'
                else:
                    c=classify(px,px2)
                    if c in ('lext','lflip'): k='RINC'
                    elif lt_term(px,px2): k='OTHER-ord'
                    else: k='REVERSED'
                stats[k]=stats.get(k,0)+1
                if k in ('EQ','OTHER-ord','REVERSED') and len(ex)<6:
                    ex.append((a,x,x2,px,px2,k))
    print('checks:',tot,'stats:',stats)
    for a,x,x2,px,px2,k in ex:
        print(f'{k} a={a}')
        print('  x  =',fmtb(x)[:65]); print('  x2 =',fmtb(x2)[:65])
        print('  px =',fmtb(px)[:65]); print('  px2=',fmtb(px2)[:65])

if __name__=='__main__':
    main()
