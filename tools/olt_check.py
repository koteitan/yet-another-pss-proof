import itertools, sys
sys.setrecursionlimit(100000)
# ot terms: ('Om',n) | ('Th',n,a) | ('Su',(t,...))   Zero = ('Su',())
def Om(n): return ('Om',n)
def Th(n,a): return ('Th',n,a)
def Su(ts): return ('Su',tuple(ts))
Zero=Su(())
def isH(t): return t[0] in ('Om','Th')
from functools import lru_cache
def Kn(n,a):
    # returns frozenset of ot terms
    if a[0]=='Om':
        m=a[1]; return frozenset({a}) if m<n else frozenset()
    if a[0]=='Th':
        m=a[1]; b=a[2]
        return Kn(n,b) if n<m else frozenset({a})
    if a[0]=='Su':
        s=set()
        for x in a[1]: s|=Kn(n,x)
        return frozenset(s)
def msdiff(xs,ys):
    # multiset xs - ys  (xs,ys tuples). return list
    from collections import Counter
    cx=Counter(xs); cy=Counter(ys)
    res=[]
    for e in cx:
        d=cx[e]-cy.get(e,0)
        if d>0: res+=[e]*d
    return res
@lru_cache(maxsize=None)
def olt(x,y):
    tx,ty=x[0],y[0]
    if tx=='Su' and ty=='Su':
        xs=x[1]; ys=y[1]
        dyx=msdiff(ys,xs); dxy=msdiff(xs,ys)
        return any(all(olt(a,b) for a in dxy) for b in dyx)
    if tx=='Su' and ty=='Om':
        return all(olt(a,y) for a in x[1])
    if tx=='Su' and ty=='Th':
        return all(olt(a,y) for a in x[1])
    if tx=='Om' and ty=='Su':
        return any(olt(x,b) or x==b for b in y[1])
    if tx=='Th' and ty=='Su':
        return any(olt(x,b) or x==b for b in y[1])
    if tx=='Om' and ty=='Om':
        return x[1]<y[1]
    if tx=='Om' and ty=='Th':
        n=y[1]; b=y[2]
        return any(olt(x,g) or x==g for g in Kn(n,b))
    if tx=='Th' and ty=='Om':
        m=x[1]; a=x[2]
        return all(olt(g,y) for g in Kn(m,a))
    if tx=='Th' and ty=='Th':
        m,a=x[1],x[2]; n,b=y[1],y[2]
        c1=any(olt(x,g) or x==g for g in Kn(n,b))
        c2= all(olt(g,y) for g in Kn(m,a)) and (m<n or (m==n and olt(a,b)))
        return c1 or c2
    raise Exception("?")

# generate small ot terms
def gen(depth, subs):
    # subs: range of small subscripts
    terms=set([Zero])
    base=set([Zero])
    for _ in range(depth):
        new=set(base)
        for n in subs:
            new.add(Om(n))
            for a in base:
                new.add(Th(n,a))
        # Su of up to 2 elements from base
        bl=list(base)
        for i in range(len(bl)):
            for j in range(len(bl)):
                new.add(Su([bl[i],bl[j]]))
        base=new
        terms|=new
    return terms

terms=gen(2, range(0,3))
terms=list(terms)
print("num terms:",len(terms))
# search transitivity counterexample
cnt=0; found=0
for a in terms:
    for b in terms:
        if not olt(a,b): continue
        for c in terms:
            if olt(b,c) and not olt(a,c):
                found+=1
                if found<=10:
                    print("CEX: a=",a,"b=",b,"c=",c)
print("transitivity counterexamples:",found)

# wider search + focus Su/Su/Su
terms2=gen(2, range(0,4))
terms2=list(terms2)
print("\nwider num terms:",len(terms2))
sus=[t for t in terms2 if t[0]=='Su']
print("Su terms:",len(sus))
fc=0
for a in sus:
    for b in sus:
        if not olt(a,b): continue
        for c in sus:
            if olt(b,c) and not olt(a,c):
                fc+=1
                if fc<=8: print("Su-CEX:",a,b,c)
print("Su/Su/Su transitivity counterexamples:",fc)
# also test totality failure examples are indeed incomparable but don't break trans
print("Su[u,v] vs Su[v,u] incomparable?:")
u=Th(0,Zero); v=Th(1,Zero)
print("  olt(Su[u,v],Su[v,u])=",olt(Su([u,v]),Su([v,u])), "olt rev=",olt(Su([v,u]),Su([u,v])), "eq=",Su([u,v])==Su([v,u]))
