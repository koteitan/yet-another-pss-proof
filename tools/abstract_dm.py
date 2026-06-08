from collections import Counter
# abstract base order given as set of pairs (strict)
def make_olt(less):
    def olt(a,b): return (a,b) in less
    return olt
def msdiff(xs,ys):
    cx=Counter(xs); cy=Counter(ys); res=[]
    for e in cx:
        d=cx[e]-cy.get(e,0)
        if d>0: res+=[e]*d
    return res
def sdm(xs,ys,olt):  # single-dominator one-step DM
    dyx=msdiff(ys,xs); dxy=msdiff(xs,ys)
    return any(all(olt(a,b) for a in dxy) for b in dyx)

# my counterexample base: a1<b1, a2<b2, else incomparable
less={('a1','b1'),('a2','b2')}
olt=make_olt(less)
# check transitive & asym
elems=['a1','a2','b1','b2']
trans_ok=all((not(olt(x,y) and olt(y,z))) or olt(x,z) for x in elems for y in elems for z in elems)
asym_ok=all(not(olt(x,y) and olt(y,x)) for x in elems for y in elems)
print("base transitive:",trans_ok,"asym:",asym_ok)
A=('a1','a2'); B=('a2','b1'); C=('b1','b2')
print("sdm A B:",sdm(A,B,olt))
print("sdm B C:",sdm(B,C,olt))
print("sdm A C:",sdm(A,C,olt))
print("=> single-dominator DM transitive here?", (not(sdm(A,B,olt) and sdm(B,C,olt))) or sdm(A,C,olt))
