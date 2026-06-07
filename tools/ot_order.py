#!/usr/bin/env python3
"""Python port of the absolute Towsner ordinal notation `ot` (wo.thy Def 2.2/2.3/2.4),
to experiment with the well-foundedness construction (ground, shift, normalization)
before formalizing in Isabelle.

Terms (match wo.thy):
  ('Om', n)        Omega_n            (n int)
  ('Th', n, a)     theta_n a          (n int)
  ('Su', [a0,...]) natural sum #{...} (Su [] = Zero)
"""
import sys, functools
sys.setrecursionlimit(100000)

def Om(n): return ('Om', n)
def Th(n,a): return ('Th', n, a)
def Su(xs): return ('Su', tuple(xs))
Zero = Su([])

def isH(t): return t[0] in ('Om','Th')

def FCset(t):
    if t[0]=='Om': return {t[1]}
    if t[0]=='Th':
        n=t[1]; return {m for m in FCset(t[2]) if m<n}
    return set().union(*[FCset(x) for x in t[1]]) if t[1] else set()

def FC(t):
    s=FCset(t)
    return max(s) if s else None   # None = -infinity (countable)

def G(t):
    s=FCset(t)
    return min(s) if s else None   # None = -infinity

def Kn(n,t):
    if t[0]=='Om':
        m=t[1]; return frozenset({Om(m)}) if m<n else frozenset()
    if t[0]=='Th':
        m=t[1]
        return Kn(n,t[2]) if n<m else frozenset({t})
    return frozenset().union(*[Kn(n,x) for x in t[1]]) if t[1] else frozenset()

@functools.lru_cache(maxsize=None)
def olt(a,b):
    """a <_o b  (Def 2.3, absolute)."""
    ta,tb=a[0],b[0]
    if ta=='Su' and tb=='Su':
        xs=list(a[1]); ys=list(b[1])
        # multiset difference
        from collections import Counter
        cx=Counter(xs); cy=Counter(ys)
        ys_x = list((cy-cx).elements())   # ys - xs
        xs_y = list((cx-cy).elements())   # xs - ys
        return any(all(olt(aa,b0) for aa in xs_y) for b0 in ys_x)
    if ta=='Su' and tb in ('Om','Th'):
        return all(olt(x,b) for x in a[1])
    if ta in ('Om','Th') and tb=='Su':
        return any(olt(a,y) or a==y for y in b[1])
    if ta=='Om' and tb=='Om':
        return a[1]<b[1]
    if ta=='Om' and tb=='Th':
        n=b[1]; return any(olt(a,g) or a==g for g in Kn(n,b[2]))
    if ta=='Th' and tb=='Om':
        m=a[1]; return all(olt(g,b) for g in Kn(m,a[2]))
    if ta=='Th' and tb=='Th':
        m=a[1]; ca=a[2]; n=b[1]; cb=b[2]
        d1 = any(olt(a,g) or a==g for g in Kn(n,cb))
        d2 = all(olt(g,b) for g in Kn(m,ca)) and (m<n or (m==n and olt(ca,cb)))
        return d1 or d2
    raise ValueError((a,b))

def ole(a,b): return a==b or olt(a,b)

# ---- shift: add k to every FREE Omega index (and theta subscript) below cutoff ----
def shift(t,k):
    """upshift/downshift ALL Om indices and Th subscripts by k (no cutoff;
    naive global shift). For experimenting."""
    if t[0]=='Om': return Om(t[1]+k)
    if t[0]=='Th': return Th(t[1]+k, shift(t[2],k))
    return Su([shift(x,k) for x in t[1]])

def normground(t):
    """ground-normalize: shift so min FCset = 0 (countable terms unchanged)."""
    g=G(t)
    return t if g is None else shift(t,-g)

def normtop(t):
    """top-normalize (Towsner alpha*): shift so max FCset = 0."""
    f=FC(t)
    return t if f is None else shift(t,-f)

def sz(t):
    if t[0]=='Om': return 1
    if t[0]=='Th': return 1+sz(t[2])
    return 1+sum(sz(x) for x in t[1])

if __name__=='__main__':
    # the counterexample from memo
    a = Th(6, Om(6))             # Th s d, s=6, d=Om6
    r = Th(5, Th(100, Om(9)))    # p<s predecessor
    print("FCset a", FCset(a), "FC", FC(a), "G", G(a))
    print("FCset r", FCset(r), "FC", FC(r), "G", G(r))
    print("r <o a :", olt(r,a))
    print("Kn 5 (Th100 Om9):", Kn(5, Th(100,Om(9))))
    print("Kn 6 (Om6):", Kn(6, Om(6)))
