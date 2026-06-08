#!/usr/bin/env python3
"""Empirically test the op_NF obligation (embed.thy):
   for w,x in NF = translate`ST_PS,  w <o x (three order)  ==>  embed w <_o embed x (ot order).

Generates ST_PS by BFS from diagSeq(0,v) applying oper(.,n), translates to `three`,
embeds to `ot`, and checks order-preservation on all comparable pairs.
"""
import sys, itertools
sys.path.insert(0, '.')
from fast_pss import diagSeq, oper, Lng
import ot_order as ot

# ---- three datatype: ('Z',) | ('P', a, b, c) ----
def Z(): return ('Z',)
def P(a,b,c): return ('P', a, b, c)

def translate(M):
    """faithful to mechanized.thy translate."""
    M = list(M)
    if not M: return Z()
    p = M[0]; rest = M[1:]
    # takeWhile / dropWhile (fst p < fst q)
    i = 0
    while i < len(rest) and p[0] < rest[i][0]:
        i += 1
    inside = rest[:i]; after = rest[i:]
    return P(p[1], translate(inside), translate(after))

# ---- three order olt (subscript-first lexicographic) ----
def tolt(x,y):
    if x[0]=='Z' and y[0]=='Z': return False
    if x[0]=='Z' and y[0]=='P': return True
    if x[0]=='P' and y[0]=='Z': return False
    _,a,b,c = x; _,e,f,g = y
    return a<e or (a==e and tolt(b,f)) or (a==e and b==f and tolt(c,g))

# ---- embed: three -> ot ----
def collapse(xs):
    if len(xs)==0: return ot.Su([])
    if len(xs)==1: return xs[0]
    return ot.Su(xs)

def eprincs(t):
    if t[0]=='Z': return []
    _,a,b,c = t
    return [ot.Th(a, embed(b))] + eprincs(c)

def embed(t):
    return collapse(eprincs(t))

# ---- generate ST_PS ----
def gen_ST_PS(vmax=3, depth=4, nmax=3, cap=4000):
    seen = set()
    frontier = []
    for v in range(0, vmax+1):
        M = tuple(diagSeq(0, v))
        if M not in seen:
            seen.add(M); frontier.append(M)
    allM = set(seen)
    for _ in range(depth):
        nxt = []
        for M in frontier:
            if Lng(M) <= 1: continue
            for n in range(1, nmax+1):
                M2 = tuple(oper(list(M), n))
                if M2 and M2 not in allM:
                    allM.add(M2); nxt.append(M2)
                    if len(allM) >= cap: break
            if len(allM) >= cap: break
        frontier = nxt
        if len(allM) >= cap: break
    return list(allM)

def main():
    Ms = gen_ST_PS()
    print(f"generated {len(Ms)} ST_PS members")
    trs = [translate(M) for M in Ms]
    # dedup by three-term
    uniq = list({repr(t): t for t in trs}.values())
    print(f"{len(uniq)} distinct NF three-terms")
    fails = 0; checked = 0
    for w, x in itertools.permutations(uniq, 2):
        if tolt(w, x):
            checked += 1
            ew, ex = embed(w), embed(x)
            if not ot.olt(ew, ex):
                fails += 1
                if fails <= 10:
                    print("FAIL:")
                    print("  w =", w)
                    print("  x =", x)
                    print("  embed w =", ew)
                    print("  embed x =", ex)
    print(f"checked {checked} comparable pairs, {fails} failures")

if __name__=='__main__':
    main()
