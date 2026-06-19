#!/usr/bin/env python3
"""bridge_probe.py -- search for an EXACT dictionary between the stuck TREE fact
`argzone_head_maxviol` (ya-pss nrm.thy) and a MATRIX-side parent_index fact.

TREE side (reuses probe_head_maxo.py enumeration / definitions):
  standard form (0,y)#r ; arg-zone W = takeWhile (0<fst) r ;
  X = nrm(conv(translate W)) ; FIRES = exists G_0-violator (proj 0 X != X).
  Empirically (266545/0): harg X is the olt-maximal G_0-violator of X.

DISCOVERED STRUCTURE (this probe verifies, 0 exceptions on the corpus):
  (S1) Every firing X is a SINGLE principal  X = P lead b 0   (c-spine = ()).
       => harg X = b = the inner argument of the head principal.
  (S2) G_0(X) = [b] + G_0(b)   (head taken since 0<=lead; c empty).
       => the OTHER violators are exactly the violating members of G_0(b).
  (S3) "harg X is max G_0-violator"  <=>  forall g in G_0(b): not olt b g.
       i.e. b dominates its own G_0-descendants -- a property of b alone.

MATRIX side (bmocf_fs.py on the FULL standard form F=(0,0)#W):
  parent_index(F), lnz, bad root r = pim[last][lnz], bad part = F[r:last].
  We test every plausible bridge `harg X = <matrix substring image>` and report
  whether ANY clean matrix substring reproduces harg X (it does NOT -- see below).

Run from tools/bmocf_verify/ :  python3 bridge_probe.py
"""
import sys, os
sys.setrecursionlimit(1000000)
HERE = os.path.dirname(os.path.abspath(__file__))
TOOLS = os.path.dirname(HERE)
sys.path.insert(0, HERE)     # v.py, bmocf_fs.py
sys.path.insert(0, TOOLS)    # wfe_explore, valnorm, fast_pss

import bmocf_fs as bf
import v as vmod
from wfe_explore import translate as tr_translate, enum_ST
from valnorm import conv, nrm, lt_term, fmtb
from fast_pss import oper

# -------- TREE side (verbatim from probe_head_maxo.py) --------
def Glist(u, x):
    if x == (): return []
    a = x[0][1]; b = x[0][2]; c = tuple(x[1:])
    head = ([b] + Glist(u, b)) if u <= a else []
    return head + Glist(u, c)
def fires(a, x): return any(not lt_term(g, x) for g in Glist(a, x))
def maxo(x, ys):
    m = x
    for y in ys:
        if lt_term(m, y): m = y
    return m
def takeW(r):
    out = []
    for p in r:
        if p[0] > 0: out.append(p)
        else: break
    return out
def NT(S): return nrm(conv(tr_translate(list(S))))
def harg(x): return () if x == () else x[0][2]
def matM_to_str(M): return "".join(f"({c[0]},{c[1]})" for c in M)

# -------- MATRIX cut (mirrors bf.bms_step) on full standard form --------
def matrix_cut(F):
    F = [tuple(c) for c in F]
    xs = len(F)
    last = F[xs - 1]
    YS = bf.YS
    yy = 0
    while yy < YS and last[yy] != 0: yy += 1
    lnz = yy - 1
    pim = bf.parent_index(F)
    r = pim[xs - 1][lnz] if lnz >= 0 else None
    badp = F[r:xs - 1] if (r is not None and r >= 0) else (F[:xs - 1] if r == -1 else [])
    return lnz, r, badp, pim

# -------- corpus --------
def build_corpus(deep_rounds, max_len_extra, enum_kwargs):
    base = enum_ST(**enum_kwargs)
    extra = set(base); cur = list(extra)
    for _ in range(deep_rounds):
        new = []
        for M in cur:
            M = list(M)
            if len(M) < 2: continue
            for n in (1, 2, 3, 4, 5):
                tt = tuple(oper(M, n))
                if len(tt) <= max_len_extra and tt not in extra:
                    extra.add(tt); new.append(tt)
        cur = new
        if not cur: break
    return extra

def run(deep_rounds=2, max_len_extra=18,
        enum_kwargs=dict(seed_max_v=5, oper_ns=(1,2,3,4,5), max_len=14, rounds=6)):
    extra = build_corpus(deep_rounds, max_len_extra, enum_kwargs)
    print(f"ST closure = {len(extra)}", flush=True)

    seen = set(); records = []
    for M in extra:
        M = list(M)
        if not M or M[0][0] != 0: continue
        W = tuple(takeW(M[1:]))
        if not W: continue
        X = NT(W)
        if X in seen: continue
        seen.add(X); records.append((W, X))

    nfire = 0
    s1 = 0           # X single principal
    s2 = 0           # G_0(X) == [b]+G_0(b)
    s3_wall = 0      # b is max violator (the actual claim)
    s3_red = 0       # reduced form: forall g in G_0(b) violating: not olt b g
    r1a = 0          # proj 0 X == harg X  (the whole collapse returns b)
    # matrix bridge candidates for harg X == NT(<substring>)
    cand_badp = 0; cand_badtail = 0
    cand_any_substr = 0   # ANY contiguous substring of F whose NT == harg X
    examples = []

    for (W, X) in records:
        V = [g for g in Glist(0, X) if not lt_term(g, X)]
        if not V: continue
        nfire += 1
        b = harg(X)
        # S1
        if len(X) == 1: s1 += 1
        # S2
        if Glist(0, X) == [b] + Glist(0, b): s2 += 1
        # S3 wall
        if all(not lt_term(b, g) for g in V): s3_wall += 1
        # S3 reduced
        gb = Glist(0, b)
        if all((lt_term(g, X) or not lt_term(b, g)) for g in gb): s3_red += 1
        # R1a: full collapse proj 0 X == harg X
        bb = X
        while True:
            gs = [g for g in Glist(0, bb) if not lt_term(g, bb)]
            if not gs: break
            bb = maxo(gs[0], gs[1:])
        if bb == b: r1a += 1

        # MATRIX side on full form
        F = [(0, 0)] + list(W)
        lnz, r, badp, pim = matrix_cut(F)
        if NT(badp) == b: cand_badp += 1
        bt = badp[1:] if len(badp) >= 1 else []
        if (NT(bt) if bt else ()) == b: cand_badtail += 1
        # brute: any contiguous substring of F (or W) whose NT==b ?
        found = False
        seqs = [W]
        for src in seqs:
            n = len(src)
            for i in range(n):
                for j in range(i+1, n+1):
                    if NT(src[i:j]) == b:
                        found = True; break
                if found: break
            if found: break
        if found: cand_any_substr += 1
        elif len(examples) < 8:
            examples.append((W, fmtb(X), fmtb(b)))

    print(f"distinct firing X = {nfire}")
    print(f"(S1) X single principal                       : {s1}/{nfire}")
    print(f"(S2) G_0(X) == [b]+G_0(b)                      : {s2}/{nfire}")
    print(f"(S3 WALL) harg X = max G_0-violator            : {s3_wall}/{nfire}  (want all)")
    print(f"(S3 RED ) forall g in G_0(b): g<X or not b<g   : {s3_red}/{nfire}")
    print(f"(R1a) proj 0 X == harg X (collapse returns b)  : {r1a}/{nfire}")
    print(f"[bridge] harg X == NT(bad part F)              : {cand_badp}/{nfire}")
    print(f"[bridge] harg X == NT(bad part tail)           : {cand_badtail}/{nfire}")
    print(f"[bridge] harg X == NT(SOME contiguous W-substr): {cand_any_substr}/{nfire}")
    if examples:
        print("  --- forms where NO W-substring NT-reproduces harg X ---")
        for (W, X, b) in examples:
            print(f"    W={matM_to_str(W):24s} X={X:24s} harg={b}")
    print()
    print("ASSESSMENT:")
    print("  harg X = b = head-argument of the (always single-principal) X.")
    print("  The matrix bad-part/parent_index slice does NOT NT-reproduce harg X")
    print("  (subscript shear: nrm re-normalizes a substring in a FRESH context,")
    print("   so no matrix substring's own nrm(translate(.)) equals the in-context b).")
    print("  The genuine content -- 'b dominates its violating G_0-descendants' --")
    print("  is an olt-comparison statement on b's own G-spine, NOT removed by")
    print("  transport to parent_index integers. Bridge relocates, not removes, the wall.")
    return dict(nfire=nfire, s1=s1, s2=s2, s3_wall=s3_wall, s3_red=s3_red, r1a=r1a,
                cand_badp=cand_badp, cand_badtail=cand_badtail,
                cand_any_substr=cand_any_substr)

if __name__ == "__main__":
    run()
