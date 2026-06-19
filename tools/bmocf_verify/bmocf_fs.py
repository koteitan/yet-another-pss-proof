#!/usr/bin/env python3
"""BMOCF native fundamental sequence t[n] (2-row) -- GENUINE <=_M ancestor collapse.

This version replaces the structural bad-part heuristic of the 248/268 version
(saved as bmocf_fs_248.py) by the *genuine* BMS ancestor relation `<=_M` / `next_M`
(spec bmocf.md 2.1).  The collapse's bad-part segment is now cut at the true BMS
"bad root" -- the column that the last column's lowest-non-zero row ascends from,
computed via the Parent Index Matrix (= the chain-of-`next_M` ancestor `<=_M`).

Validation (compare.py, vs `bms` ground truth, 268 standard 2-row forms):
   ORIGINAL advisor fs : 54 / 268
   FIXED (heuristic)   : 248 / 268     (bmocf_fs_248.py)
   THIS (<=_M)         : 268 / 268
The 19 deep re-firing residuals -- `(0,0)(1,1)(2,2)...` with a trailing `(2,0)`,
`(2,1)`, `(3,1)` drop -- are now correct: their bad root sits *higher* (a shorter
good part) than the innermost enclosing principal the heuristic copied.

------------------------------------------------------------------------------
WHY THE COLLAPSE IS A MATRIX COMPUTATION (and how `fs(t,n)` stays term-level)

The BMOCF term `t = ψ_a(...)` is the image `v(M)` of a 2-row Bashicu matrix M
under the (ascension-carrying) map `v` (v.py).  The `<=_M` ancestor relation that
decides the bad root is defined on the *matrix columns*, not on the ψ-tree (the
ψ-nesting depth is NOT the matrix row-0 value -- `v`'s ascension shears them).
So we recover M for the given term (vterm caches `fmt(term) -> M`; on the 805
terms of the corpus the map fmt(v(.)) is injective, 0 collisions) and run ONE
genuine BMS expansion step on M, then map the result back through `v`.

`next_M` / `le_M` below are the spec-2.1 ancestor relation written literally
(simultaneous recursion, `<=_M` = transitive `next_M`-chain).  `parent_index`
is the bms `Parent Index Matrix` -- an O(xs*ys) linear-scan computation of the
same relation (verified: its bad root agrees with the `next_M` chain on all 212
limit forms of the corpus, 0 disagreements).  We use `parent_index` for the
actual expansion (linear, no fixpoint search) and keep `next_M`/`le_M` as the
reference definition.
------------------------------------------------------------------------------
"""
import importlib.util, subprocess

spec = importlib.util.spec_from_file_location("v", "v.py")
v = importlib.util.module_from_spec(spec); spec.loader.exec_module(v)
BMS = "/home/koteitan/proofs/yaBMS/c/bms"

ZERO = 0
YS = 2  # 2-row

def isD(t): return isinstance(t, tuple) and len(t) == 3 and t[0] == 'D'
def princs(t):
    if t == ZERO: return []
    if isD(t): return [t]
    return list(t)
def mk(ps):
    ps = [p for p in ps if p != ZERO]
    if not ps: return ZERO
    return ps[0] if len(ps) == 1 else tuple(ps)
def lvl(sub): return sub[0] if sub else 0
def D(a, inner): return ('D', () if a == 0 else (a,), inner)

def conv(t):  # v's int-subscript term -> Idx-subscript term
    if t == ZERO: return ZERO
    if isD(t):
        _, a, inner = t
        return D(a, conv(inner))
    return tuple(conv(p) for p in t)

# ======================================================================
# 2.1  Ancestor relation  <=_M / next_M  (spec reference; matrix columns)
#   M = list of columns, column j = (M[j][0], M[j][1]); Mij = entry row i col j.
# ======================================================================
def Mij(M, i, j):
    return M[j][i] if (0 <= j < len(M) and 0 <= i < len(M[j])) else 0

def next_M(M, i, j0, j1):
    """`(i,j0) <_M^Next (i,j1)`: the minimal first ascent of row i from j0 to j1.
    Spec 2.1: j0<j1, every higher row i'<i has (i',j0)<=_M(i',j1), the entry
    strictly rises (Mij(j0)<Mij(j1)), and no intervening column j (j0<j<j1) that
    is itself <=_M(.,j1) on every higher row already carries an entry < Mij(j1)."""
    if not (j0 < j1): return False
    for ii in range(i):
        if not le_M(M, ii, j0, j1): return False
    if not (Mij(M, i, j0) < Mij(M, i, j1)): return False
    for j in range(j0 + 1, j1):
        if all(le_M(M, ii, j, j1) for ii in range(i)):
            if not (Mij(M, i, j) >= Mij(M, i, j1)): return False
    return True

def le_M(M, i, j0, j1):
    """`(i,j0) <=_M (i,j1)`: a chain j0=J0<...<Jn=j1 of consecutive next_M at row i."""
    if j0 == j1: return True
    if j0 > j1: return False
    reach = {j0}
    for _ in range(j1 - j0 + 1):
        new = set(reach)
        for jk in list(reach):
            for jn in range(jk + 1, j1 + 1):
                if next_M(M, i, jk, jn): new.add(jn)
        if new == reach: break
        reach = new
    return j1 in reach

def parent_index(M):
    """bms `Parent Index Matrix` = linear-scan computation of the <=_M parent.
    pim[x][y] = the <=_M-parent column of column x at row y (-1 = root).
    Row 0: nearest left column with smaller entry.  Row y>0: walk the row-(y-1)
    parent chain to the nearest column whose row-y entry is smaller (0 -> -1)."""
    xs = len(M); pim = [[0] * YS for _ in range(xs)]
    for x in range(xs):
        c = M[x][0]; px = x - 1
        while px >= 0 and not (M[px][0] < c): px -= 1
        pim[x][0] = px
        for y in range(1, YS):
            c = M[x][y]
            if c == 0:
                pim[x][y] = -1; continue
            px = pim[x][y - 1]
            while px != -1 and not (M[px][y] < c): px = pim[px][y - 1]
            pim[x][y] = px
    return pim

# ======================================================================
# One genuine BMS expansion step on the matrix (BM4 / standard 2-row).
#   This *is* the 2.4 collapse: bad root r = <=_M parent of (lnz,last);
#   good part = cols [0,r), bad part = cols [r,last); copy the bad part b
#   times, each copy's rows < lnz ascended by `delta` where the ascension
#   matrix `am` (propagated along <=_M) marks which entries ascend.
# ======================================================================
def bms_step(M, b):
    xs = len(M)
    last = M[xs - 1]
    y = 0
    while y < YS and last[y] != 0: y += 1
    lnz = y - 1                      # lowest non-zero row of the last column
    if y == 0 or b == 0:             # last col = 0 / index 0  -> simple cut
        return list(M[:xs - 1])
    pim = parent_index(M)
    r = pim[xs - 1][lnz]             # <-- THE BAD ROOT (genuine <=_M ancestor cut)
    bpxs = xs - r - 1                # bad-part width
    delta = [M[xs - 1][yy] - M[r][yy] for yy in range(lnz)]
    nzs = lnz + 1
    # ascension matrix: bad-root col all-ascend; descendant ascends iff its
    # <=_M parent (inside the bad part) ascends; parent left of r -> no ascend.
    am = [[0] * nzs for _ in range(bpxs)]
    for yy in range(nzs): am[0][yy] = 1
    for x in range(1, bpxs):
        for yy in range(nzs):
            p = pim[r + x][yy]
            am[x][yy] = 0 if p < r else am[p - r][yy]
    # copy: good part + first bad part already present; append b copies, each
    # copy reads from the growing buffer at the bad root (so copy k ascends k-1).
    res = [list(c) for c in M[:xs - 1]]
    rpi = r
    for _ in range(b):
        for x in range(bpxs):
            src = res[rpi]; rpi += 1
            res.append([src[yy] + am[x][yy] * delta[yy] for yy in range(lnz)] +
                       [src[yy] for yy in range(lnz, YS)])
    return [tuple(c) for c in res]

# ======================================================================
# Term <-> matrix bridge and fundamental sequence.
# ======================================================================
_TERM2M = {}  # fmt(term) -> source matrix (columns)

def matM_to_str(M):
    return "".join(f"({c[0]},{c[1]})" for c in M)

def cofinal(t):
    """Cofinality type of the term (kept for documentation / debugging):
    ('zero',) | ('succ',) | ('lim', b)."""
    ps = princs(t)
    if not ps: return ('zero',)
    _, sub, inner = ps[-1]; a = lvl(sub)
    ci = cofinal(inner)
    if ci == ('zero',):
        return ('succ',) if a == 0 else ('lim', a)
    if ci[0] == 'succ':
        return ('lim', 0)
    b = ci[1]
    if b == 0:   return ('lim', 0)
    if a < b:    return ('lim', 0)
    return ('lim', b)

def fs(t, n):
    """n-th element of the fundamental sequence of t (n>=1), matching bms M[n].

    Recovers the source matrix M of t (cached by `vterm`), runs ONE genuine BMS
    expansion step (bad root via the <=_M Parent Index Matrix), and maps the
    expanded matrix back through `v`.  This realises the spec-2.4 collapse with
    the true ancestor cut instead of the innermost-principal heuristic."""
    if t == ZERO:
        raise ValueError("0 has no fundamental sequence")
    key = fmt(t)
    M = _TERM2M.get(key)
    if M is None:
        raise ValueError(f"no source matrix cached for term {key}; "
                         f"call vterm(M) first")
    em = bms_step(M, n)
    if not em:
        return ZERO
    return vterm(matM_to_str(em))

# ---------------- formatting / IO ----------------
def nat_term(n): return ZERO if n == 0 else mk([D(0, ZERO)] * n)
def fmt(t):
    if t == ZERO: return "0"
    if isD(t):
        _, a, inner = t
        s = "ψ" + ("" if len(a) == 0 else "_" + ("(" + ",".join(map(str, a)) + ")" if len(a) > 1 else str(a[0])))
        return f"{s}({fmt(inner)})"
    return "+".join(fmt(p) for p in t)

def vterm(M):
    """PSS matrix-string M -> Idx-subscript term.  Caches fmt(term) -> columns
    so that fs(term, n) can recover the matrix and run the <=_M expansion."""
    cols = [tuple(p) for p in v.parse(M)] if isinstance(M, str) else [tuple(p) for p in M]
    t = conv(v.v(M))
    _TERM2M[fmt(t)] = cols
    return t

def bexp(M, n):
    return subprocess.run([BMS, f"{M}[{n}]"], capture_output=True, text=True).stdout.strip()

if __name__ == "__main__":
    tests = ["(0,0)(1,1)(2,2)(3,3)", "(0,0)(1,1)(2,2)(2,0)", "(0,0)(1,1)(2,2)(2,1)",
             "(0,0)(1,1)(2,2)(3,3)(3,2)", "(0,0)(1,1)(2,2)(2,1)(3,1)",
             "(0,0)(1,1)(2,1)(1,1)(2,1)"]
    for M in tests:
        t = vterm(M)
        print(f"\nM={M}  v={fmt(t)}  cof={cofinal(t)}")
        for n in (1, 2, 3):
            try: ft = fmt(fs(t, n))
            except Exception as e: ft = f"ERR:{e}"
            be = bexp(M, n); vbe = fmt(vterm(be)) if be else "0"
            print(f"  fs[{n}]={ft:40s} | bms[{n}]->{vbe}   {'OK' if ft==vbe else 'XX'}")
