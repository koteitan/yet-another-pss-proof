#!/usr/bin/env python3
"""Fast executable model of the pair-sequence system (PSS), 1:1 with the
Isabelle definitions in pss_defs.thy.

Why this exists: empirically test/falsify conjectures BEFORE proving them in
Isabelle (catch sampling artifacts, find counterexamples).  The hot path is
row-0 reachability (`le0`); here it is a bitset (Python big-int mask) transitive
closure, memoized per sequence -- 25x faster at length 8, ~470x at length 24
than red_model.reach (which recomputes O(L^3) on every call).

Representation
--------------
A *pairseq* M is a list of (row0, row1) integer tuples; equivalently a 2-row
Bashicu matrix whose columns are the pairs.  entry(M,i,j) = row i of column j.
le0 is the reflexive-transitive closure of nextrel0, stored as one big-int
bitmask per node: bit b of R[a] is set iff a le0 b.

Reuse note (for the neighbouring ya-pss project, which shares pairseq /
nextrel0/1 / le0 / oper / diagSeq): everything down to `maxent` is GENERAL PSS
infrastructure.  To test a termination MEASURE, append your own
`translate(M) -> measure` and sweep a closure checking it decreases under oper.
"""
from functools import lru_cache

# ---------------------------------------------------------------------------
# Basic accessors
# ---------------------------------------------------------------------------

def Lng(M):
    """Length of the sequence (number of columns)."""
    return len(M)

def entry(M, i, j):
    """Row i (0 or 1) of column j, i.e. M_{i,j}."""
    return M[j][i]

def fmt(M):
    """Pretty-print a pairseq as (a,b)(c,d)... for logs / counterexamples."""
    return "".join(f"({a},{b})" for (a, b) in M)

# ---------------------------------------------------------------------------
# Row-0 reachability le0 -- bitset transitive closure (the hot path)
# ---------------------------------------------------------------------------

@lru_cache(maxsize=None)
def _reach0_masks(M):
    """Row-0 le0 reachability as big-int bitmasks, memoized per sequence.

    M is a TUPLE of pairs (so it is hashable for the cache).  Returns a tuple
    R of length n where bit b of R[a] is set iff a le0 b.  Built by: (1) the
    nextrel0 adjacency, then (2) reflexive closure, then (3) transitive closure
    by repeatedly OR-ing each node's mask with the masks of its set bits until
    a fixpoint.  O(L^3) once; afterwards every le0 query is O(1).
    """
    n = len(M)
    r0 = [p[0] for p in M]
    adj = [0]*n
    for a in range(n):
        e0a = r0[a]
        for b in range(a+1, n):
            e0b = r0[b]
            if e0a < e0b:
                # nextrel0(a,b): strictly increasing row-0, every strictly-between
                # column >= the endpoint row-0 (the row-0 "valley" condition).
                ok = True
                for j in range(a+1, b):
                    if r0[j] < e0b:
                        ok = False; break
                if ok:
                    adj[a] |= (1 << b)
    R = [(1 << i) | adj[i] for i in range(n)]        # reflexive + direct edges
    changed = True
    while changed:                                    # transitive closure
        changed = False
        for i in range(n):
            ri = R[i]; newr = ri; x = ri
            while x:                                   # iterate set bits of ri
                b = (x & -x).bit_length() - 1
                newr |= R[b]
                x &= x - 1
            if newr != ri:
                R[i] = newr; changed = True
    return tuple(R)

def le0(M, a, b):
    """True iff (0,a) <=_M (0,b): a reaches b along row-0 (reflexive-transitive
    closure of nextrel0).  O(1) after the first call on M (cached mask)."""
    n = len(M)
    if not (0 <= a < n and 0 <= b < n): return False
    return bool((_reach0_masks(tuple(M))[a] >> b) & 1)

# ---------------------------------------------------------------------------
# Adjacency relations nextrel0 / nextrel1 (the "Next" edges)
# ---------------------------------------------------------------------------

def nextrel0(M, j0, j1):
    """Row-0 immediate-Next edge (0,j0) <Next (0,j1): j0<j1, row-0 strictly
    increases j0->j1, and every column strictly between has row-0 >= row-0 of
    j1 (so j0 is the immediate row-0 predecessor)."""
    n = Lng(M)
    if not (j0 < n and j1 < n and j0 < j1): return False
    if not (entry(M, 0, j0) < entry(M, 0, j1)): return False
    return all(entry(M, 0, j) >= entry(M, 0, j1) for j in range(j0+1, j1))

def nextrel1(M, j0, j1):
    """Row-1 immediate-Next edge (1,j0) <Next (1,j1): row-1 strictly increases,
    j0 le0 j1 (row-0 reachable), and j0 is row-1-maximal among row-0 ancestors
    of j1 -- every j>j0 with le0(j,j1) has row-1 >= row-1 of j1 (the row-1
    valley/maximality condition)."""
    n = Lng(M)
    if not (j0 < n and j1 < n and j0 < j1): return False
    if not (entry(M, 1, j0) < entry(M, 1, j1)): return False
    if not le0(M, j0, j1): return False
    return all(entry(M, 1, j) >= entry(M, 1, j1) for j in range(j0+1, n) if le0(M, j, j1))

# ---------------------------------------------------------------------------
# Parents (the unique Next-predecessor in a row, when it exists)
# ---------------------------------------------------------------------------

def hasParent1(M, j1):
    """True iff column j1 has a UNIQUE row-1 parent (exactly one nextrel1 edge
    into it).  Mirrors Isabelle hasParent M 1 j1 = (EX! j0. nextR M 1 j0 j1)."""
    return sum(1 for j0 in range(Lng(M)) if nextrel1(M, j0, j1)) == 1

def parent1(M, j1):
    """The row-1 parent of j1 (first/only j0 with nextrel1), or None if none.
    Only meaningful together with hasParent1 (uniqueness)."""
    for j0 in range(Lng(M)):
        if nextrel1(M, j0, j1): return j0
    return None

def hasParent0(M, j1):
    """True iff column j1 has a UNIQUE row-0 parent (exactly one nextrel0 edge)."""
    return sum(1 for j0 in range(Lng(M)) if nextrel0(M, j0, j1)) == 1

def parent0(M, j1):
    """The row-0 parent of j1 (first/only j0 with nextrel0), or None if none."""
    for j0 in range(Lng(M)):
        if nextrel0(M, j0, j1): return j0
    return None

def idx1(M, j1):
    """i1 = max{i in {0,1} | M_{i,j1} > 0}: the top non-zero row of column j1.
    1 if row-1 is positive, else 0.  (Well-defined only when M_{j1} != (0,0).)"""
    return 1 if entry(M, 1, j1) > 0 else 0

def diagSeq(a, b):
    """The diagonal ((j,j))_{j=a..b} -- the ST_PS generators (a<=b)."""
    return [(j, j) for j in range(a, b+1)]

# ---------------------------------------------------------------------------
# Fundamental sequence M[n] (the oper / expansion map)  -- pss_defs.thy 153
# ---------------------------------------------------------------------------

def oper(M, n):
    """M[n], the n-th term of the fundamental sequence (faithful to oper_def).

    Let j1 = Lng M - 1, i1 = idx1.  Degenerate branches return M or Pred M
    (drop last column):
      * j1 == 0                          -> M
      * M_{j1} == (0,0)                  -> Pred M
      * no unique row-i1 parent of j1    -> Pred M
    Otherwise (genuine tiling) with j0 = parent of j1 in row i1:
      M[n] = take j0 M  ++  n copies of the block [j0, j1), the k-th copy
      shifted by (k*d0, k*d1), where d0 = M_{0,j1}-M_{0,j0} when i1>0 else 0,
      and d1 = M_{1,j1}-M_{1,j0} when i1>1 else 0 (so d1 is always 0 since
      i1<=1).  Row-1 of the blocks is therefore PERIODIC; row-0 ramps by d0.
    """
    j1 = Lng(M) - 1
    if j1 == 0: return list(M)
    if entry(M, 0, j1) == 0 and entry(M, 1, j1) == 0:
        return list(M[:-1]) if Lng(M) > 1 else list(M)        # Pred M
    i1 = idx1(M, j1)
    if i1 == 1:
        if not hasParent1(M, j1): return list(M[:-1]) if Lng(M) > 1 else list(M)
        j0 = parent1(M, j1)
    else:
        if not hasParent0(M, j1): return list(M[:-1]) if Lng(M) > 1 else list(M)
        j0 = parent0(M, j1)
    d0 = (entry(M, 0, j1) - entry(M, 0, j0)) if i1 > 0 else 0
    d1 = (entry(M, 1, j1) - entry(M, 1, j0)) if i1 > 1 else 0
    out = list(M[:j0])                                        # the green prefix G
    for k in range(n):                                        # n tiled blocks B_k
        for j in range(j0, j1):
            out.append((entry(M, 0, j) + k*d0, entry(M, 1, j) + k*d1))
    return out

# ---------------------------------------------------------------------------
# Reducedness conditions (RedCondA / RedCondB)  -- pss_defs.thy 422
# ---------------------------------------------------------------------------

def RedCondA(M):
    """Condition (A): every column with a UNIQUE row-i parent differs from that
    parent by exactly +1 in that row (the LOCAL +1 condition, for i in {0,1})."""
    n = Lng(M)
    for j in range(n):
        if hasParent0(M, j) and entry(M, 0, parent0(M, j)) + 1 != entry(M, 0, j): return False
        if hasParent1(M, j) and entry(M, 1, parent1(M, j)) + 1 != entry(M, 1, j): return False
    return True

def RedCondB(M):
    """Condition (B): every column WITHOUT a unique row-0 parent has its two
    rows equal (M_{0,j} = M_{1,j})."""
    n = Lng(M)
    for j in range(n):
        if (not hasParent0(M, j)) and entry(M, 0, j) != entry(M, 1, j): return False
    return True

def reduced(M):
    """M is reduced iff RedCondA and RedCondB.  By the proven m_6_6 keystone
    this coincides with Red M = M (membership in RT_PS), so it is the fast
    stand-in for reducedness (no need to run the recursive Red)."""
    return RedCondA(M) and RedCondB(M)

# ---------------------------------------------------------------------------
# Enumeration helpers (for empirical sweeps)
# ---------------------------------------------------------------------------

def maxent(M):
    """Largest entry appearing in M (used to bound closures / enumerations)."""
    return max((max(a, b) for (a, b) in M), default=0)

def enum_reduced_tiling(maxlen, maxe):
    """Brute-force enumerate all reduced, tiling-branch (i1=1, unique row-1
    parent of the last column) sequences with length <= maxlen and entries
    <= maxe.  Cost is (maxe+1)^(2L) per length L, so practical only up to
    maxlen ~5; for more reach, generate the ST_PS closure by BFS under `oper`
    from `diagSeq` seeds instead (cheap thanks to the cached le0)."""
    import itertools
    cols = [(a, b) for a in range(maxe+1) for b in range(maxe+1)]
    out = []
    for L in range(2, maxlen+1):
        for M in itertools.product(cols, repeat=L):
            M = list(M)
            j1 = L-1
            if entry(M, 0, j1) == 0 and entry(M, 1, j1) == 0: continue
            if idx1(M, j1) != 1: continue
            if not hasParent1(M, j1): continue
            if not (parent1(M, j1) < j1): continue
            if reduced(M):
                out.append(M)
    return out
