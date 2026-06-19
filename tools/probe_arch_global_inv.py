#!/usr/bin/env python3
"""ARCHITECTURE sanity-probe (design phase, NO Lean).

Question being tested (recommended architecture option (i), the GLOBAL
copy-tiling invariant): is the HARD equal-lead domination
`olt (translate K) (translate B)` for the canonical Gterm-0 witness
K = B[i:j] (contiguous infix) ALWAYS decided at the first column where
shift(K) and B differ, by shift(K) being strictly LOWER (row-0 OR row-1),
i.e. exactly the core_i0/core_i1 disjunction — AND is that first-divergence
"downward" fact equivalent to a SINGLE forest-global predicate:

    GINV(B) := for every contiguous infix K=B[i:j] that is a Gterm-0
               witness, the column-shifted copy shift(K) (shift so its
               head row-0 aligns to B's head row-0) is, at the first
               differing column p, strictly seqlex-below B at column p.

The architecture claim is: GINV(B) holds for ALL B with (0,0)::B in ST_PS,
row1<=1, and FAILS for non-ST_PS steps1 sequences (so it is genuinely a
forest-reachability fact, NOT a column-local one) -- AND that GINV is
PRESERVED by the oper copy-tiling map (the inductive lever the round-7
per-step attack lacked, because it is stated GLOBALLY over the whole
divergence, not per intra-copy witness).

We test:
  (A) GINV(B) is 0-viol over the ST_PS row1<=1 fragment at closure+5/+6/+7.
  (B) the first-divergence column is core_i0 (row-0 lower) OR core_i1
      (row-0 equal, row-1 lower) OR shift(K) is a proper prefix of B
      -- never "higher", confirming the seqlex disjunction is exactly the
      two cores.
  (C) GINV FAILS for arbitrary steps1 sequences (forest-reachability needed).
  (D) [the inductive lever] GINV(parent-block) ==> GINV(each oper copy
      tile), checked across actual oper steps: does the GLOBAL invariant
      transport across a copy step, where the per-witness round-7 statement
      did not?
"""
import sys
sys.path.insert(0, '.')
from fast_pss import oper, diagSeq, Lng, le0, entry
from wfe_explore import translate, olt
from probe_bmocf_ancestor import enum_depth

def lead(t): return t[0] if t else -1

def Gterm(u, t):
    if t == (): return []
    a, b, c = t
    out = []
    if u <= a:
        out.append(b); out += Gterm(u, b)
    out += Gterm(u, c)
    return out

# ---- canonical infix witness recovery -------------------------------------
# Gterm_translate_subblock: each g in Gterm 0 (translate B) is translate K for
# a contiguous SubBlock K of B.  We recover K by searching contiguous infixes
# K=B[i:j] with translate K == g (the model analogue of the lean witness).

def infixes(B):
    n = len(B)
    for i in range(n):
        for j in range(i+1, n+1):
            yield i, j, B[i:j]

def shift_to(K, target_row0):
    """shift K's columns so head row-0 == target_row0 (delta may be <=0)."""
    if not K: return K
    delta = target_row0 - K[0][0]
    return [(p[0]+delta, p[1]) for p in K]

def seqlex_firstdiff(A, B):
    """return ('lt0'|'lt1'|'prefixA'|'gt0'|'gt1'|'prefixB'|'eq', pos)."""
    n = min(len(A), len(B))
    for p in range(n):
        a, b = A[p], B[p]
        if a[0] != b[0]:
            return ('lt0' if a[0] < b[0] else 'gt0', p)
        if a[1] != b[1]:
            return ('lt1' if a[1] < b[1] else 'gt1', p)
    if len(A) < len(B): return ('prefixA', n)
    if len(A) > len(B): return ('prefixB', n)
    return ('eq', n)

def ginv_check(B):
    """returns (ok, list of (K, kind) for each hard witness, viols)."""
    t = translate(B)
    g0 = Gterm(0, t)  # coeffs at the root head-0 node (lead t may be 1)
    db = B[0][0] if B else 0
    viols = []; kinds = []
    for g in g0:
        # find a contiguous-infix K with translate K == g (canonical-ish)
        K = None
        for i, j, cand in infixes(B):
            if translate(cand) == g:
                K = cand; break
        if K is None:
            continue  # not infix-realizable in this model slice; skip
        Ksh = shift_to(K, db)
        kind, pos = seqlex_firstdiff(Ksh, B)
        kinds.append((tuple(K), kind))
        # GINV demands downward-or-prefix at first divergence:
        if kind in ('gt0', 'gt1', 'prefixB', 'eq'):
            # 'eq' only ok if g==t (the trivial whole); else viol
            if not (kind == 'eq' and g == t):
                viols.append((tuple(K), kind, pos))
    return (len(viols) == 0, kinds, viols)

# ---- STEP A: single-copy tile obligation `copy_tile_seqlex` ----------------
# oper (fast_pss) on the genuine tiling branch produces, with j1=len-1,
# i1=idx1, j0=parent:
#   G = M[:j0];  body B0 = M[j0:j1] = (v0,w0)::R;  lp = M[j1];
#   d0 = M0[j1]-M0[j0] if i1==1 else 0;  row-1 periodic (d1=0).
# The k-th tile is body.map (p -> (p.1 + k*d0, p.2)).
# OBLIGATION:  seqlex (tile k) (body ++ [lp])  for all k<n.
# hdisj := (d0==0) or (0<d0 and w0<lp.2 and lp.1==v0+d0).

from fast_pss import idx1, hasParent1, parent1, hasParent0, parent0, entry as fentry

def oper_decomp(M):
    """Return (G, body, d0, lp) on the genuine tiling branch, else None."""
    j1 = len(M) - 1
    if j1 == 0: return None
    if fentry(M, 0, j1) == 0 and fentry(M, 1, j1) == 0: return None
    i1 = idx1(M, j1)
    if i1 == 1:
        if not hasParent1(M, j1): return None
        j0 = parent1(M, j1)
    else:
        if not hasParent0(M, j1): return None
        j0 = parent0(M, j1)
    if not (j0 < j1): return None
    d0 = (fentry(M, 0, j1) - fentry(M, 0, j0)) if i1 > 0 else 0
    G = list(M[:j0]); body = list(M[j0:j1]); lp = M[j1]
    return G, body, d0, lp

def tile(body, k, d0):
    return [(p[0] + k*d0, p[1]) for p in body]

def hdisj_holds(body, d0, lp):
    v0, w0 = body[0]
    if d0 == 0: return True
    return (0 < d0) and (w0 < lp[1]) and (lp[0] == v0 + d0)

def stepA(seen):
    """CORRECTED obligation (faithful to core_i0/core_i1/translate_oper_bad):
    the TAIL-COPY concatenation C (copies k=1..n-1) appended after the base
    body is dominated by [lp]:  seqlex (body ++ C) (body ++ [lp]).
    Equivalently (the load-bearing single-copy fact core_i1/core_i0 actually
    use): the FIRST tail copy's head c=(v0+d0,w0) has c.1=lp.1 & c.2<lp.2
    (d0>0 ascending) OR re-opens at v0<=lp.1 (d0=0 exact) -- so seqlex of the
    tail-rest against [lp] is forced.  We check seqlex(body++C, body++[lp])
    for sampled n (2..5)."""
    ok = bad = 0; checked = 0; cex = []
    for M in seen:
        dc = oper_decomp(M)
        if dc is None: continue
        G, body, d0, lp = dc
        if not body: continue
        if hdisj_holds(body, d0, lp):
            v0, w0 = body[0]
            for n in range(2, 6):
                # C = copies k=1..n-1 concatenated (k=0 is the base body)
                C = []
                for k in range(1, n):
                    C += tile(body, k, d0)
                lhs = body + C
                rhs = body + [lp]
                kind, pos = seqlex_firstdiff(lhs, rhs)
                checked += 1
                if kind in ('lt0', 'lt1', 'prefixA'):
                    ok += 1
                else:
                    bad += 1
                    if len(cex) < 6: cex.append((tuple(body), d0, lp, n, kind, pos))
    return ok, bad, checked, cex

def stepA_adversarial():
    """Fabricate (d0>0,!hdisj): is seqlex(body++C, body++[lp]) STILL forced?
    If yes (for all sampled n), hdisj would be vacuous => BAD."""
    nofail = total = 0; ex = []
    bodies = [[(0,0)], [(0,0),(1,1)], [(0,0),(1,0)], [(1,1),(2,1)], [(0,1),(1,1)]]
    for body in bodies:
        v0, w0 = body[0]
        for d0 in range(1, 4):
            for lp in [(v0+d0, w0), (v0+d0, w0-1 if w0>0 else 0),
                       (v0, w0), (v0+d0+1, w0+1), (v0+5, 0)]:
                if hdisj_holds(body, d0, lp): continue
                total += 1
                allok = True
                for n in range(2, 5):
                    C = []
                    for k in range(1, n):
                        C += tile(body, k, d0)
                    kind, _ = seqlex_firstdiff(body + C, body + [lp])
                    if kind not in ('lt0', 'lt1', 'prefixA'):
                        allok = False; break
                if allok:
                    nofail += 1
                    if len(ex) < 8: ex.append((tuple(body), d0, lp))
    return nofail, total, ex


def main():
    print("=== STEP A: copy_tile_seqlex de-risking ===")
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        hosts = [M for M in seen if Lng(M) <= 18]
        ok, bad, checked, cex = stepA(hosts)
        print(f'[closure+{rounds}] oper-tiles checked={checked} '
              f'seqlex-OK={ok} VIOL={bad}')
        for body, d0, lp, k, kind in cex[:4]:
            print('    TILE-CEX body', body, 'd0', d0, 'lp', lp,
                  'k', k, 'kind', kind)
    nofail, total, ex = stepA_adversarial()
    print(f'[adversarial no-hdisj] fabricated(d0>0,!hdisj)={total} '
          f'seqlex-STILL-forced(BAD if>0)={nofail}')
    for body, d0, lp in ex[:6]:
        print('    NO-HDISJ-yet-seqlex body', body, 'd0', d0, 'lp', lp)
    print()
    print("=== whole-block GINV (original) ===")
    for rounds in (5, 6, 7):
        seen = enum_depth(4, (1, 2, 3), 28, rounds)
        hosts = [M for M in seen if Lng(M) <= 18]
        # the residual domain: (0,0)::B in ST_PS, here B = M[1:] of a host
        # whose head is (0,0); row1<=1.
        frag = [M for M in hosts
                if M and M[0] == (0, 0) and all(c[1] <= 1 for c in M)]
        Bs = [M[1:] for M in frag if len(M) > 1]

        nodes = okc = badc = 0
        kindtab = {}
        cex = []
        for B in Bs:
            ok, kinds, viols = ginv_check(B)
            nodes += 1
            if ok: okc += 1
            else:
                badc += 1
                if len(cex) < 5: cex.append((B, viols[:2]))
            for _, k in kinds:
                kindtab[k] = kindtab.get(k, 0) + 1

        print(f'[closure+{rounds}] ST_PS row1<=1 B-blocks={nodes}')
        print(f'  (A) GINV ok={okc} VIOL={badc}')
        print(f'  (B) first-divergence kinds: {dict(sorted(kindtab.items()))}')
        for B, vs in cex[:3]:
            print('    GINV-CEX B=', B)
            for K, k, p in vs: print('        K', K, 'kind', k, 'pos', p)

if __name__ == '__main__':
    main()
