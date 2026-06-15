#!/usr/bin/env python3
"""Does the seqlex first-difference drive olt(proj0 b)(proj0 f) in equal-maxsub?

Setup: b,f firing head-0 NF args, olt b f, maxsub b = maxsub f = k.
proj0 b = chainAt b k = leading .b-chain node at lead k (verified prior 1285/1285).

We want to test whether olt_ST_iff_seqlex is the missing GLOBAL handle:
  - b,f = translate Mb, translate Mf for ST_PS Mb,Mf (the args of head-0 NF).
    BUT b,f are ARGS (the .b of P 0 b c) — are THEY themselves translates of ST_PS?
    Need: is b in NF (= translate of some ST_PS)?  Check.
  - If b = translate Mb, olt b f <-> seqlex Mb Mf (first column-difference).
  - Does the seqlex first-difference column correspond to the spine position
    where proj0 b / proj0 f differ?

KEY questions:
  Q1: are the head-0 NF args b themselves in NF (translate ST_PS)?  (so seqlex applies)
  Q2: relationship proj0 b vs the seqlex structure of b's preimage.
  Q3: in equal-maxsub, does seqlex first-diff column j determine olt(proj0 b)(proj0 f)?

Since b,f may not be directly ST_PS-translates, test the cleaner thing:
  the WHOLE terms B0 = P 0 b c, F0 = P 0 f g ARE in NF (= translate ST_PS).
  proj0 acts on the arg b.  olt B0 F0 <-> seqlex Mb0 Mf0.
We test whether the proj-comparison is governed by seqlex on the full preimages.
"""
import sys
sys.path.insert(0, '.')
from wfe_explore import translate, enum_ST, olt, maxsub, spine
Z = ()
def lead(t): return 0 if t==Z else t[0]
def Gterm(u, t):
    if t == Z: return []
    a, b, c = t; out = []
    if u <= a: out.append(b); out += Gterm(u, b)
    out += Gterm(u, c); return out
def pfire(u, b): return any(not olt(g, b) for g in Gterm(u, b))
def proj(u, b):
    while True:
        bad = [g for g in Gterm(u, b) if not olt(g, b)]
        if not bad: return b
        m = bad[0]
        for h in bad[1:]:
            if olt(m, h): m = h
        b = m
def chainAt(t, k):
    cur = t
    while cur != Z:
        if lead(cur) == k: return cur
        cur = cur[1]
    return None

# seqlex on pair sequences (matches Lean def)
def pairlt(p, q):
    return p[0] < q[0] or (p[0]==q[0] and p[1] < q[1])
def seqlex(M, N):
    if not M: return len(N) > 0
    if not N: return False
    p, q = M[0], N[0]
    if pairlt(p, q): return True
    if p == q: return seqlex(M[1:], N[1:])
    return False
def seqlex_firstdiff(M, N):
    i = 0
    while i < len(M) and i < len(N) and M[i] == N[i]:
        i += 1
    return i

def main():
    ST = enum_ST(seed_max_v=4, oper_ns=(1,2,3,4), max_len=14, rounds=8)
    # keep ST preimages so we can use seqlex
    ST = [tuple(M) for M in ST]
    NFmap = {}   # translate(M) -> M  (one preimage)
    for M in ST:
        t = translate(list(M))
        NFmap.setdefault(t, M)
    NF = sorted(NFmap.keys(), key=str)
    # head-0 NF args b with their FULL term and preimage
    # full term B0 = P 0 b c in NF; b = B0[1]
    fullfire = []   # (B0, Mb0)  where B0 fires at its arg
    for B0 in NF:
        if B0 == Z or B0[0] != 0: continue
        b = B0[1]
        if pfire(0, b):
            fullfire.append((B0, NFmap[B0]))
    print(f"head-0 NF terms with firing arg: {len(fullfire)}")

    # Q3: equal-maxsub pairs; does seqlex first-diff on full preimages drive
    # olt(proj0 b)(proj0 f)?  Specifically: the column j of first difference,
    # and whether proj0 b,f differ 'because of' column j.
    # Simpler verifiable claim S: olt(proj0 b)(proj0 f) <-> seqlex Mb0 Mf0
    #   (the WHOLE-term seqlex order is preserved by proj0-of-arg).
    S_ok = S_tot = 0
    for (B0, Mb0) in fullfire:
        b = B0[1]; pb = proj(0, b)
        for (F0, Mf0) in fullfire:
            f = F0[1]
            if not olt(B0, F0): continue
            if maxsub(b) != maxsub(f): continue
            S_tot += 1
            sl = seqlex(list(Mb0), list(Mf0))   # = olt B0 F0 (should be True)
            pj = olt(pb, proj(0, f))
            if sl == pj: S_ok += 1
    print(f"S: olt(proj0 b)(proj0 f) <-> seqlex(Mb0,Mf0) [eqmaxsub]: {S_ok}/{S_tot}")

    # Also: olt B0 F0 already <-> seqlex; so really testing pj == True for all.
    # Confirm pj True for all eqmaxsub (the residual itself).
    pj_true = pj_tot = 0
    for (B0, Mb0) in fullfire:
        b=B0[1]; pb=proj(0,b)
        for (F0,Mf0) in fullfire:
            f=F0[1]
            if not olt(B0,F0) or maxsub(b)!=maxsub(f): continue
            pj_tot+=1
            if olt(pb,proj(0,f)): pj_true+=1
    print(f"residual olt(proj0 b)(proj0 f) eqmaxsub: {pj_true}/{pj_tot}")

if __name__ == '__main__':
    main()
