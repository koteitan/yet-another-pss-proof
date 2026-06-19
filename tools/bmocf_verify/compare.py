#!/usr/bin/env python3
"""Compare BMOCF native fundamental sequence against bms M[n] expansion over a
corpus of 2-row STANDARD Bashicu-Matrix forms.

Compares TWO implementations against bms ground truth (bms is authoritative):
  - ORIGINAL : advisor's bmocf_fs.fs(t, nat_term(n))         (the buggy version)
  - FIXED    : fs_ref.fs(t, n)                               (the corrected collapse)

Both at the SAME bms index n in {1,2,3}.

Usage:
  python3 compare.py            # full corpus, before/after summary + smallest mismatches
  python3 compare.py -v M       # debug a single form M
"""
import importlib.util, subprocess, sys

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); return m

bm = load("bmocf_fs", "bmocf_fs.py")          # FIXED implementation (this dir)
orig = load("bmocf_fs_orig", "bmocf_fs_orig.py")  # ORIGINAL advisor implementation

BMS = "/home/koteitan/proofs/yaBMS/c/bms"

def is_standard(M):
    return subprocess.run([BMS, "-s", M], capture_output=True, text=True).stdout.strip() == "1"
def bms_expand(M, n):
    return subprocess.run([BMS, f"{M}[{n}]"], capture_output=True, text=True).stdout.strip()
def fmtM(pairs):
    return "".join(f"({a},{b})" for a, b in pairs)

# ---------------- corpus generator ----------------
HARD = [
    "(0,0)(1,1)(2,2)(3,3)(2,2)", "(0,0)(1,1)(2,2)(1,1)(2,2)",
    "(0,0)(1,1)(2,0)(3,1)", "(0,0)(1,1)(2,2)(2,1)(3,2)",
    "(0,0)(1,1)(2,2)(3,3)(2,2)(3,3)", "(0,0)(1,1)(2,2)(3,3)(4,4)(3,3)",
    "(0,0)(1,1)(2,2)(3,1)", "(0,0)(1,1)(2,2)(3,2)", "(0,0)(1,1)(2,1)(3,2)",
    "(0,0)(1,1)(2,2)(3,3)(4,2)", "(0,0)(1,1)(1,1)", "(0,0)(1,1)(2,2)(2,2)",
    "(0,0)(1,1)(2,2)(2,1)", "(0,0)(1,1)(2,2)(2,2)(2,2)", "(0,0)(1,1)(2,1)(2,1)",
    "(0,0)(1,1)(2,2)(3,3)(4,3)", "(0,0)(1,1)(2,2)(2,1)(3,1)",
    "(0,0)(1,1)(2,2)(3,2)(4,3)", "(0,0)(1,1)(2,2)(3,2)(3,1)(4,2)",
    "(0,0)(1,1)(2,2)(2,2)(3,3)", "(0,0)(1,1)(2,2)(3,3)(3,3)",
    "(0,0)(1,1)(2,2)(3,3)(4,4)(5,5)", "(0,0)(1,1)(2,2)(3,2)(3,2)",
    "(0,0)(1,1)(2,2)(3,3)(4,4)(5,3)", "(0,0)(1,1)(2,2)(3,3)(4,2)(4,1)",
]

def gen_candidates(max_len=8, max_sub=4):
    seen = set(); cands = []
    def add(pairs):
        s = fmtM(pairs)
        if s not in seen: seen.add(s); cands.append(pairs)
    # ascension spines
    for L in range(1, max_len):
        for top in range(1, max_sub+1):
            add([(0,0)] + [(i, min(i, top)) for i in range(1, L+1)])
    for s in HARD: add(bm.v.parse(s))
    # brute enumerate small forms
    def rec(prefix, length):
        if length == 0: add(list(prefix)); return
        last = prefix[-1][0]
        for lvl in range(0, last+2):
            for sub in range(0, min(lvl, max_sub)+1):
                rec(prefix + [(lvl, sub)], length-1)
    for L in range(1, 5): rec([(0,0)], L)
    return cands

def standard_corpus():
    S = [fmtM(p) for p in gen_candidates()]
    S = [m for m in S if is_standard(m)]
    return sorted(set(S), key=lambda M: (len(bm.v.parse(M)),
                                         max((b for _, b in bm.v.parse(M)), default=0), M))

# ---------------- comparison ----------------
def eval_form(fn, M):
    """fn(t,n)->term. Return (all_ok, [(n, lhs, rhs, bms_str)...])."""
    t = bm.vterm(M); rows = []; all_ok = True
    for n in (1, 2, 3):
        be = bms_expand(M, n)
        rhs = bm.fmt(bm.vterm(be)) if be else "0"
        try: lhs = bm.fmt(fn(t, n))
        except Exception as e: lhs = f"ERR:{type(e).__name__}:{e}"
        ok = (lhs == rhs)
        all_ok = all_ok and ok
        rows.append((n, lhs, rhs, be, ok))
    return all_ok, rows

ORIG = lambda t, n: orig.fs(t, orig.nat_term(n))   # original advisor fs (buggy)
FIXED = lambda t, n: bm.fs(t, n)                    # fixed fs (this dir's bmocf_fs.py)

def summarize(fn, S, label):
    match = 0; mism = []
    for M in S:
        ok, rows = eval_form(fn, M)
        if ok: match += 1
        else: mism.append((M, rows))
    print(f"{label}: total={len(S)}  match={match}  mismatch={len(mism)}")
    return match, mism

def main():
    if len(sys.argv) >= 3 and sys.argv[1] == "-v":
        M = sys.argv[2]
        print(f"M={M}  standard={is_standard(M)}  v={bm.fmt(bm.vterm(M))}  cof={bm.cof(bm.vterm(M))[1:]}")
        for label, fn in (("ORIG", ORIG), ("FIXED", FIXED)):
            print(f" [{label}]")
            _, rows = eval_form(fn, M)
            for n, lhs, rhs, be, ok in rows:
                print(f"   n={n} {'OK' if ok else 'XX'}  fs={lhs}   bms[{n}]={be}->{rhs}")
        return

    S = standard_corpus()
    lens = [len(bm.v.parse(M)) for M in S]
    subs = [max((b for _, b in bm.v.parse(M)), default=0) for M in S]
    print("=== CORPUS ===")
    print(f"standard forms: {len(S)}")
    print(f"  lengths  : {sorted(set(lens))}  counts {[lens.count(l) for l in sorted(set(lens))]}")
    print(f"  max subs : {sorted(set(subs))}  counts {[subs.count(s) for s in sorted(set(subs))]}")
    print()
    print("=== BEFORE / AFTER (vs bms[n] ground truth) ===")
    mo, _ = summarize(ORIG, S, "ORIGINAL fs")
    mf, mism = summarize(FIXED, S, "FIXED fs")
    print()
    # breakdown by subscript class for FIXED
    fin = [M for M in S if max((b for _, b in bm.v.parse(M)), default=0) == 0]
    ordc = [M for M in S if max((b for _, b in bm.v.parse(M)), default=0) >= 1]
    for lab, sub in (("finite/succ (maxsub=0)", fin), ("ordinal-collapse (maxsub>=1)", ordc)):
        ok = sum(1 for M in sub if eval_form(FIXED, M)[0])
        print(f"  FIXED on {lab}: {ok}/{len(sub)} match")
    print()
    print("=== SMALLEST FIXED-fs mismatches (up to 20 forms) ===")
    for M, rows in mism[:20]:
        for n, lhs, rhs, be, ok in rows:
            if not ok:
                print(f"M={M} n={n}: fs={lhs} | bms={rhs}")

if __name__ == "__main__":
    main()
