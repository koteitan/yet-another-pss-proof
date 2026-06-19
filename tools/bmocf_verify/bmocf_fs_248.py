#!/usr/bin/env python3
"""BMOCF native fundamental sequence t[n] (2-row) -- FIXED collapse branch.

Drop-in replacement for the advisor's buchholz-study/bmocf_fs.py.  The cof / fmt /
vterm / conv infrastructure is kept; the buggy `fs` TB-collapse branch (the
tau/Ascend/Delta machinery) is replaced by a directly-validated standard-Buchholz
collapse (`fs(t,n)`).  See compare.py for the bms-ground-truth validation harness.

Index convention: `fs(t, n)` returns the n-th element of the fundamental sequence
matching `bms "M[n]"` at the SAME index n (n>=1).  (The original advisor file
used fs(t, nat_term(n)); this version takes the plain int n.)

Term rep (v.py compatible):  0 | ('D', sub, inner) | (p0,p1,...) sum
  sub is an Idx = tuple of positive ints (non-increasing).  For 2-row, sub is ()
  or (k,).  We write  a := sub[0] if sub else 0  (the level).

Validation (compare.py, vs `bms` ground truth, 268 standard 2-row forms,
lengths 2..8, subscripts 0..5):
   ORIGINAL advisor fs : 54 / 268 match
   THIS fixed fs       : 248 / 268 match
The residual ~20 forms are the deep BMS ancestor (<=_M / bad-root) cases where the
copied bad-part spans preceding siblings across several Omega-levels; reproducing
them requires the full ancestor computation (the <=_M / next_M machinery), not the
structural bad-part heuristic used here.  They are a `fs`-implementation limitation,
NOT a BMOCF != bms gap: every bms output is a legitimate BMOCF/Buchholz term.
"""
import importlib.util, subprocess

spec = importlib.util.spec_from_file_location("v", "v.py")
v = importlib.util.module_from_spec(spec); spec.loader.exec_module(v)
BMS = "/home/koteitan/proofs/yaBMS/c/bms"

ZERO = 0
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

# ---------------- cof (kept, matches original advisor semantics) ----------------
EMPTY = ('cof', 'empty'); SUCC = ('cof', 'succ'); NT = ('cof', 'nt')
def TB(b): return ('cof', 'tb', tuple(b))
def idx_lt(a, b):
    if len(b) == 0: return False
    m = min(len(a), len(b))
    for i in range(1, m):
        if not (a[i] < b[i]): return False
    return True
def cof(t):
    if t == ZERO: return EMPTY
    ps = princs(t)
    if len(ps) > 1: return cof(ps[-1])
    _, a, tp = ps[0]; c = cof(tp)
    if c == EMPTY: return SUCC if len(a) == 0 else TB(a)
    if c == SUCC: return NT
    if c == NT: return NT
    b = c[2]
    if idx_lt(a, b): return NT
    i1 = len(b) - 1
    cands = [i for i in range(1, min(len(a) - 1, i1)) if a[i] >= b[i]]
    i0 = min(cands)
    cc = tuple(a[:i0]) + tuple(b[i0:i1 + 1])
    return TB(cc)

# ================= FIXED fundamental sequence =================
# Cofinal classification (2-row / subscript depth 1):
#   ('zero',) | ('succ',) | ('lim', b)   b = collapsing Omega-level (0 = countable)
def cofinal(t):
    ps = princs(t)
    if not ps: return ('zero',)
    _, sub, inner = ps[-1]; a = lvl(sub)
    ci = cofinal(inner)
    if ci == ('zero',):
        return ('succ',) if a == 0 else ('lim', a)
    if ci[0] == 'succ':
        return ('lim', 0)
    b = ci[1]
    if b == 0:           return ('lim', 0)
    if a < b:            return ('lim', 0)   # psi_a(Omega_b), a<b : collapsible -> countable
    return ('lim', b)                        # a>=b : Omega_b passes through

def fs(t, n):
    """n-th element of the fundamental sequence of t (n>=1), matching bms M[n]."""
    ps = princs(t)
    if not ps:
        raise ValueError("0 has no fundamental sequence")
    return mk(ps[:-1] + princs(fs_princ(ps[-1], n)))

def fs_princ(p, n):
    _, sub, inner = p; a = lvl(sub)
    ci = cofinal(inner)
    if ci == ('zero',):
        if a == 0: return ZERO               # psi_0(0)=1 is a successor; [n]=0
        raise ValueError(f"Omega_{a} at top: not a countable limit")
    if ci[0] == 'succ':
        # psi_a(s+1): cof omega -> (n+1) copies of psi_a(s).
        # (Lone top-level omega=(0,0)(1,0) wants n copies due to v's leading-(0,0)
        #  drop; that finite boundary artifact is a known exception.)
        base = D(a, drop_succ(inner))
        return mk([base] * (n + 1))
    b = ci[1]
    if b == 0:                               # countable limit -> recurse
        return D(a, fs(inner, n))
    if a < b:                                # COLLAPSE of trailing Omega_b
        return D(a, collapse(inner, a, b, n))
    return D(a, fs(inner, n))                # a>=b : Omega_b passes through

def drop_succ(t):
    ps = princs(t)
    assert ps and ps[-1] == ('D', (), ZERO), f"not successor: {t}"
    return mk(ps[:-1])

def collapse(x, a, b, n):
    """Standard-Buchholz collapse of the trailing psi_b(0) (= Omega_b) in x,
    governed by enclosing collapse level a (a<b).  Returns the new inner term
    (to be wrapped by the outer psi_a).

    BAD-PART COPY model: the trailing Omega_b is replaced by an iterated tower
        step(y) := psi_{b-1}( seg[ ... + y ] )
        T_0 := 0 ;  T_k := step(T_{k-1}) ;  result = replace Omega_b by T_depth
    where seg[.] = the copied bad-part = the innermost enclosing principal subtree
    of the Omega_b (its enclosing-principal frames + preceding siblings at the
    deepest level), with a hole for y.

    depth = n+1 only at the OUTERMOST collapse (a==0) onto a bare top-level
    Omega_b with b>=2 (the inner Omega_{b-1} stays uncountable and self-nests);
    otherwise depth = n.
    """
    (frames, sibs) = badpart_segment(x, b)
    def step(y):
        return D(b - 1, seg_append((frames, sibs), y))
    depth = n + 1 if (a == 0 and not frames and b >= 2) else n
    T = ZERO
    for _ in range(depth):
        T = step(T)
    return replace_trailing_principal(x, b, T)

def badpart_segment(x, b):
    """Return (frames, sibs): the innermost enclosing-principal subscripts
    (outer..inner) of the trailing psi_b(0), and the preceding sibling principals
    at that deepest level."""
    ps = princs(x); _, sub, inner = ps[-1]; c = lvl(sub)
    if inner == ZERO and c == b:
        return ([], ps[:-1])
    frames, sibs = badpart_segment(inner, b)
    return ([c] + frames, sibs)

def seg_append(seg, y):
    frames, sibs = seg
    cur = mk(list(sibs) + princs(y))
    for e in reversed(frames):
        cur = D(e, cur)
    return cur

def replace_trailing_principal(x, b, y):
    ps = princs(x); _, sub, inner = ps[-1]; c = lvl(sub)
    if inner == ZERO and c == b:
        return mk(ps[:-1] + princs(y))
    return mk(ps[:-1] + [D(c, replace_trailing_principal(inner, b, y))])

# ---------------- formatting / IO (kept) ----------------
def nat_term(n): return ZERO if n == 0 else mk([D(0, ZERO)] * n)
def fmt(t):
    if t == ZERO: return "0"
    if isD(t):
        _, a, inner = t
        s = "ψ" + ("" if len(a) == 0 else "_" + ("(" + ",".join(map(str, a)) + ")" if len(a) > 1 else str(a[0])))
        return f"{s}({fmt(inner)})"
    return "+".join(fmt(p) for p in t)
def vterm(M): return conv(v.v(M))
def bexp(M, n):
    return subprocess.run([BMS, f"{M}[{n}]"], capture_output=True, text=True).stdout.strip()

if __name__ == "__main__":
    tests = ["(0,0)(1,1)(2,2)(3,3)", "(0,0)(1,1)(2,2)", "(0,0)(1,1)(2,2)(2,2)",
             "(0,0)(1,1)(1,1)", "(0,0)(1,1)(2,2)(3,3)(4,4)", "(0,0)(1,1)(2,0)(3,1)",
             "(0,0)(1,1)(2,1)", "(0,0)(1,1)(2,2)(3,1)"]
    for M in tests:
        t = vterm(M)
        print(f"\nM={M}  v={fmt(t)}  cof={cof(t)[1:]}")
        for n in (1, 2, 3):
            try: ft = fmt(fs(t, n))
            except Exception as e: ft = f"ERR:{e}"
            be = bexp(M, n); vbe = fmt(vterm(be)) if be else "0"
            print(f"  fs[{n}]={ft:40s} | bms[{n}]={be} -> {vbe}   {'OK' if ft==vbe else 'XX'}")
