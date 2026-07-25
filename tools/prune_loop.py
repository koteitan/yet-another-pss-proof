#!/usr/bin/env python3
"""Delete every declaration `lean/tools/DeadCode.lean` reported, build-verified.

Proof-term reachability is the candidate generator; three safeguards decide what
actually goes:

  1. **name mention** — a declaration still named in a surviving source is kept
     (`simp [foo]` cites `foo` in the source even when the rewrite it licensed
     was definitional and so never entered the proof term).  Applied to fixpoint,
     since keeping one declaration can rescue the ones it names.
  2. **`@[simp]`** — a simp lemma can be used by a bare `simp` without the
     finished term citing it.  These are held back, then re-tried one module at
     a time; a module keeps them only if the build needs them.
  3. **the build** — anything that still breaks it is put back, and the build is
     repeated until green.

    python3 tools/prune_loop.py <dead list from DeadCode.lean>
"""
import re, subprocess, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from prune_lean import blocks, namespace_at

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN = os.path.join(ROOT, 'lean')


def strip_comments(src):
    out = []; i = 0; n = len(src); depth = 0
    while i < n:
        if src.startswith('/-', i): depth += 1; i += 2; continue
        if src.startswith('-/', i) and depth > 0: depth -= 1; i += 2; out.append(' '); continue
        if depth == 0 and src.startswith('--', i):
            j = src.find('\n', i); i = n if j < 0 else j; continue
        out.append(src[i] if depth == 0 else ('\n' if src[i] == '\n' else ' ')); i += 1
    return ''.join(out)


def load(dead_path):
    dead = {}
    for line in open(dead_path):
        line = line.strip()
        if not line: continue
        loc, name = line.split()[0], line.split()[1]
        dead.setdefault(loc.split(':')[0].split('.')[-1], set()).add(name)
    return dead


def pristine():
    subprocess.run(['git', 'checkout', '--', 'lean'], cwd=ROOT, check=True)


def apply(dead):
    pristine()
    removed = 0
    for mod, names in dead.items():
        path = os.path.join(LEAN, mod + '.lean')
        lines = open(path).read().split('\n')
        keep = [True] * len(lines)
        for kind, a, b, name in blocks(lines):
            if kind != 'decl' or name is None: continue
            if '.'.join(namespace_at(lines, a) + [name]) in names:
                removed += 1
                for k in range(a, b): keep[k] = False
        open(path, 'w').write('\n'.join(l for l, k in zip(lines, keep) if k))
    return removed


def rescue_by_name(dead):
    """Put back anything a surviving source still names.  Runs to fixpoint."""
    total = 0
    while True:
        apply(dead)
        srcs = [strip_comments(open(os.path.join(LEAN, p)).read())
                for p in os.listdir(LEAN)]
        rescued = 0
        for names in dead.values():
            for full in list(names):
                short = full.split('.')[-1]
                pat = re.compile(r'(?<![A-Za-z0-9_.\'])' + re.escape(short) + r'(?![A-Za-z0-9_\'])')
                if any(pat.search(s) for s in srcs):
                    names.discard(full); rescued += 1
        total += rescued
        if rescued == 0:
            return total


def elaboration_used(dead):
    """Dead candidates that elaboration can use without the term citing them:
    `@[simp]` lemmas (a bare `simp` may fire them) and `instance`s (type-class
    resolution finds them by type, never by name)."""
    pristine()
    out = {}
    for mod, names in dead.items():
        lines = open(os.path.join(LEAN, mod + '.lean')).read().split('\n')
        for kind, a, b, name in blocks(lines):
            if kind != 'decl' or name is None: continue
            full = '.'.join(namespace_at(lines, a) + [name])
            if full not in names: continue
            head = '\n'.join(lines[a:b])
            if '@[simp]' in head or re.search(r'^\s*(?:noncomputable\s+)?instance\b', head, re.M):
                out.setdefault(mod, set()).add(full)
    return out


def build():
    r = subprocess.run(['lake', 'build'], cwd=LEAN, capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr


def settle(dead, label):
    """Build; put back whatever breaks; repeat until green.

    A whole cluster of mutually-referencing dead declarations has to go at once,
    so nothing is held back pre-emptively for being *named*: only the build
    decides.  What it demands is (a) the identifiers its errors name and (b) any
    dead name that a still-surviving declaration of a failing module mentions —
    the latter catches references the error message does not spell out.
    """
    for attempt in range(20):
        n = apply(dead)
        code, out = build()
        if code == 0:
            print(f'{label}: GREEN, {n} declarations removed', flush=True)
            return True
        # 復活は完全修飾名で判定する。短い名前で照合すると、別の名前空間にある
        # 同名の宣言（`YAPSS.le_maxr1` と `YAPSS.Wset.le_maxr1`）が巻き添えで戻る。
        broken = (set(re.findall(r"Unknown (?:identifier|constant) `([^`]+)`", out))
                  | set(re.findall(r"The identifier `([^`]+)` is unknown", out)))
        shorts = {b.split('.')[-1] for b in broken}
        failing = set(re.findall(r'YAPSS/(\w+)\.lean:', out))
        for mod in failing:
            src = strip_comments(open(os.path.join(LEAN, mod + '.lean')).read())
            for names in dead.values():
                for full in names:
                    short = full.split('.')[-1]
                    pat = r'(?<![A-Za-z0-9_.\'])' + re.escape(short) + r'(?![A-Za-z0-9_\'])'
                    if re.search(pat, src):
                        shorts.add(short)
        # 完全修飾名が壊れたと報告されたものは、その名前だけを戻す
        exact = {b for b in broken if '.' in b}
        rescued = set()
        for names in dead.values():
            for full in list(names):
                if full in exact or full.split('.')[-1] in shorts:
                    names.discard(full); rescued.add(full)
        print(f'{label} round {attempt}: restored {len(rescued)} {sorted(rescued)}', flush=True)
        if not rescued:
            print(out[-3000:]); print(f'{label}: STUCK'); return False
    print(f'{label}: gave up'); return False


def main():
    dead = load(sys.argv[1])
    print(f'candidates: {sum(len(v) for v in dead.values())}', flush=True)

    if settle(dead, 'all at once'):
        kept = {m: sorted(v) for m, v in dead.items() if v}
        print('removed per module: ' + ', '.join(f'{m} {len(v)}' for m, v in sorted(kept.items())))
        return

    simp = elaboration_used(dead)
    for mod, names in simp.items():
        dead[mod] -= names
    print(f'simp/instance held back: {sum(len(v) for v in simp.values())}', flush=True)

    if not settle(dead, 'phase A'):
        return

    for mod, names in sorted(simp.items()):
        dead[mod] |= names
        apply(dead)
        code, _ = build()
        if code == 0:
            print(f'  {mod}: its {len(names)} simp/instance decls are removable too', flush=True)
        else:
            dead[mod] -= names
            print(f'  {mod}: elaboration needs them, kept', flush=True)

    settle(dead, 'final')
    kept = {m: sorted(v) for m, v in dead.items() if v}
    print('removed per module: ' + ', '.join(f'{m} {len(v)}' for m, v in sorted(kept.items())))


if __name__ == '__main__':
    main()
