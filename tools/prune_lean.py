#!/usr/bin/env python3
"""Delete declarations that `lean/tools/DeadCode.lean` reported as unreachable.

Usage:
    cd lean && lake env lean tools/DeadCode.lean | grep '^  YAPSS' > /tmp/dead.txt
    python3 tools/prune_lean.py /tmp/dead.txt [--apply]

The file is cut into top-level blocks.  A block is one declaration together with
the doc comment (`/-- ... -/`) and the attribute lines (`@[simp]`) that precede
it; `/-! ... -/` section comments, `namespace` / `end` / `open` lines and blank
lines are their own blocks and are never removed.  A block is deleted when the
name it declares is in the dead list.
"""
import re, sys, os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN = os.path.join(ROOT, 'lean')

DECL_KW = r'(?:theorem|lemma|def|abbrev|instance|inductive|structure|class|example)'
DECL_START = re.compile(
    r'^(?:@\[[^\]]*\]\s*)*(?:private\s+|protected\s+|noncomputable\s+|partial\s+|unsafe\s+)*'
    + DECL_KW + r'\b')
DECL_NAME = re.compile(DECL_KW + r'\s+([A-Za-z_][A-Za-z0-9_\'!?]*)')
ATTR_ONLY = re.compile(r'^@\[[^\]]*\]\s*$')


def blocks(lines):
    """Yield (kind, start, end, name) with end exclusive."""
    i, n = 0, len(lines)
    while i < n:
        ln = lines[i]
        # doc comment / attribute prefix that belongs to the next declaration
        pre = i
        while i < n and (lines[i].startswith('/--') or ATTR_ONLY.match(lines[i])):
            if lines[i].startswith('/--'):
                while i < n and '-/' not in lines[i]:
                    i += 1
            i += 1
        if i < n and DECL_START.match(lines[i]):
            head = lines[i]
            m = DECL_NAME.search(head)
            name = m.group(1) if m else None
            j = i + 1
            while j < n and not starts_top_level(lines, j):
                j += 1
            yield ('decl', pre, j, name)
            i = j
            continue
        if i > pre:                      # prefix not followed by a declaration
            yield ('other', pre, i, None)
            continue
        # standalone block comment
        if ln.startswith('/-'):
            j = i
            depth = 0
            while j < n:
                depth += lines[j].count('/-') - lines[j].count('-/')
                j += 1
                if depth <= 0:
                    break
            yield ('comment', i, j, None)
            i = j
            continue
        yield ('other', i, i + 1, None)
        i += 1


def starts_top_level(lines, j):
    ln = lines[j]
    if not ln or ln[0] in ' \t':
        return False
    return (DECL_START.match(ln) or ln.startswith('/--') or ln.startswith('/-!')
            or ln.startswith('/-') or ATTR_ONLY.match(ln)
            or re.match(r'^(namespace|end|open|section|variable|universe|import)\b', ln))


def namespace_at(lines, upto):
    """Namespace prefix in force at line `upto` (list of components).

    `section X` / `end X` do not affect the name prefix, so only `namespace`
    openings are pushed and an `end X` pops only when `X` matches the top.
    """
    stack = []
    for ln in lines[:upto]:
        m = re.match(r'^namespace\s+(\S+)', ln)
        if m:
            stack.append(m.group(1).split('.'))
            continue
        m = re.match(r'^end\s+(\S+)', ln)
        if m and stack and stack[-1] == m.group(1).split('.'):
            stack.pop()
    return [c for part in stack for c in part]


def main():
    dead_path = sys.argv[1]
    apply = '--apply' in sys.argv
    dead = {}
    for line in open(dead_path):
        line = line.strip()
        if not line:
            continue
        loc, name = line.split()[0], line.split()[1]
        mod = loc.split(':')[0].split('.')[-1]
        dead.setdefault(mod, set()).add(name)

    total = 0
    for mod, names in sorted(dead.items()):
        path = os.path.join(LEAN, mod + '.lean')
        lines = open(path).read().split('\n')
        keep = [True] * len(lines)
        hit = []
        for kind, a, b, name in blocks(lines):
            if kind != 'decl' or name is None:
                continue
            full = '.'.join(namespace_at(lines, a) + [name])
            if full in names:
                hit.append((full, a + 1, b - a))
                for k in range(a, b):
                    keep[k] = False
        missing = names - {h[0] for h in hit}
        # constructors of a deleted inductive are covered by their parent
        missing = {m for m in missing if m.rsplit('.', 1)[0] not in {h[0] for h in hit}}
        print(f'{mod}: {len(hit)} blocks, {sum(h[2] for h in hit)} lines'
              + (f'  UNMATCHED {sorted(missing)}' if missing else ''))
        total += sum(h[2] for h in hit)
        if apply:
            open(path, 'w').write('\n'.join(l for l, k in zip(lines, keep) if k))
    print(f'total {total} lines')


if __name__ == '__main__':
    main()
