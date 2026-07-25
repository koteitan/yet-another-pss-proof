#!/usr/bin/env python3
"""lean/<module>.md を数式の総量で分割し、リンクを張り替える。

GitHub は 1 ページの数式ソースが 2.6〜2.9 万文字を超えると、それ以降の数式を
描画せず Unable to render expression にする（実測）。境界は描画コストの予算で
あって式の個数ではないので、安全域 BUDGET を置いて分割する。

分割は宣言（<a id=...> の節）の境界でのみ行い、各部の数式量が均等になるように
切る。分割後、全ファイルの相互リンクを新しい所在へ張り替える。

    python3 tools/split_md.py            # 実行
    python3 tools/split_md.py --dry-run  # 分割案だけ表示
"""
import re, sys, os, glob, math

BUDGET = 20000
LEAN = 'lean'
MODULES = ['Pss', 'Term', 'Decrease', 'Reduction', 'Cnf', 'Seqlex',
           'Column', 'Cofinality', 'ArgDom', 'Wset', 'Final']


def math_chars(text):
    """このテキストが GitHub の予算に対して消費する数式ソースの文字数。"""
    lines = text.split('\n')
    n = 0
    i = 0
    while i < len(lines):
        if lines[i].strip() == '```math':
            j = i + 1
            body = []
            while j < len(lines) and lines[j].strip() != '```':
                body.append(lines[j]); j += 1
            n += len('\n'.join(body)) + 4
            i = j + 1
            continue
        for m in re.finditer(r'\$`([^`]+)`\$', lines[i]):
            n += len(m.group(1)) + 2
        i += 1
    return n


def sections(text):
    """(見出し前のヘッダ, [(アンカー名, 本文), ...]) に分ける。"""
    parts = re.split(r'(?m)^(?=<a id="[td]-)', text)
    head = parts[0]
    secs = []
    for p in parts[1:]:
        name = re.match(r'<a id="([td]-[^"]+)"></a>', p).group(1)
        secs.append((name, p))
    return head, secs


def pack(w, cap):
    """各部の合計が cap 以下になるよう、前から詰められるだけ詰める。
    連続分割で部の個数を最小にするには、この貪欲が最適である。"""
    groups, start, acc = [], 0, 0
    for i, x in enumerate(w):
        if acc and acc + x > cap:
            groups.append((start, i)); start, acc = i, 0
        acc += x
    groups.append((start, len(w)))
    return groups


def plan(secs, budget=BUDGET):
    """節を、数式量が均等な最小個数の連続部分列に分ける。

    まず budget で最小の部数 k を求め、次に k 部のまま最大の部が最小になる
    上限を二分探索する（節 1 つが budget を超える場合はそれ自体が 1 部になる）。"""
    w = [math_chars(b) for _, b in secs]
    if not w:
        return [(0, 0)]
    k = len(pack(w, max(budget, max(w))))
    lo, hi = max(w), sum(w)
    while lo < hi:
        mid = (lo + hi) // 2
        if len(pack(w, mid)) <= k:
            hi = mid
        else:
            lo = mid + 1
    return pack(w, lo)


def part_name(mod, i):
    return mod if i == 0 else '%s-%d' % (mod, i + 1)


def nav(mod, i, n):
    if n == 1:
        return '[← README](README.md)'
    items = []
    for k in range(n):
        items.append('**%d**' % (k + 1) if k == i
                     else '[%d](%s.md)' % (k + 1, part_name(mod, k)))
    return '[← README](README.md) ｜ %s %s' % (mod, ' '.join(items))


def main():
    dry = '--dry-run' in sys.argv
    layout = {}          # mod -> [(part file name, head, [(anchor, body)])]
    for mod in MODULES:
        text = open(os.path.join(LEAN, mod + '.md')).read()
        head, secs = sections(text)
        groups = plan(secs)
        layout[mod] = [(part_name(mod, i), head if i == 0 else None, secs[a:b])
                       for i, (a, b) in enumerate(groups)]
        if len(groups) > 1 or dry:
            print('%-11s %6d 文字 -> %d 分割  %s' % (
                mod, math_chars(text), len(groups),
                ' '.join(str(math_chars(''.join(b for _, b in g))) for _, _, g in layout[mod])))
    if dry:
        return

    # アンカー -> それが載るファイル
    where = {}
    for mod, parts in layout.items():
        for fname, _, secs in parts:
            for name, _ in secs:
                where[(mod, name)] = fname

    def relink(text, mod):
        def other(m):
            tgt, anc = m.group(1), m.group(2)
            return '](%s.md#%s)' % (where.get((tgt, anc), tgt), anc)
        text = re.sub(r'\]\((\w+?)(?:-\d+)?\.md#([td]-[^)]+)\)', other, text)

        def self_(m):
            anc = m.group(1)
            f = where.get((mod, anc))
            return '](#%s)' % anc if f == cur else '](%s.md#%s)' % (f, anc)
        return re.sub(r'\]\(#([td]-[^)]+)\)', self_, text)

    written = []
    for mod, parts in layout.items():
        n = len(parts)
        for i, (fname, head, secs) in enumerate(parts):
            cur = fname
            body = ''.join(b for _, b in secs)
            if head is None:
                head = nav(mod, i, n) + '\n\n'
            else:
                head = re.sub(r'^\[← README\]\(README\.md\)[^\n]*',
                              nav(mod, i, n), head, count=1)
            out = relink(head + body, mod).rstrip('\n') + '\n'
            open(os.path.join(LEAN, fname + '.md'), 'w').write(out)
            written.append(fname)
        for i in range(n, 12):                       # 前回より部が減ったら消す
            stale = os.path.join(LEAN, part_name(mod, i) + '.md')
            if os.path.exists(stale):
                os.remove(stale); print('削除', stale)
    print('書き出し %d ファイル' % len(written))


if __name__ == '__main__':
    main()
