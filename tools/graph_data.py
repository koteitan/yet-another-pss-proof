#!/usr/bin/env python3
"""lean/*.md から定義・定理の参照グラフを取り出し、lean/graph-data.json に書く。

ノードは 1 つの節（`<a id="t-foo">` / `<a id="d-foo">`）、辺はその節の本文から
別の節へのリンクである。英語版だけを見る（日本語版は同じ構造を持つ）。

    python3 tools/graph_data.py
"""
import json, os, re, sys

LEAN = 'lean'
SKIP = {'README.md', 'requirement.md', 'graph.html'}
MODULES = ['Pss', 'Term', 'Decrease', 'Reduction', 'Cnf', 'Seqlex',
           'Column', 'Cofinality', 'ArgDom', 'Wset', 'Final']

SEC = re.compile(r'<a id="([td]-[^"]+)"></a>\s*\n##\s*(.+)')
LINK = re.compile(r'\]\((?:([\w\-]+)\.md)?#([td]-[^)]+)\)')


def files():
    out = []
    for m in MODULES:
        k = 0
        while True:
            name = m if k == 0 else '%s-%d' % (m, k + 1)
            p = os.path.join(LEAN, name + '.md')
            if not os.path.exists(p):
                break
            out.append((m, name, p))
            k += 1
    return out


def main():
    nodes, edges, order = [], [], {}
    seen = set()
    for mod, name, path in files():
        text = open(path).read()
        marks = [(m.start(), m.group(1), m.group(2).strip()) for m in SEC.finditer(text)]
        for i, (pos, ident, title) in enumerate(marks):
            end = marks[i + 1][0] if i + 1 < len(marks) else len(text)
            body = text[pos:end]
            if ident in seen:            # 同じ節が 2 度出ることはない
                continue
            seen.add(ident)
            order[ident] = len(nodes)
            # 見出しの "Theorem: 説明 (T.foo)" から説明部分を取る
            desc = re.sub(r'^\s*(Theorem|Definition):\s*', '', title)
            desc = re.sub(r'\s*\(([TD]\.[^)]+)\)\s*$', '', desc)
            nodes.append({
                'id': ident,
                'kind': ident[0],                       # 't' か 'd'
                'name': ident[2:],
                'desc': desc,
                'module': mod,
                'file': name + '.md',
            })
            for _, tgt in LINK.findall(body):
                if tgt != ident:
                    edges.append([ident, tgt])
    ids = {n['id'] for n in nodes}
    edges = [e for e in edges if e[1] in ids]
    # 同じ辺の重複を落とす
    edges = [list(t) for t in dict.fromkeys(map(tuple, edges))]

    indeg = {n['id']: 0 for n in nodes}
    for _, b in edges:
        indeg[b] += 1
    for n in nodes:
        n['indeg'] = indeg[n['id']]

    data = {'modules': MODULES, 'nodes': nodes, 'edges': edges}
    with open(os.path.join(LEAN, 'graph-data.json'), 'w') as f:
        json.dump(data, f, ensure_ascii=False, separators=(',', ':'))
    print('ノード %d  辺 %d' % (len(nodes), len(edges)))

    if '--stat' in sys.argv:
        for k, label in ((0, '参照元なし'), (1, '参照元 1 つ')):
            xs = [n for n in nodes if n['indeg'] == k and n['kind'] == 't']
            print('\n%s の定理 %d 件' % (label, len(xs)))
            for n in xs:
                print('  %-14s %s' % (n['file'][:-3], n['name']))


if __name__ == '__main__':
    main()
