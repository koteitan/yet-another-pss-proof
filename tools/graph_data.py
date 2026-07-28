#!/usr/bin/env python3
"""参照グラフを lean/graph-data.json に書く。

ノードと辺は **`lean/*.lean` のカーネルの証明項**から取る。抽出は Lean 側の
`lean/tools/GraphData.lean` が行い、その出力 `lean/tools/graph-deps.json` を
ここで読む（記法・`@[simp]` の暗黙の使用・`omega` が生成した補題も辺に入る）。

    cd lean && lake env lean tools/GraphData.lean > tools/graph-deps.json
    python3 tools/graph_data.py

見出しの説明文だけは `lean/*.md` から取って添える（Lean 側には無いため）。
"""
import json, os, re

LEAN = 'lean'
DEPS = os.path.join(LEAN, 'tools', 'graph-deps.json')
OUT = os.path.join(LEAN, 'graph-data.json')
MODULES = ['Pss', 'Term', 'Decrease', 'Reduction', 'Cnf', 'Seqlex',
           'Column', 'Cofinality', 'ArgDom', 'Wset', 'Final']

SEC = re.compile(r'<a id="([td])-([^"]+)"></a>\s*\n##\s*(.+)')


def md_info():
    """短縮名 -> (説明, md ファイル名)。英語版の見出しから取る。"""
    info = {}
    for m in MODULES:
        k = 0
        while True:
            name = m if k == 0 else '%s-%d' % (m, k + 1)
            p = os.path.join(LEAN, name + '.md')
            if not os.path.exists(p):
                break
            for kind, ident, title in SEC.findall(open(p).read()):
                desc = re.sub(r'^\s*(Theorem|Definition):\s*', '', title.strip())
                desc = re.sub(r'\s*\(([TD]\.[^)]+)\)\s*$', '', desc)
                info[ident] = (desc, name + '.md')
            k += 1
    return info


def main():
    deps = json.load(open(DEPS))
    info = md_info()

    nodes = []
    for n in deps['nodes']:
        short = n['name'].split('.')[-1]
        kind = 't' if n['kind'] == 'thm' else 'd'
        desc, file = info.get(short, ('', ''))
        nodes.append({
            'id': n['name'],
            'kind': kind,
            'name': short,
            'desc': desc,
            'module': n['module'],
            'file': file or '%s.lean:%d' % (n['module'], n['line']),
            'line': n['line'],
        })
    nodes.sort(key=lambda n: (MODULES.index(n['module']), n['line']))

    ids = {n['id'] for n in nodes}
    edges = [list(t) for t in dict.fromkeys(
        (a, b) for a, b in deps['edges'] if a in ids and b in ids and a != b)]

    indeg = {n['id']: 0 for n in nodes}
    for _, b in edges:
        indeg[b] += 1
    for n in nodes:
        n['indeg'] = indeg[n['id']]

    json.dump({'modules': MODULES, 'nodes': nodes, 'edges': edges},
              open(OUT, 'w'), ensure_ascii=False, separators=(',', ':'))
    miss = [n['name'] for n in nodes if not n['desc']]
    print('ノード %d  辺 %d' % (len(nodes), len(edges)))
    if miss:
        print('md に見出しが無い宣言 %d 件: %s' % (len(miss), ' '.join(miss[:8])))


if __name__ == '__main__':
    main()
