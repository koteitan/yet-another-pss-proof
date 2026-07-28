#!/usr/bin/env python3
"""定義・定理の参照グラフのページ `lean/graph/index.html` を作る。

    cd lean && lake env lean graph/GraphData.lean > graph/deps.json   # 依存を取り直すとき
    python3 lean/graph/build.py                                       # ページを作る

ノードと辺は `deps.json`、すなわち **`lean/*.lean` のカーネルの証明項**から取る
（記法・`@[simp]` の暗黙の使用・`omega` が生成した補題も辺に入る）。見出しの説明文
だけは Lean 側に無いので `lean/*.md` から拾う。

出来上がる `index.html` は 1 ファイルで完結し、外部への通信をしない。
"""
import json, os, re

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.dirname(HERE)
DEPS = os.path.join(HERE, 'deps.json')
TEMPLATE = os.path.join(HERE, 'template.html')
DATA = os.path.join(HERE, 'data.json')
OUT = os.path.join(HERE, 'index.html')
MARK = '/*__DATA__*/'

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
            for _, ident, title in SEC.findall(open(p).read()):
                desc = re.sub(r'^\s*(Theorem|Definition):\s*', '', title.strip())
                desc = re.sub(r'\s*\(([TD]\.[^)]+)\)\s*$', '', desc)
                info[ident] = (desc, name + '.md')
            k += 1
    return info


def build_data():
    deps = json.load(open(DEPS))
    info = md_info()
    nodes = []
    for n in deps['nodes']:
        short = n['name'].split('.')[-1]
        desc, file = info.get(short, ('', ''))
        nodes.append({
            'id': n['name'],
            'kind': 't' if n['kind'] == 'thm' else 'd',
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
    return {'modules': MODULES, 'nodes': nodes, 'edges': edges}


def main():
    data = build_data()
    json.dump(data, open(DATA, 'w'), ensure_ascii=False, separators=(',', ':'))
    html = open(TEMPLATE).read()
    if MARK not in html:
        raise SystemExit('%s に %s が無い' % (TEMPLATE, MARK))
    # </script> がデータ中に現れると <script> が途中で閉じてしまう
    blob = json.dumps(data, ensure_ascii=False, separators=(',', ':')).replace('</', '<\\/')
    open(OUT, 'w').write(html.replace(MARK, blob))
    miss = [n['name'] for n in data['nodes'] if not n['desc']]
    print('%s  %d ノード %d 辺  %d KB'
          % (os.path.relpath(OUT), len(data['nodes']), len(data['edges']),
             os.path.getsize(OUT) // 1024))
    if miss:
        print('md に見出しが無い宣言 %d 件: %s' % (len(miss), ' '.join(miss[:8])))


if __name__ == '__main__':
    main()
