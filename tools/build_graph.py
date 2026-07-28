#!/usr/bin/env python3
"""lean/graph-data.json と tools/graph_template.html から lean/graph.html を作る。

    python3 tools/graph_data.py     # md からグラフを抽出して graph-data.json を書く
    python3 tools/build_graph.py    # graph-data.json を埋め込んで graph.html を書く

graph.html は 1 ファイルで完結し、外部への通信をしない。
"""
import json, os

DATA = 'lean/graph-data.json'
TEMPLATE = 'tools/graph_template.html'
OUT = 'lean/graph.html'
MARK = '/*__DATA__*/'


def main():
    data = json.load(open(DATA))
    html = open(TEMPLATE).read()
    if MARK not in html:
        raise SystemExit('%s に %s が無い' % (TEMPLATE, MARK))
    # </script> がデータ中に現れると <script> が途中で閉じてしまう
    blob = json.dumps(data, ensure_ascii=False, separators=(',', ':')).replace('</', '<\\/')
    open(OUT, 'w').write(html.replace(MARK, blob))
    print('%s  %d ノード %d 辺  %d KB'
          % (OUT, len(data['nodes']), len(data['edges']), os.path.getsize(OUT) // 1024))


if __name__ == '__main__':
    main()
