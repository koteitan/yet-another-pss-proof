#!/usr/bin/env python3
"""帰納法の仮定を「〜である」ではなく「〜を仮定する」の形に揃える。

    帰納法の仮定は Φ(A') である。          -> Φ(A') を仮定する。
    帰納法の仮定は Φ(A')、すなわち … である。 -> Φ(A')、すなわち … を仮定する。
    the induction hypothesis is Φ(A').     -> assume Φ(A').

文をまたがないよう、閉じの「である」/ ピリオドまでの間に句点・改行 2 つ・
```math フェンスの外の '.' が来ない場合だけ置換する。残りは報告して手で直す。

    python3 tools/ih_phrasing.py            # 実行
    python3 tools/ih_phrasing.py --dry-run  # 置換数と残りを表示するだけ
"""
import re, sys, glob, os

# --- 日本語 -----------------------------------------------------------------
# 「帰納法の仮定は」…「である。」「であり、」「である」（行末）
JA = [
    (re.compile(r'帰納法の仮定は\s*((?:[^。]|\n)*?)である。'), r'\1を仮定する。'),
    (re.compile(r'帰納法の仮定は\s*((?:[^。]|\n)*?)であり、'), r'\1を仮定し、'),
    (re.compile(r'帰納法の仮定は\s*((?:[^。]|\n)*?)である(?=\n)'), r'\1を仮定する'),
]

# --- 英語 -------------------------------------------------------------------
# 文頭の The … / 文中の the … 。閉じは最初のピリオド（数式の中は $`…`$ で守られる）。
EN = [
    (re.compile(r'The induction hypothes[ei]s (?:is|are) ((?:[^.]|\.\d|\n)*?)\.'),
     r'Assume \1.'),
    (re.compile(r'the induction hypothes[ei]s (?:is|are) ((?:[^.]|\.\d|\n)*?)\.'),
     r'assume \1.'),
]


def apply(path, rules):
    s = open(path).read()
    n = 0
    for pat, rep in rules:
        s, k = pat.subn(rep, s)
        n += k
    return s, n


def main():
    dry = '--dry-run' in sys.argv
    tot = 0
    for p in sorted(glob.glob('lean/*.md')):
        b = os.path.basename(p)
        if b.startswith('requirement'):
            continue
        rules = JA if b.endswith('-ja.md') else EN
        s, n = apply(p, rules)
        if n:
            tot += n
            print('%-20s %3d' % (b, n))
            if not dry:
                open(p, 'w').write(s)
    print('置換 %d 箇所' % tot)

    left = []
    for p in sorted(glob.glob('lean/*.md')):
        b = os.path.basename(p)
        if b.startswith('requirement'):
            continue
        t = apply(p, JA if b.endswith('-ja.md') else EN)[0]
        pat = '帰納法の仮定は' if b.endswith('-ja.md') else None
        hits = (t.count(pat) if pat else
                len(re.findall(r'[Tt]he induction hypothes[ei]s (?:is|are)', t)))
        if hits:
            left.append((b, hits))
    if left:
        print('\n残り（手で直す）:')
        for b, n in left:
            print('  %-20s %d' % (b, n))
    else:
        print('残りなし')


if __name__ == '__main__':
    main()
