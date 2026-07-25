#!/usr/bin/env python3
"""lean/*.md を英日対訳の 2 系統に分ける（my-github-md-rule のモード 4）。

`lean/X.md` を英語の本体、`lean/X-ja.md` を日本語とする。日本語側の内部リンクは
すべて `-ja` 版を指すように張り替え、両方の冒頭に言語切り替えのナビ行を置く。

    python3 tools/bilingual.py            # 実行
    python3 tools/bilingual.py --dry-run  # 何をするか表示するだけ

英語側の中身は分岐した時点では日本語のままである（翻訳は別工程）。
"""
import os, re, sys, glob

LEAN = 'lean'
SKIP = {'PROOF-STATUS.md', 'task.md'}     # 作業用の文書。証明本文ではないので対象外
MODULES = ['Pss', 'Term', 'Decrease', 'Reduction', 'Cnf', 'Seqlex',
           'Column', 'Cofinality', 'ArgDom', 'Wset', 'Final']


def targets():
    return sorted(os.path.basename(p) for p in glob.glob(os.path.join(LEAN, '*.md'))
                  if os.path.basename(p) not in SKIP and not os.path.basename(p).endswith('-ja.md'))


def ja(name):
    return name[:-3] + '-ja.md'


def to_ja_links(text, names):
    """`](Foo.md#x)` を `](Foo-ja.md#x)` に。対象外のファイルはそのまま。"""
    def sub(m):
        f, rest = m.group(1), m.group(2)
        return '](%s%s)' % (ja(f) if f in names else f, rest)
    text = re.sub(r'\]\(([\w\-]+\.md)((?:#[^)]*)?)\)', sub, text)
    return text.replace('](../README.md)', '](../README-ja.md)')


def parts_of(mod):
    out = [mod]
    k = 2
    while os.path.exists(os.path.join(LEAN, '%s-%d.md' % (mod, k))):
        out.append('%s-%d' % (mod, k)); k += 1
    return out


def nav(stem, lang):
    """stem は拡張子なしの英語側の名前（Wset-2 など）。"""
    en, jp = stem + '.md', stem + '-ja.md'
    home = 'README.md' if lang == 'en' else 'README-ja.md'
    if stem in ('README', 'requirement'):
        back = '[← README](../%s)' % ('README.md' if lang == 'en' else 'README-ja.md')
        if stem == 'requirement':
            back = '[← README](%s)' % home
    else:
        back = '[← README](%s)' % home
    line = '%s | [English](%s) | [Japanese](%s)' % (back, en, jp)
    mod = re.sub(r'-\d+$', '', stem)
    if mod in MODULES:
        ps = parts_of(mod)
        if len(ps) > 1:
            items = []
            for i, p in enumerate(ps):
                f = p + ('.md' if lang == 'en' else '-ja.md')
                items.append('**%d**' % (i + 1) if p == stem else '[%d](%s)' % (i + 1, f))
            line += ' | %s %s' % (mod, ' '.join(items))
    return line


def main():
    dry = '--dry-run' in sys.argv
    names = set(targets())
    for name in sorted(names):
        stem = name[:-3]
        src = os.path.join(LEAN, name)
        text = open(src).read()
        body = re.sub(r'^\[← README\][^\n]*\n', '', text, count=1)   # 旧ナビ行を落とす
        en = nav(stem, 'en') + '\n' + body
        jp = nav(stem, 'ja') + '\n' + to_ja_links(body, names)
        if dry:
            print('%-18s -> %s + %s' % (name, name, ja(name)))
            continue
        open(os.path.join(LEAN, name), 'w').write(en)
        open(os.path.join(LEAN, ja(name)), 'w').write(jp)
    print('%d ファイルを 2 系統に分けた' % len(names))


if __name__ == '__main__':
    main()
