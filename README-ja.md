[English](README.md)

# yet-another-pss-proof

Version: **v1.2.2**

**ペア数列システム**（Pair Sequence System, PSS。2 行のバシク行列システム）の停止性の
独立な証明と、その Lean 4 / Mathlib による形式証明。

PSS は Bashicu 氏が考案し、その停止性は P進大好きbot 氏が Buchholz の崩壊関数 $\psi$ を
用いて最初に証明した。本リポジトリはそれとは**別の証明**を与える。ペア数列を
$p_a(b)+c$ という独自の三分木記法へ翻訳し、その記法の上で停止性を導く。

停止性の主定理は無条件・`sorry` なしで完成している。
`#print axioms YAPSS.PSS_terminates_unconditional` は
`[propext, Classical.choice, Quot.sound]` のみを返し、`lake build` はプロジェクト
全体で通る。経路のどこにも順序数は現れず、これは主張ではなく機械的に確認できる。
`import Final` した Lean の環境には定数 `Ordinal` がそもそも存在せず、Mathlib の
順序数・濃度のモジュールは 1 つも import 閉包に入らない。

数列を整礎な記法へ写し、展開の 1 段で測度が真に減少することを示す、という戦略そのものは
原始数列システム（Primitive Sequence System, PrSS）の停止証明
（[`prss-proof`](https://github.com/koteitan/prss-proof)）と同じである。
本証明で新しいのは、その記法の整礎性を順序数を使わずに示す部分である。

PSS の強さは $\psi_0(\psi_\omega(0))$（Buchholz ordinal）と考えられており、
$p_a(b)$ の添字 $a$ を自然数に取ることに対応する。

## 証明

[`lean/README-ja.md`](lean/README-ja.md)

## グラフ

[`lean/graph/index.html`](lean/graph/index.html) — 440 の定義・定理をノード、2360 の参照を
矢印にしたもの。GitHub は `.html` をソースとして表示するので、リポジトリを手元に持ってきて開く。

## ビルド

```sh
cd lean && lake build
```

Lean 4 と Mathlib `v4.30.0`。

（Isabelle 版は v1.0.1 で撤去した。今後 `lean/` から改めて翻訳する予定。旧 Isabelle 開発は
タグ `ya-pss-isabelle-archive` に保存されている。）

## ディレクトリ構造

```
lean/                 Lean 4 / Mathlib による形式証明
  README.md           11 モジュールの索引（依存順）
  requirement.md      lean/*.md の編集方針
  Pss.lean/.md        ペア数列システムの定義
  Term.lean/.md       記法 p_a(b)+c、順序、翻訳
  Decrease.lean/.md   展開の 1 段が測度を真に減らすこと
  Reduction.lean/.md  停止性の整礎性への還元
  Cnf.lean/.md        Cantor 標準形条件とコピー分解
  Seqlex.lean/.md     翻訳が列辞書式順序への順序同型であること
  Column.lean/.md     接頭辞不変性と標準形の位置的不変量
  Cofinality.lean/.md Bachmann 共終性
  ArgDom.lean/.md     その宿主に依らない核
  Wset.lean/.md       反復帰納的集合 W_u
  Final.lean/.md      主定理
  lakefile.toml       11 モジュールを依存順に roots として列挙
  graph/              index.html — 参照グラフと、それを作る一式
  memo/               証明の一部ではない検査用コード
  tools/              DeadCode.lean — 証明項が到達しない宣言の検出
tools/                実行可能な PSS モデルと、形式化前に主張を反例探索で確かめる probe
task.md               作業ツリー
```

## 出典・引用 (Reference)

- Bashicu, "[BASIC 言語による巨大数のまとめ](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:BashicuHyudora/BASIC%E8%A8%80%E8%AA%9E%E3%81%AB%E3%82%88%E3%82%8B%E5%B7%A8%E5%A4%A7%E6%95%B0%E3%81%AE%E3%81%BE%E3%81%A8%E3%82%81?oldid=15603&useskin=oasis)", [巨大数研究 Wiki](http://ja.googology.wikia.com/) ユーザーブログ, 2015.8.21.（疑似BASIC言語によるペア数列システムの最初の定義）
- koteitan, "[バシク行列の亜種ルールの分類](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Koteitan/%E3%83%90%E3%82%B7%E3%82%AF%E8%A1%8C%E5%88%97%E3%81%AE%E4%BA%9C%E7%A8%AE%E3%83%AB%E3%83%BC%E3%83%AB%E3%81%AE%E5%88%86%E9%A1%9E)", [巨大数研究 Wiki](http://ja.googology.wikia.com/) ユーザーブログ, 2018.6.2.（バシク行列の亜種ルールの分類）
- P進大好きbot, "[ペア数列の停止性](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E3%81%AE%E5%81%9C%E6%AD%A2%E6%80%A7)", [巨大数研究 Wiki](http://ja.googology.wikia.com/) ユーザーブログ, 2018.11.11.（ペア数列の停止性の最初の証明。本リポジトリの PSS の定義もこれに倣う）
- W. Buchholz, "[A new system of proof-theoretic ordinal functions](https://www.sciencedirect.com/science/article/pii/0168007286900527)", Annals of Pure and Applied Logic, Volume 32, 1986, pp. 195–207.（崩壊関数 $\psi_v$ と記法系 $\mathrm{OT}$）
- W. Buchholz, "[An independence result for $(\Pi^1_1\text{-}\mathrm{CA})+\mathrm{BI}$](https://www.sciencedirect.com/science/article/pii/0168007287900780)", Annals of Pure and Applied Logic, Volume 33, 1987, pp. 131–155.（§2 の反復帰納的集合 $W_v$ と、$\mathrm{OT}$ の整礎性の**構文的**証明。本証明の `Wset.lean` / `Cofinality.lean` はこの方法をペア数列へ移したもの）
