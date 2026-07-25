[English](README.md)

# yet-another-pss-proof v1.2.0

ペア数列システム (Pair Sequence System, PSS) の停止性の証明とその Lean 4 / Mathlib による形式証明。
**停止性の主定理は無条件・`sorry` なしで完成している**（`lean/Final.lean`、`#print axioms` は
`propext` / `Classical.choice` / `Quot.sound` のみ）。順序数も Buchholz 記法への翻訳も用いない。
これは主張ではなく機械的に確認できる：`import YAPSS.Final` した環境には定数 `Ordinal` が
そもそも存在せず、Mathlib の順序数・濃度のモジュールは 1 つも import 閉包に入らない。

## 経緯と本証明の位置づけ
**ペア数列システム** (PSS) は Bashicu 氏が考案した。
その停止性は P進大好きbot 氏が証明した（下記出典、Buchholz の ψ を用いる）。
本リポジトリの証明は、また別のアプローチによる PSS 停止証明である。

本証明はペア数列を **`p_a(b)+c` という独自の三分木記法** へ変換し、
`(a,b,c)` の3次元超限帰納法で素直に停止性を導く。これは原始数列システム
(Primitive Sequence System, PrSS) の停止証明
（[`prss-proof`](https://github.com/koteitan/prss-proof)）と同じ戦略
（数列を整礎な記法へ写し、展開ステップで測度が真に減少することを示す）を、
ペア数列へ一般化したものである。PSS の強さは ψ₀(ψ_ω(0))（Buchholz ordinal）と
考えられており、添字 `a` を自然数（0,1,2,… とその上限 ω）に取ることに対応する。

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
  PROOF-STATUS.md     証明の現状と経緯（authoritative）
  lakefile.toml       11 モジュールを依存順に roots として列挙
  tools/              DeadCode.lean — 証明項が到達しない宣言の検出
md/                   旧世代の証明本文（lean/*.md へ移行中）
tools/                実行可能な PSS モデルと、形式化前に主張を反例探索で確かめる probe
task.md               作業ツリー
```

`lean/<module>.lean` の隣に同名の `lean/<module>.md` を置き、同じ証明を人間向けに書く。
両者は 1 対 1 に保つ。

## ビルド

```sh
cd lean && lake build YAPSS
```

（Isabelle 版は v1.0.1 で撤去した。今後 `lean/` から改めて翻訳する予定。旧 Isabelle 開発は
タグ `ya-pss-isabelle-archive` に保存されている。）

## 出典・引用 (Reference)
- Bashicu, "[BASIC 言語による巨大数のまとめ](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:BashicuHyudora/BASIC%E8%A8%80%E8%AA%9E%E3%81%AB%E3%82%88%E3%82%8B%E5%B7%A8%E5%A4%A7%E6%95%B0%E3%81%AE%E3%81%BE%E3%81%A8%E3%82%81?oldid=15603&useskin=oasis)", [巨大数研究 Wiki](http://ja.googology.wikia.com/) ユーザーブログ, 2015.8.21.（ペア数列システムの考案）
- P進大好きbot. "[ペア数列の停止性](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E3%81%AE%E5%81%9C%E6%AD%A2%E6%80%A7)", [巨大数研究 Wiki](http://ja.googology.wikia.com/) ユーザーブログ, 2018.11.11.（ペア数列の停止性の証明。本リポジトリの PSS 定義もこの論文に倣う）
- W. Buchholz, "[A new system of proof-theoretic ordinal functions](https://www.sciencedirect.com/science/article/pii/0168007286900527)", Annals of Pure and Applied Logic, Volume 32, 1986, pp. 195–207.（PSS の強さ ψ₀(ψ_ω(0)) ＝ Buchholz ordinal）
- W. Buchholz, "[An independence result for (Π¹₁-CA)+BI](https://www.sciencedirect.com/science/article/pii/0168007287900780)", Annals of Pure and Applied Logic, Volume 33, 1987, pp. 131–155.（§2 の反復帰納的集合 $W_v$ と、$\mathrm{OT}_B$ の整礎性の**構文的**証明。本証明の `Wset.lean` / `Cofinality.lean` はこの方法をペア数列へ移したもの）
- koteitan, "[pss-proof](https://github.com/koteitan/pss-proof)".（P進大好きbot 氏の証明の形式化。その順序数を用いない $\mathrm{OT}_B$ 整礎性の構文的証明が本証明のルートの下敷き）
