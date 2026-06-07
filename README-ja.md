# yet-another-pss-proof

ペア数列システム (Pair Sequence System, PSS) の停止性の証明とその Isabelle/HOL による形式証明。

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

## バージョン管理内ファイル

| ファイル | 役割 |
|---|---|
| `README-ja.md` | このファイル。リポジトリ内ファイルの説明。 |
| `proof-ja.md` | markdown + MathJax による**完成した証明本文**（上位・人間向け）。Isabelle に変換できる証明のみを記し、経験的・未証明事項は書かない（循環論法防止）。 |
| `memo.md` | 証明完成のための作業メモ（経験的観察・戦略・未解決の核の分析）。証明本文ではない。 |
| `def.thy` | Bashicu 氏のペア数列システムの定義部分（Isabelle）。P進大好きbot 氏の論文（下記出典）に倣い、論文に忠実な変数名を用いる。 |
| `proofs.thy` | `proof-ja.md` に対応する上位の形式証明（停止性定理本体）。`proof` は Isabelle の予約語のため `proofs` とする。 |
| `mechanized.thy` | `proof-ja.md` では省いた細かい部分（下位）。記法 `p_a(b)+c`、線形順序、translate、減少補題。 |
| `wf.thy` | 整礎性の還元（減少→対角 accessibility、maxsub 単調性、within-level への還元）。 |
| `wo.thy` | 整礎性の核（整備中）。Towsner の distinguished-set 法（下記出典）による整礎順序記法を移植し、PSS 記法を順序埋め込みして整礎性を得る。 |
| `ROOT` | Isabelle セッション `YAPSS` のビルド定義。 |

## ビルド

```sh
isbman build -d . -v YAPSS
```

（`isbman` は同一マシン上で複数の証明を安全に走らせるための Isabelle ビルドマネージャ。）

## 出典・引用 (Reference)
- Bashicu, "[BASIC 言語による巨大数のまとめ](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:BashicuHyudora/BASIC%E8%A8%80%E8%AA%9E%E3%81%AB%E3%82%88%E3%82%8B%E5%B7%A8%E5%A4%A7%E6%95%B0%E3%81%AE%E3%81%BE%E3%81%A8%E3%82%81?oldid=15603&useskin=oasis)", [巨大数研究 Wiki](http://ja.googology.wikia.com/) ユーザーブログ, 2015.8.21.（ペア数列システムの考案）
- P進大好きbot. "[ペア数列の停止性](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E3%81%AE%E5%81%9C%E6%AD%A2%E6%80%A7)", [巨大数研究 Wiki](http://ja.googology.wikia.com/) ユーザーブログ, 2018.11.11.（ペア数列の停止性の証明。本リポジトリの PSS 定義もこの論文に倣う）
- W. Buchholz, "[A new system of proof-theoretic ordinal functions](https://www.sciencedirect.com/science/article/pii/0168007286900527)", Annals of Pure and Applied Logic, Volume 32, 1986, pp. 195–207.（PSS の強さ ψ₀(ψ_ω(0)) ＝ Buchholz ordinal）
- H. Towsner, "[Polymorphic Ordinal Notations](https://arxiv.org/abs/2504.02131)", arXiv:2504.02131, 2025.（整礎性核 `wo.thy` の distinguished-set 整礎性証明の移植元）
