[English](README.md)

# yet-another-pss-proof v1.2.0

ペア数列システム (Pair Sequence System, PSS) の停止性の証明とその Lean 4 / Mathlib による形式証明。
**停止性の主定理は無条件・`sorry` なしで完成している**（`lean/YAPSS/Final.lean`、`#print axioms` は
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

## バージョン管理内ファイル

| ファイル | 役割 |
|---|---|
| `README-ja.md` | このファイル。リポジトリ内ファイルの説明。 |
| `proof-ja.md` | markdown + MathJax による**完成した証明本文**（上位・人間向け）。Isabelle に変換できる証明のみを記し、経験的・未証明事項は書かない（循環論法防止）。 |
| `memo.md` | 証明完成のための作業メモ（経験的観察・戦略・未解決の核の分析）。証明本文ではない。 |
| `lean/YAPSS/Def.lean` | Bashicu 氏のペア数列システムの定義（`ST_PS`・基本列 `M⟦n⟧`・`step`）。P進大好きbot 氏の論文（下記出典）に倣い、論文に忠実な変数名を用いる。 |
| `lean/YAPSS/Mechanized.lean` | 記法 `p_a(b)+c`（`Three`）、添字優先順序 `olt`、変換 `translate`、展開の分解 `oper_bad_blocks`。 |
| `lean/YAPSS/Proofs.lean` | 停止性の還元（整礎性 ⟹ `WellFounded stepRel`）。 |
| `lean/YAPSS/Cofinality.lean` | **PSS Bachmann 共終性**（基本列が limit の下に共終）。 |
| `lean/YAPSS/AscArg.lean` | 共終性の核 `ArgDomCore` を `ST_PS` 導出への帰納で証明。 |
| `lean/YAPSS/Wset.lean` | **反復帰納的集合 `W_u`**（Buchholz 1987 §2 の PSS 移植）と可到達性の橋。 |
| `lean/YAPSS/Final.lean` | **主定理** `PSS_terminates_unconditional`（無条件・`sorry` なし・順序数を用いない）。 |
| `lean/PROOF-STATUS.md` | 証明の現状と経緯（authoritative）。 |
| `md/requirement.md` | `md/YAPSS/*.md`（人間向け証明本文）の編集方針。 |

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
