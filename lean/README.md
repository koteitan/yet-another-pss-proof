[← README](../README.md)

# `lean/` — PSS 停止性の形式証明

| モジュール | 名前 | 説明 | 依存先 |
|---|---|---|---|
| [`Pss`](Pss.md) | ペア数列システム | ペア数列 $`M`$、基本列 $`M[n]`$、標準形 $`\mathrm{ST\_PS}`$、展開 $`M \Rightarrow N`$ の定義 | — |
| [`Term`](Term.md) | 三分岐記法 | 記法 $`p_a(b)+c`$、添字優先辞書式順序 $`\prec`$、翻訳 $`\mathrm{tr}`$ | [`Pss`](Pss.md) |
| [`Decrease`](Decrease.md) | 測度の減少 | 展開の分岐の分解と $`\mathrm{tr}(M[n]) \prec \mathrm{tr}(M)`$ | [`Term`](Term.md) |
| [`Reduction`](Reduction.md) | 停止性への還元 | $`\prec`$ が $`\mathrm{tr}`$ の像の上で整礎ならば展開関係は停止する | [`Decrease`](Decrease.md) |
| [`Cnf`](Cnf.md) | Cantor 標準形条件 | 条件 $`\mathrm{cnf}`$ と、コピー分解 $`\mathrm{sh}_d`$ / $`\mathrm{cp}_d`$ | [`Decrease`](Decrease.md) |
| [`Seqlex`](Seqlex.md) | 列辞書式順序 | $`\mathrm{tr}`$ が標準形の上で列辞書式順序への順序同型であること | [`Cnf`](Cnf.md) |
| [`Column`](Column.md) | 列の不変量 | 親子関係の接頭辞不変性と、位置的不変量 $`\mathrm{r1ok}`$ / $`\mathrm{z0ok}`$ | [`Cnf`](Cnf.md), [`Seqlex`](Seqlex.md) |
| [`Cofinality`](Cofinality.md) | Bachmann 共終性 | $`N \prec M`$ ならばある $`n`$ で $`N \preceq M[n]`$ | [`Term`](Term.md), [`Seqlex`](Seqlex.md), [`Column`](Column.md) |
| [`ArgDom`](ArgDom.md) | 共終性の核 | 共終性を宿主に依らない核 $`\mathrm{ArgDomCore}`$ に還元し、それを証明する | [`Cofinality`](Cofinality.md) |
| [`Wset`](Wset.md) | 反復帰納的集合 | 最小不動点 $`W_u`$ とその帰納法、標準形が $`W_u`$ に属すること | [`Column`](Column.md) |
| [`Final`](Final.md) | 主定理 | $`\mathrm{PSS\_terminates\_unconditional}`$ と無限展開列の非存在 | [`ArgDom`](ArgDom.md), [`Wset`](Wset.md), [`Reduction`](Reduction.md) |

編集方針は [`requirement.md`](requirement.md)。証明の現状と経緯は
[`PROOF-STATUS.md`](PROOF-STATUS.md)。

## ビルド

```sh
cd lean
lake build
```

自分のパッケージだけを作り直すときは `lake clean yapss` を先に打つ。
**引数なしの `lake clean` は Mathlib のビルド成果物まで消す**ので使わない。
