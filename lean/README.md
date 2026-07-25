[← README](../README.md)

# `lean/` — PSS 停止性の形式証明

**PSS の停止性は無条件・`sorry` なしで形式証明されている。**

```lean
theorem PSS_terminates_unconditional : WellFounded stepRel
theorem no_infinite_expansion_holds :
    ¬ ∃ S : ℕ → PairSeq, (∀ i, ST_PS (S i)) ∧ ∀ i, step (S i) (S (i + 1))
```

いずれも [`Final.lean`](Final.lean) にあり、

```
#print axioms YAPSS.PSS_terminates_unconditional
  -- [propext, Classical.choice, Quot.sound]
```

すなわち `sorryAx` も名前付きの仮定も含まない。`lake build` はプロジェクト全体で通る。

証明は 3 段からなる。

1. ペア数列 $`M`$ を $`\mathrm{tr}`$ によって三分木記法 $`p_a(b)+c`$ の項へ写す
   （[`Term.md`](Term.md)）。項には添字優先の辞書式順序 $`\prec`$ を入れる。
2. 展開の 1 段はこの測度を真に減らす：$`\mathrm{tr}(M[n]) \prec \mathrm{tr}(M)`$
   （[`Decrease.md`](Decrease.md)）。したがって停止性は、標準形の像の上での
   $`\prec`$ の整礎性に還元される（[`Reduction.md`](Reduction.md)）。
3. その整礎性を、**順序数を使わず**、Buchholz の記法系への翻訳も使わずに示す。
   * **Bachmann 共終性** — $`M`$ より真に小さい標準形は、基本列の項 $`M[n]`$ の
     いずれかで上から抑えられる（[`Cofinality.md`](Cofinality.md)、[`ArgDom.md`](ArgDom.md)）
   * **反復帰納的集合** $`W_u`$ とその最小不動点帰納法を、ペア数列に対して直接立てる
     （[`Wset.md`](Wset.md)）

   この 2 つを合わせると整礎性が出る（[`Final.md`](Final.md)）。これは Buchholz (1987)
   §2 の方法である。そこでは Buchholz の記法系 $`\mathrm{OT}_B`$ の整礎性が、順序数への
   評価ではなく、集合 $`W_v`$ と基本列から**構文的に**得られている。上の経路はその方法を
   ペア数列へ直接移したものである。

順序数への評価写像も、Buchholz の $`\mathrm{OT}`$ への埋め込みも、係数優越条件も、
この経路のどこにも現れない。これは主張ではなく機械的に確認できる。`import Final` した
Lean の環境には定数 `Ordinal` がそもそも存在せず、Mathlib の順序数・濃度のモジュールは
1 つも import 閉包に入らない。

## モジュール

`<module>.lean` の隣に同名の `<module>.md` を置き、同じ証明を人間向けに書いてある。
両者は 1 対 1 に保つ。

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
