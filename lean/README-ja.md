[← README](../README-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# PSS 停止性の証明

ペア数列に展開の操作 $`M \Rightarrow N`$ が定まっている。**この操作は必ず止まる**、
すなわち標準形から始まる無限の展開列は存在しない、というのがここで示すことである。

証明は 6 章からなる。

**第 1 章。** ペア数列、その基本列 $`M[n]`$、標準形、展開 $`M \Rightarrow N`$ を定義する。

**第 2 章。** ペア数列 $`M`$ を $`p_a(b)+c`$ という三分木の記法の項 $`\mathrm{tr}(M)`$ へ
写す。項には添字優先の辞書式順序 $`\prec`$ を入れる。

**第 3 章。** 展開の 1 歩はこの測度を真に減らす：$`\mathrm{tr}(M[n]) \prec \mathrm{tr}(M)`$。
したがって、$`\prec`$ が標準形の像の上で整礎でありさえすれば、展開は止まる。

**第 4 章。** 第 5 章で使う道具を用意する。Cantor 標準形条件、$`\mathrm{tr}`$ が列辞書式順序への
順序同型であること、そして列の位置的不変量である。

**第 5 章。** その整礎性を、**順序数を使わず**、Buchholz の記法系への翻訳も使わずに示す。
使うのは次の 2 つである。

- **Bachmann 共終性** — $`M`$ より真に小さい標準形は、基本列の項 $`M[n]`$ のいずれかで
  上から抑えられる。
- **反復帰納的集合** $`W_u`$ — ペア数列の集合 $`W_u`$ を、$`u`$ より小さいレベルの $`W_v`$ から
  作った作用素の最小不動点として、$`u`$ について再帰的に定める。その最小性が与える帰納法に
  よって、どの標準形もある $`u`$ で $`W_u`$ に属することを示す。

この 2 つを合わせると整礎性が出る。これは Buchholz (1987) §2 の方法である。そこでは
Buchholz の記法系 $`\mathrm{OT}`$ の整礎性が、順序数への評価ではなく、集合 $`W_v`$ と
基本列から**構文的に**得られている。上の経路はその方法をペア数列へ直接移したものである。

**第 6 章。** 以上を合わせて、展開関係が整礎であること、無限の展開列が存在しないことを得る。

## 証明の構造

| | 何を示すか | 本文 |
|---|---|---|
| 第 1 章 | ペア数列 $`M`$、基本列 $`M[n]`$、標準形 $`\mathrm{ST\_PS}`$、展開 $`M \Rightarrow N`$ | [ペア数列システム](Pss-ja.md) |
| 第 2 章 | 記法 $`p_a(b)+c`$、順序 $`\prec`$、翻訳 $`\mathrm{tr}`$ | [三分岐記法](Term-ja.md) |
| 第 3 章 | 展開の分岐の分解と $`\mathrm{tr}(M[n]) \prec \mathrm{tr}(M)`$ | [測度の減少](Decrease-ja.md) |
| | $`\prec`$ が $`\mathrm{tr}`$ の像の上で整礎ならば展開は止まる | [停止性への還元](Reduction-ja.md) |
| 第 4 章 | Cantor 標準形条件 $`\mathrm{cnf}`$ と、コピー分解 $`\mathrm{sh}_d`$ / $`\mathrm{cp}_d`$ | [Cantor 標準形条件](Cnf-ja.md) [2](Cnf-2-ja.md) [3](Cnf-3-ja.md) |
| | $`\mathrm{tr}`$ が標準形の上で列辞書式順序への順序同型であること | [列辞書式順序](Seqlex-ja.md) [2](Seqlex-2-ja.md) |
| | 親子関係の接頭辞不変性と、位置的不変量 $`\mathrm{r1ok}`$ / $`\mathrm{z0ok}`$ | [列の不変量](Column-ja.md) [2](Column-2-ja.md) [3](Column-3-ja.md) [4](Column-4-ja.md) |
| 第 5 章 | $`N \prec M`$ ならばある $`n`$ で $`N \preceq M[n]`$ | [Bachmann 共終性](Cofinality-ja.md) [2](Cofinality-2-ja.md) [3](Cofinality-3-ja.md) |
| | 共終性を宿主に依らない核 $`\mathrm{ArgDomCore}`$ に還元し、それを証明する | [共終性の核](ArgDom-ja.md) [2](ArgDom-2-ja.md) [3](ArgDom-3-ja.md) [4](ArgDom-4-ja.md) [5](ArgDom-5-ja.md) |
| | 最小不動点 $`W_u`$ とその帰納法、どの標準形もある $`u`$ で $`W_u`$ に属すること | [反復帰納的集合](Wset-ja.md) [2](Wset-2-ja.md) [3](Wset-3-ja.md) [4](Wset-4-ja.md) |
| 第 6 章 | 展開関係の整礎性と、無限展開列の非存在 | [主定理](Final-ja.md) |

上から順に読める。各節は前の節までで示したことだけを使う。

数式の多い節は 2 以降に続く。GitHub は 1 ページの数式が一定量を超えるとそれ以降を
描画しないので、その手前で切ってある。

本文の編集方針は [`requirement.md`](requirement-ja.md)。

## Lean との対応

上の表の各節 `<module>.md` の**形式証明が同名の `<module>.lean` にある**。
たとえば [Bachmann 共終性](Cofinality-ja.md) [2](Cofinality-2-ja.md) [3](Cofinality-3-ja.md) の形式証明は
[`Cofinality.lean`](Cofinality.lean) である。

両者は 1 対 1 に対応する。`<module>.md` の見出し

```
## 定理: 標準形は空でない (T.stps_len_pos)
## 定義: 正規形上の順序 (D.Rnf)
```

の括弧の中は `<module>.lean` の宣言名であり（名前空間 `YAPSS.` は省く）、
節の並び順も `<module>.lean` の宣言の並び順と同じである。
一方にあって他方に無い命題・定義は無い。
