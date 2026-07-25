[← 目次](README.md)

# Cofinality — PSS Bachmann 共終性

標準形 $`M`$ より $`\prec`$ で真に小さい標準形 $`N`$ は、必ず $`M`$ の基本列 $`M[n]`$ のどれかで上から抑えられる
——これが PSS Bachmann 共終性であり、本証明の 2 本柱のうちの 1 本である。
本章は、この主張を桁優先辞書式順序 $`\prec_{\mathrm{lex}}`$ 上の組合せ的主張へ還元し、
[(D.oper)](Def.md#d-oper) の 4 つの分岐（長さ $`\le 1`$／末尾 $`(0,0)`$／親なし／それ以外）を個別に処理する。
最後の分岐はコピー幅 $`d_0`$ が $`0`$ か正かで分かれ、$`d_0=0`$ の側は本章で仮定なしに証明され、
$`d_0>0`$ の側は単一の残余命題 $`\mathrm{AscArgDom}`$ へ還元される（それは [`AscArg.md`](AscArg.md) で証明される）。

## 記法

本章で導入する Lean 名と本文の記法の対応。

| Lean | 本文 | 意味 |
|---|---|---|
| `sle M N` | $`M \preceq_{\mathrm{lex}} N`$ | $`M = N \vee M \prec_{\mathrm{lex}} N`$ |
| `SeqlexCofinality` | $`\mathrm{SeqCof}`$ | 共終性の $`\prec_{\mathrm{lex}}`$ 版（命題定数） |
| `AscCrux` | $`\mathrm{AscCrux}`$ | 上昇コピー分岐の要（命題定数） |
| `AscCrux1` | $`\mathrm{AscCrux}_1`$ | その先頭段を済ませた形（命題定数） |
| `AscArgDom` | $`\mathrm{AscArgDom}`$ | 本章が残す唯一の残余（命題定数） |

他の章で定義済みの記号は次のように書く。

| Lean | 本文 | 定義箇所 |
|---|---|---|
| `M.length` | $`\lvert M\rvert`$ | — |
| `p.1`, `p.2` | $`\pi_0 p`$, $`\pi_1 p`$ | — |
| `M.getD j (0,0)` | $`M\langle j\rangle`$ | — |
| `entry M i j` | $`M_{i,j}`$ | [(D.entry)](Def.md#d-entry) |
| `M⟦n⟧` | $`M[n]`$ | [(D.oper)](Def.md#d-oper) |
| `x <o y`, `x ≤o y` | $`x \prec y`$, $`x \preceq y`$ | [(D.olt)](Mechanized.md#d-olt), [(D.ole)](Mechanized.md#d-ole) |
| `translate M` | $`\mathrm{tr}\,M`$ | [(D.translate)](Mechanized.md#d-translate) |
| `pairlt p q` | $`p <_{\mathrm{p}} q`$ | [(D.pairlt)](Seqlex.md#d-pairlt) |
| `seqlex M N` | $`M \prec_{\mathrm{lex}} N`$ | [(D.seqlex)](Seqlex.md#d-seqlex) |
| `shiftr0 d X` | $`\sigma_d X`$ | [(D.shiftr0)](Wf.md#d-shiftr0) |
| `copies d B n` | $`\mathrm{cop}_d(B,n)`$ | [(D.copies)](Wf.md#d-copies) |
| `blockok d B` | $`\mathrm{blockok}(d,B)`$ | [(D.blockok)](Seqlex.md#d-blockok) |
| `steps1 M` | $`\mathrm{steps}_1 M`$ | [(D.steps1)](Seqlex.md#d-steps1) |
| `r1ok M` | $`\mathrm{r1ok}\,M`$ | [(D.r1ok)](Nrmstep.md#d-r1ok) |
| `z0ok M` | $`\mathrm{z0ok}\,M`$ | [(D.z0ok)](Nrmstep.md#d-z0ok) |
| `cnf t` | $`\mathrm{cnf}\,t`$ | [(D.cnf)](Wf.md#d-cnf) |

明示的に書き下すと

```math
p <_{\mathrm{p}} q \ :\iff\ \pi_0 p < \pi_0 q \ \vee\ (\pi_0 p = \pi_0 q \wedge \pi_1 p < \pi_1 q),
```

```math
M \prec_{\mathrm{lex}} N \ :\iff\
\begin{cases}
N \ne [] & (M = []) \\
\bot & (M \ne [],\ N = []) \\
p <_{\mathrm{p}} q \ \vee\ (p = q \wedge M' \prec_{\mathrm{lex}} N')
 & (M = p \mathbin{::} M',\ N = q \mathbin{::} N')
\end{cases}
```

```math
\sigma_d X := \mathrm{map}\,(\lambda p.\ (\pi_0 p + d,\ \pi_1 p))\,X,
\qquad
\mathrm{cop}_d(B,n) := \mathrm{flatMap}\,(\lambda k.\ \sigma_{k\cdot d}B)\,\mathrm{range}(n).
```

行 0 の値 $`a`$ を基準とする `takeWhile` / `dropWhile` を、[`Mechanized.md`](Mechanized.md) と同じく

```math
\mathrm{tw}_a L := L.\mathrm{takeWhile}\,(\lambda q.\ a < \pi_0 q),\qquad
  \mathrm{dw}_a L := L.\mathrm{dropWhile}\,(\lambda q.\ a < \pi_0 q)
```

と書く。さらに広義不等号版を

```math
\mathrm{tw}^{\ge}_a L := L.\mathrm{takeWhile}\,(\lambda q.\ a \le \pi_0 q),\qquad
  \mathrm{dw}^{\ge}_a L := L.\mathrm{dropWhile}\,(\lambda q.\ a \le \pi_0 q)
```

と書く。本文で用いる `takeWhile` / `dropWhile` の性質は次の 4 つに限る（$`p`$ は判定可能述語、$`L`$ はリスト）。

- (L1) $`\mathrm{takeWhile}\,p\,L \mathbin{+\!\!+} \mathrm{dropWhile}\,p\,L = L`$。
- (L2) $`x \in \mathrm{takeWhile}\,p\,L \ \Rightarrow\ p\,x`$。
- (L3) $`\mathrm{dropWhile}\,p\,L = z \mathbin{::} Z \ \Rightarrow\ \neg\,p\,z`$。
- (L4) $`\bigl(\forall x \in L,\ p\,x\bigr)\ \Rightarrow\ \mathrm{takeWhile}\,p\,L = L`$ かつ $`\mathrm{dropWhile}\,p\,L = []`$。

(L4) の連結版は [(T.takeWhile_append_all)](Mechanized.md#t-takeWhile_append_all)、
[(T.dropWhile_append_all)](Mechanized.md#t-dropWhile_append_all) である。
また連結の分解について、$`A \mathbin{+\!\!+} u = B \mathbin{+\!\!+} v`$ から、$`\lvert u\rvert = \lvert v\rvert`$ ならば
$`A = B \wedge u = v`$ が、$`\lvert A\rvert = \lvert B\rvert`$ ならば $`A = B \wedge u = v`$ が従う（連結の単射性）。

---

## Part 0 — $`\prec_{\mathrm{lex}}`$ の補助事実

[(T.olt_ST_iff_seqlex)](Seqlex.md#t-olt_ST_iff_seqlex) により、標準形の上では $`\mathrm{tr}`$ は
$`\prec_{\mathrm{lex}}`$ から $`\prec`$ への順序同型である。したがって共終性の主張全体を
ペア列上の組合せ的主張に置き換えられる。この節はそのために必要な $`\prec_{\mathrm{lex}}`$ の
リスト水準の性質を集める。

<a id="t-pairlt_trans"></a>
### 定理 $`<_{\mathrm{p}}`$ の推移律 (T.pairlt_trans)

**主張** $`p <_{\mathrm{p}} q`$ かつ $`q <_{\mathrm{p}} r`$ ならば $`p <_{\mathrm{p}} r`$。

**証明** [(D.pairlt)](Seqlex.md#d-pairlt) の定義を両仮定に展開して 4 通りに場合分けする。

1. $`\pi_0 p < \pi_0 q`$ かつ $`\pi_0 q < \pi_0 r`$：$`\mathbb{N}`$ の $`<`$ の推移律から $`\pi_0 p < \pi_0 r`$、第 1 選言。
2. $`\pi_0 p < \pi_0 q`$ かつ $`(\pi_0 q = \pi_0 r \wedge \pi_1 q < \pi_1 r)`$：$`\pi_0 p < \pi_0 q = \pi_0 r`$、第 1 選言。
3. $`(\pi_0 p = \pi_0 q \wedge \pi_1 p < \pi_1 q)`$ かつ $`\pi_0 q < \pi_0 r`$：$`\pi_0 p = \pi_0 q < \pi_0 r`$、第 1 選言。
4. $`(\pi_0 p = \pi_0 q \wedge \pi_1 p < \pi_1 q)`$ かつ $`(\pi_0 q = \pi_0 r \wedge \pi_1 q < \pi_1 r)`$：
   $`\pi_0 p = \pi_0 r`$ かつ $`\pi_1 p < \pi_1 q < \pi_1 r`$ より $`\pi_1 p < \pi_1 r`$、第 2 選言。

いずれの場合も $`p <_{\mathrm{p}} r`$。∎

<a id="t-seqlex_trans"></a>
### 定理 $`\prec_{\mathrm{lex}}`$ の推移律 (T.seqlex_trans)

**主張** $`A \prec_{\mathrm{lex}} B`$ かつ $`B \prec_{\mathrm{lex}} C`$ ならば $`A \prec_{\mathrm{lex}} C`$。

**証明** $`A`$ の構造（リストの構成子）に関する帰納法。$`B, C`$ は全称量化したまま動かす。帰納法の述語は

```math
\Phi(A) :\equiv \forall B\,C \in \mathrm{PairSeq},\
 \bigl(A \prec_{\mathrm{lex}} B \ \wedge\ B \prec_{\mathrm{lex}} C\bigr) \to A \prec_{\mathrm{lex}} C.
```

- **基底段 $`A = []`$。** [(D.seqlex)](Seqlex.md#d-seqlex) の第 1 式より、示すべき $`[] \prec_{\mathrm{lex}} C`$ は
  $`C \ne []`$ と同値である。$`C = []`$ と仮定すると、仮定 $`B \prec_{\mathrm{lex}} []`$ は、
  $`B = []`$ なら第 1 式より $`[] \ne []`$ で偽、$`B = b \mathbin{::} B'`$ なら第 2 式より $`\bot`$ である。
  いずれも矛盾するので $`C \ne []`$。よって $`\Phi([])`$。
- **帰納段 $`A = a \mathbin{::} A'`$。** 帰納法の仮定は $`\Phi(A')`$ である。
  $`B \prec_{\mathrm{lex}} C`$ と $`a \mathbin{::} A' \prec_{\mathrm{lex}} B`$ を仮定する。
  $`B = []`$ なら第 2 式より前者の仮定 $`a\mathbin{::}A' \prec_{\mathrm{lex}} []`$ が $`\bot`$ であるから矛盾。
  よって $`B = b \mathbin{::} B'`$。また $`C = []`$ ならば、$`B = b\mathbin{::}B'`$ が非空であるから
  [(D.seqlex)](Seqlex.md#d-seqlex) 第 2 式より仮定 $`B \prec_{\mathrm{lex}} []`$ が $`\bot`$ となり矛盾。
  よって $`C = c \mathbin{::} C'`$。[(T.seqlex_cons_cons)](Seqlex.md#t-seqlex_cons_cons) により

  ```math
  a \mathbin{::} A' \prec_{\mathrm{lex}} b \mathbin{::} B' \iff a <_{\mathrm{p}} b \ \vee\ (a = b \wedge A' \prec_{\mathrm{lex}} B'),
  ```
  ```math
  b \mathbin{::} B' \prec_{\mathrm{lex}} c \mathbin{::} C' \iff b <_{\mathrm{p}} c \ \vee\ (b = c \wedge B' \prec_{\mathrm{lex}} C').
  ```

  4 通りに場合分けし、いずれも $`a \mathbin{::} A' \prec_{\mathrm{lex}} c \mathbin{::} C'`$ を示す。

  1. $`a <_{\mathrm{p}} b`$ かつ $`b <_{\mathrm{p}} c`$：[(T.pairlt_trans)](#t-pairlt_trans) より $`a <_{\mathrm{p}} c`$、第 1 選言。
  2. $`a <_{\mathrm{p}} b`$ かつ $`b = c`$：$`a <_{\mathrm{p}} c`$、第 1 選言。
  3. $`a = b`$ かつ $`b <_{\mathrm{p}} c`$：$`a <_{\mathrm{p}} c`$、第 1 選言。
  4. $`a = b`$, $`A' \prec_{\mathrm{lex}} B'`$, $`b = c`$, $`B' \prec_{\mathrm{lex}} C'`$：$`a = c`$ であり、
     帰納法の仮定 $`\Phi(A')`$ を $`B := B'`$, $`C := C'`$ に適用して $`A' \prec_{\mathrm{lex}} C'`$。第 2 選言。

  よって $`\Phi(a \mathbin{::} A')`$。∎

<a id="d-sle"></a>
### 定義 広義桁優先辞書式順序 (D.sle)

```math
M \preceq_{\mathrm{lex}} N \ :\iff\ M = N \ \vee\ M \prec_{\mathrm{lex}} N .
```

<a id="t-sle_refl"></a>
### 定理 $`\preceq_{\mathrm{lex}}`$ の反射性 (T.sle_refl)

**主張** 任意の $`M \in \mathrm{PairSeq}`$ に対し $`M \preceq_{\mathrm{lex}} M`$。

**証明** [(D.sle)](#d-sle) の第 1 選言 $`M = M`$ が成り立つ。∎

<a id="t-seqlex_sle_trans"></a>
### 定理 $`\prec_{\mathrm{lex}}`$ と $`\preceq_{\mathrm{lex}}`$ の合成 (T.seqlex_sle_trans)

**主張** $`A \prec_{\mathrm{lex}} B`$ かつ $`B \preceq_{\mathrm{lex}} C`$ ならば $`A \prec_{\mathrm{lex}} C`$。

**証明** [(D.sle)](#d-sle) より $`B \preceq_{\mathrm{lex}} C`$ は $`B = C`$ または $`B \prec_{\mathrm{lex}} C`$ である。
前者なら仮定がそのまま $`A \prec_{\mathrm{lex}} C`$ を与える。
後者なら [(T.seqlex_trans)](#t-seqlex_trans) より $`A \prec_{\mathrm{lex}} C`$。∎

<a id="t-seqlex_append_mono"></a>
### 定理 大きい側の右延長 (T.seqlex_append_mono)

**主張** $`A \prec_{\mathrm{lex}} B`$ ならば、任意の $`C \in \mathrm{PairSeq}`$ に対し
$`A \prec_{\mathrm{lex}} B \mathbin{+\!\!+} C`$。

**証明** $`A`$ の構造に関する帰納法。帰納法の述語は

```math
\Phi(A) :\equiv \forall B \in \mathrm{PairSeq},\ A \prec_{\mathrm{lex}} B \to
 \forall C \in \mathrm{PairSeq},\ A \prec_{\mathrm{lex}} B \mathbin{+\!\!+} C.
```

- **基底段 $`A = []`$。** 仮定 $`[] \prec_{\mathrm{lex}} B`$ は $`B \ne []`$ を意味する
  （[(D.seqlex)](Seqlex.md#d-seqlex) 第 1 式）。$`B = []`$ は除かれるので $`B = b \mathbin{::} B'`$、
  よって $`B \mathbin{+\!\!+} C = b \mathbin{::} (B' \mathbin{+\!\!+} C) \ne []`$ であり
  $`[] \prec_{\mathrm{lex}} B \mathbin{+\!\!+} C`$。
- **帰納段 $`A = a \mathbin{::} A'`$。** 帰納法の仮定は $`\Phi(A')`$。
  仮定 $`a \mathbin{::} A' \prec_{\mathrm{lex}} B`$ より $`B \ne []`$（$`B = []`$ なら第 2 式で $`\bot`$）、
  $`B = b \mathbin{::} B'`$ とおく。[(T.seqlex_cons_cons)](Seqlex.md#t-seqlex_cons_cons) より
  $`a <_{\mathrm{p}} b`$ または $`(a = b \wedge A' \prec_{\mathrm{lex}} B')`$。
  $`B \mathbin{+\!\!+} C = b \mathbin{::} (B' \mathbin{+\!\!+} C)`$ であるから、
  - $`a <_{\mathrm{p}} b`$ のときは第 1 選言により
    $`a \mathbin{::} A' \prec_{\mathrm{lex}} b \mathbin{::} (B' \mathbin{+\!\!+} C)`$、
  - $`a = b`$, $`A' \prec_{\mathrm{lex}} B'`$ のときは帰納法の仮定 $`\Phi(A')`$ を $`B := B'`$, $`C := C`$ に適用して
    $`A' \prec_{\mathrm{lex}} B' \mathbin{+\!\!+} C`$ を得、第 2 選言により結論。

  よって $`\Phi(a \mathbin{::} A')`$。∎

<a id="t-sle_append_mono"></a>
### 定理 $`\preceq_{\mathrm{lex}}`$ の右延長 (T.sle_append_mono)

**主張** $`A \preceq_{\mathrm{lex}} B`$ ならば、任意の $`C`$ に対し $`A \preceq_{\mathrm{lex}} B \mathbin{+\!\!+} C`$。

**証明** [(D.sle)](#d-sle) により 2 つに分ける。

- $`A = B`$ のとき。$`C`$ の構成子で分ける。$`C = []`$ なら $`B \mathbin{+\!\!+} [] = B = A`$ で第 1 選言。
  $`C = c \mathbin{::} C'`$ なら $`C \ne []`$ であるから
  [(T.seqlex_prefix)](Seqlex.md#t-seqlex_prefix) を $`u := A`$, $`v := C`$ に適用して
  $`A \prec_{\mathrm{lex}} A \mathbin{+\!\!+} C = B \mathbin{+\!\!+} C`$、第 2 選言。
- $`A \prec_{\mathrm{lex}} B`$ のとき。[(T.seqlex_append_mono)](#t-seqlex_append_mono) より
  $`A \prec_{\mathrm{lex}} B \mathbin{+\!\!+} C`$、第 2 選言。∎

<a id="t-seqlex_snoc_cases"></a>
### 定理 末尾 1 列を落とす場合分け (T.seqlex_snoc_cases)

**主張** $`N \prec_{\mathrm{lex}} D \mathbin{+\!\!+} [lp]`$ ならば

```math
N \preceq_{\mathrm{lex}} D
\qquad\text{または}\qquad
\exists\, q,\ S,\ \bigl(N = D \mathbin{+\!\!+} q \mathbin{::} S \ \wedge\ q <_{\mathrm{p}} lp\bigr).
```

**証明** $`D`$ の構造に関する帰納法（$`lp`$, $`N`$ は全称量化したまま動かす）。帰納法の述語は

```math
\Phi(D) :\equiv \forall lp \in \mathbb{N}\times\mathbb{N},\ \forall N \in \mathrm{PairSeq},\
 N \prec_{\mathrm{lex}} D \mathbin{+\!\!+} [lp] \to
 \Bigl(N \preceq_{\mathrm{lex}} D \ \vee\ \exists q\,S,\ N = D \mathbin{+\!\!+} q\mathbin{::}S \wedge q <_{\mathrm{p}} lp\Bigr).
```

- **基底段 $`D = []`$。** $`D \mathbin{+\!\!+} [lp] = [lp]`$ である。
  - $`N = []`$ のとき：[(T.sle_refl)](#t-sle_refl) より $`[] \preceq_{\mathrm{lex}} []= D`$、第 1 の場合。
  - $`N = q \mathbin{::} S`$ のとき：[(T.seqlex_cons_cons)](Seqlex.md#t-seqlex_cons_cons) より
    $`q <_{\mathrm{p}} lp`$ または $`(q = lp \wedge S \prec_{\mathrm{lex}} [])`$。
    後者の $`S \prec_{\mathrm{lex}} []`$ は、$`S = []`$ なら $`[] \ne []`$ で偽、$`S`$ が非空なら $`\bot`$ で偽。
    よって $`q <_{\mathrm{p}} lp`$ であり、$`N = [] \mathbin{+\!\!+} q \mathbin{::} S`$ だから第 2 の場合。
- **帰納段 $`D = d \mathbin{::} D'`$。** 帰納法の仮定は $`\Phi(D')`$。
  $`D \mathbin{+\!\!+} [lp] = d \mathbin{::} (D' \mathbin{+\!\!+} [lp])`$ である。
  - $`N = []`$ のとき：$`D = d\mathbin{::}D' \ne []`$ であるから $`[] \prec_{\mathrm{lex}} D`$、
    よって $`N \preceq_{\mathrm{lex}} D`$、第 1 の場合。
  - $`N = q \mathbin{::} S`$ のとき：[(T.seqlex_cons_cons)](Seqlex.md#t-seqlex_cons_cons) より
    $`q <_{\mathrm{p}} d`$ または $`(q = d \wedge S \prec_{\mathrm{lex}} D' \mathbin{+\!\!+} [lp])`$。
    - $`q <_{\mathrm{p}} d`$：第 1 選言により $`q\mathbin{::}S \prec_{\mathrm{lex}} d\mathbin{::}D' = D`$、
      よって $`N \preceq_{\mathrm{lex}} D`$。
    - $`q = d`$ かつ $`S \prec_{\mathrm{lex}} D' \mathbin{+\!\!+} [lp]`$：帰納法の仮定 $`\Phi(D')`$ を
      $`lp := lp`$, $`N := S`$ に適用する。
      - $`S \preceq_{\mathrm{lex}} D'`$ が出た場合：$`S = D'`$ なら $`N = d\mathbin{::}D' = D`$ で第 1 選言、
        $`S \prec_{\mathrm{lex}} D'`$ なら $`d = d`$ と第 2 選言により
        $`d\mathbin{::}S \prec_{\mathrm{lex}} d\mathbin{::}D'`$。いずれも $`N \preceq_{\mathrm{lex}} D`$。
      - $`S = D' \mathbin{+\!\!+} q'\mathbin{::}S' \wedge q' <_{\mathrm{p}} lp`$ が出た場合：
        $`N = d \mathbin{::} (D' \mathbin{+\!\!+} q'\mathbin{::}S') = (d\mathbin{::}D') \mathbin{+\!\!+} q'\mathbin{::}S' = D \mathbin{+\!\!+} q'\mathbin{::}S'`$ であり、第 2 の場合。

  よって $`\Phi(d \mathbin{::} D')`$。∎

---

## Part 1 — $`\prec_{\mathrm{lex}}`$ への還元

<a id="d-SeqlexCofinality"></a>
### 定義 共終性の $`\prec_{\mathrm{lex}}`$ 版 (D.SeqlexCofinality)

```math
\mathrm{SeqCof} \ :\equiv\ \forall M, N \in \mathrm{PairSeq},\
 \bigl(M \in \mathrm{ST\_PS} \wedge N \in \mathrm{ST\_PS} \wedge N \prec_{\mathrm{lex}} M\bigr)
 \to \exists n,\ \bigl(1 \le n \ \wedge\ N \preceq_{\mathrm{lex}} M[n]\bigr)
```

（[(D.ST_PS)](Def.md#d-ST_PS), [(D.oper)](Def.md#d-oper)）。これは命題定数（`Prop` 型の定義）であり、
以降「$`\mathrm{SeqCof}`$ を仮定すると」の形で用いる。

<a id="t-pss_cofinality_of_seqlex"></a>
### 定理 $`\prec_{\mathrm{lex}}`$ 版からの還元 (T.pss_cofinality_of_seqlex)

**主張** $`\mathrm{SeqCof}`$ が成り立つとする。$`M, N \in \mathrm{ST\_PS}`$ かつ
$`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$ ならば

```math
\exists n,\ \bigl(1 \le n \ \wedge\ \mathrm{tr}\,N \preceq \mathrm{tr}(M[n])\bigr).
```

**証明** まず $`N \ne M`$ である。実際 $`N = M`$ ならば $`\mathrm{tr}\,N \prec \mathrm{tr}\,N`$ となり
[(T.olt_irrefl)](Mechanized.md#t-olt_irrefl) に矛盾する。
$`N, M \in \mathrm{ST\_PS}`$ と $`N \ne M`$ に
[(T.olt_ST_iff_seqlex)](Seqlex.md#t-olt_ST_iff_seqlex) を適用すると

```math
\mathrm{tr}\,N \prec \mathrm{tr}\,M \iff N \prec_{\mathrm{lex}} M
```

であるから、仮定より $`N \prec_{\mathrm{lex}} M`$。
$`\mathrm{SeqCof}`$（[(D.SeqlexCofinality)](#d-SeqlexCofinality)）を適用して
$`1 \le n`$ かつ $`N \preceq_{\mathrm{lex}} M[n]`$ なる $`n`$ を得る。この $`n`$ を答とする。
[(D.sle)](#d-sle) により 2 つに分ける。

- $`N = M[n]`$ のとき：$`\mathrm{tr}\,N = \mathrm{tr}(M[n])`$ であるから
  [(D.ole)](Mechanized.md#d-ole) の第 2 選言により $`\mathrm{tr}\,N \preceq \mathrm{tr}(M[n])`$。
- $`N \prec_{\mathrm{lex}} M[n]`$ のとき：$`N = M[n]`$ か否かでさらに分ける。
  - $`N = M[n]`$ ならば上と同じく第 2 選言。
  - $`N \ne M[n]`$ ならば、[(D.ST_PS)](Def.md#d-ST_PS) の規則 (oper) を $`M \in \mathrm{ST\_PS}`$ と
    $`1 \le n`$ に適用して $`M[n] \in \mathrm{ST\_PS}`$ を得る。
    [(T.olt_ST_iff_seqlex)](Seqlex.md#t-olt_ST_iff_seqlex) を $`N`$, $`M[n]`$, $`N \ne M[n]`$ に適用し、
    その同値の右から左への向き（$`\prec_{\mathrm{lex}} \Rightarrow \prec`$）により
    $`\mathrm{tr}\,N \prec \mathrm{tr}(M[n])`$、第 1 選言。∎

---

## Part 2 — $`M[n]`$ の退化分岐

[(D.oper)](Def.md#d-oper) は $`M`$ の形により 4 つの分岐をもつ。この節ではそのうち
(a) $`\lvert M\rvert \le 1`$、(b) 末尾が $`(0,0)`$、(c) 親が一意に存在しない、の 3 つを処理する。

<a id="t-entry_zero"></a>
### 定理 行 0 成分 (T.entry_zero)

**主張** $`M_{0,j} = \pi_0 (M\langle j\rangle)`$。

**証明** [(D.entry)](Def.md#d-entry) の定義 $`M_{i,j} = \mathrm{if}\ i = 0\ \mathrm{then}\ \pi_0(M\langle j\rangle)\ \mathrm{else}\ \pi_1(M\langle j\rangle)`$
において $`i = 0`$ であるから条件 $`0 = 0`$ が真、`then` 側が選ばれる。∎

<a id="t-entry_one"></a>
### 定理 行 1 成分 (T.entry_one)

**主張** $`M_{1,j} = \pi_1 (M\langle j\rangle)`$。

**証明** [(D.entry)](Def.md#d-entry) において $`i = 1`$ であり、$`1 \ne 0`$ であるから条件が偽、
`else` 側が選ばれる。∎

<a id="t-dropLast_snoc_getD"></a>
### 定理 末尾 1 列の切り出し (T.dropLast_snoc_getD)

**主張** $`M \ne []`$ ならば
```math
\mathrm{dropLast}\,M \mathbin{+\!\!+} \bigl[\,M\langle \lvert M\rvert - 1\rangle\,\bigr] = M .
```

**証明** $`M \ne []`$ より $`0 < \lvert M\rvert`$、したがって $`\lvert M\rvert - 1 < \lvert M\rvert`$ である。
`getD` の定義（添字が範囲内なら該当要素、範囲外なら既定値）より

```math
M\langle \lvert M\rvert - 1\rangle = M[\lvert M\rvert-1] = \mathrm{getLast}\,M
```

である（最後の等号は $`\mathrm{getLast}\,M = M[\lvert M\rvert - 1]`$ という `getLast` の定義）。
よって示すべき式は $`\mathrm{dropLast}\,M \mathbin{+\!\!+} [\mathrm{getLast}\,M] = M`$ であり、
これは非空リストの標準的な分解である。∎

<a id="t-seqlex_cof_short"></a>
### 定理 分岐 self の共終性 (T.seqlex_cof_short)

**主張** $`\lvert M\rvert - 1 = 0`$ かつ $`N \prec_{\mathrm{lex}} M`$ ならば
$`\exists n,\ (1 \le n \wedge N \preceq_{\mathrm{lex}} M[n])`$。

**証明** $`n := 1`$ とする。$`1 \le 1`$ である。
[(T.oper_eq_self_of_short)](Mechanized.md#t-oper_eq_self_of_short) を $`n := 1`$ と
$`\lvert M\rvert - 1 = 0`$ に適用して $`M[1] = M`$。
よって仮定 $`N \prec_{\mathrm{lex}} M`$ はそのまま $`N \prec_{\mathrm{lex}} M[1]`$ であり、
[(D.sle)](#d-sle) の第 2 選言により $`N \preceq_{\mathrm{lex}} M[1]`$。∎

<a id="t-seqlex_cof_zero"></a>
### 定理 分岐 zero の共終性 (T.seqlex_cof_zero)

**主張** $`1 < \lvert M\rvert`$、$`M_{0,\lvert M\rvert-1} = 0 \wedge M_{1,\lvert M\rvert-1} = 0`$、
$`N \prec_{\mathrm{lex}} M`$ ならば $`\exists n,\ (1 \le n \wedge N \preceq_{\mathrm{lex}} M[n])`$。

**証明** $`lp := M\langle \lvert M\rvert - 1\rangle`$ とおく。

1. $`M \ne []`$。$`M = []`$ なら $`\lvert M\rvert = 0`$ となり $`1 < 0`$ で矛盾。
2. $`lp = (0,0)`$。[(T.entry_zero)](#t-entry_zero) より $`\pi_0 lp = M_{0,\lvert M\rvert-1} = 0`$、
   [(T.entry_one)](#t-entry_one) より $`\pi_1 lp = M_{1,\lvert M\rvert-1} = 0`$。
   対は成分で決まるから $`lp = (0,0)`$。
3. $`\mathrm{dropLast}\,M \mathbin{+\!\!+} [lp] = M`$。[(T.dropLast_snoc_getD)](#t-dropLast_snoc_getD)。
4. $`M[1] = \mathrm{dropLast}\,M`$。$`1 < \lvert M\rvert`$ より $`\lvert M\rvert - 1 \ne 0`$ であるから
   [(T.oper_eq_pred_of_zero)](Mechanized.md#t-oper_eq_pred_of_zero) が使えて $`M[1] = \mathrm{Pred}\,M`$。
   [(D.Pred)](Def.md#d-Pred) は $`\mathrm{Pred}\,M = \mathrm{if}\ \lvert M\rvert \le 1\ \mathrm{then}\ M\ \mathrm{else}\ \mathrm{dropLast}\,M`$
   であり、$`1 < \lvert M\rvert`$ より条件 $`\lvert M\rvert \le 1`$ は偽、よって $`\mathrm{Pred}\,M = \mathrm{dropLast}\,M`$。

$`n := 1`$ とする。3 により仮定は $`N \prec_{\mathrm{lex}} \mathrm{dropLast}\,M \mathbin{+\!\!+} [lp]`$ と書ける。
[(T.seqlex_snoc_cases)](#t-seqlex_snoc_cases) を $`D := \mathrm{dropLast}\,M`$ に適用して 2 つに分ける。

- $`N \preceq_{\mathrm{lex}} \mathrm{dropLast}\,M`$：4 によりこれが $`N \preceq_{\mathrm{lex}} M[1]`$ である。
- $`N = \mathrm{dropLast}\,M \mathbin{+\!\!+} q \mathbin{::} S`$ かつ $`q <_{\mathrm{p}} lp`$：
  2 より $`lp = (0,0)`$ であるから $`q <_{\mathrm{p}} (0,0)`$、すなわち
  $`\pi_0 q < 0`$ または $`(\pi_0 q = 0 \wedge \pi_1 q < 0)`$。
  $`\mathbb{N}`$ には $`0`$ より小さい元がないからいずれも偽であり、この場合は起こらない。∎

<a id="t-hasParent_last_ST_PS"></a>
### 定理 分岐 noparent は $`\mathrm{ST\_PS}`$ 上で空 (T.hasParent_last_ST_PS)

**主張** $`M \in \mathrm{ST\_PS}`$、$`0 < \lvert M\rvert`$、
$`\neg\bigl(M_{0,\lvert M\rvert-1} = 0 \wedge M_{1,\lvert M\rvert-1} = 0\bigr)`$ ならば

```math
\mathrm{hasParent}\bigl(M,\ \mathrm{idx}_1(M, \lvert M\rvert-1),\ \lvert M\rvert-1\bigr)
```

（[(D.hasParent)](Def.md#d-hasParent), [(D.idx1)](Def.md#d-idx1)）。

**証明** [(T.hp_last)](Nrmstep.md#t-hp_last) を適用する。その仮定は
$`\mathrm{blockok}(0,M)`$、$`\mathrm{z0ok}\,M`$、$`0 < \lvert M\rvert`$、
$`M\langle \lvert M\rvert-1\rangle \ne (0,0)`$ の 4 つである。
第 1 は [(T.blockok_ST_PS)](Seqlex.md#t-blockok_ST_PS)、第 2 は
[(T.z0ok_ST_PS)](Nrmstep.md#t-z0ok_ST_PS)、第 3 は仮定である。
第 4 は次のように示す。$`M\langle \lvert M\rvert-1\rangle = (0,0)`$ と仮定すると、
[(T.entry_zero)](#t-entry_zero) より $`M_{0,\lvert M\rvert-1} = \pi_0(0,0) = 0`$、
[(T.entry_one)](#t-entry_one) より $`M_{1,\lvert M\rvert-1} = \pi_1(0,0) = 0`$ となり、
本定理の第 3 仮定に矛盾する。∎

したがって $`\mathrm{ST\_PS}`$ の元に対しては [(D.oper)](Def.md#d-oper) の分岐 (c) は起こらない。

---

## Part 3 — 分岐 bad：コピー敷き詰めの要への還元

<a id="t-sle_append_cancel"></a>
### 定理 共通前部分の消去 (T.sle_append_cancel)

**主張** $`A \mathbin{+\!\!+} u \preceq_{\mathrm{lex}} A \mathbin{+\!\!+} v \iff u \preceq_{\mathrm{lex}} v`$。

**証明** [(D.sle)](#d-sle) を両辺に展開すると、示すべきは

```math
\bigl(A \mathbin{+\!\!+} u = A \mathbin{+\!\!+} v \ \vee\ A \mathbin{+\!\!+} u \prec_{\mathrm{lex}} A \mathbin{+\!\!+} v\bigr)
\iff \bigl(u = v \ \vee\ u \prec_{\mathrm{lex}} v\bigr).
```

第 2 選言どうしは [(T.seqlex_append_cancel)](Seqlex.md#t-seqlex_append_cancel) により同値である。
第 1 選言について、$`\Rightarrow`$ 向きは連結の左消去（$`A\mathbin{+\!\!+}u = A\mathbin{+\!\!+}v \Rightarrow u = v`$）、
$`\Leftarrow`$ 向きは $`u = v`$ から $`A\mathbin{+\!\!+}u = A\mathbin{+\!\!+}v`$ が従うことによる。∎

<a id="t-getD_append_right'"></a>
### 定理 右側成分の取り出し (T.getD_append_right')

**主張** $`(A \mathbin{+\!\!+} B)\langle \lvert A\rvert + i\rangle = B\langle i\rangle`$。

**証明** `getD` は `getElem?` に既定値を与えたものである。
$`\lvert A\rvert \le \lvert A\rvert + i`$ であるから、連結の添字取得の規則により

```math
(A \mathbin{+\!\!+} B)[\lvert A\rvert + i]^? = B[(\lvert A\rvert + i) - \lvert A\rvert]^? = B[i]^? .
```

両辺に既定値 $`(0,0)`$ を与えれば主張を得る。∎

<a id="t-getD_last_of_snoc"></a>
### 定理 snoc の末尾 (T.getD_last_of_snoc)

**主張** $`(D \mathbin{+\!\!+} [lp])\bigl\langle \lvert D \mathbin{+\!\!+} [lp]\rvert - 1\bigr\rangle = lp`$。

**証明** $`\lvert D \mathbin{+\!\!+} [lp]\rvert = \lvert D\rvert + 1`$ であるから
$`\lvert D \mathbin{+\!\!+} [lp]\rvert - 1 = \lvert D\rvert`$。
$`\lvert D\rvert \le \lvert D\rvert`$ であるから連結の添字取得の規則により
$`(D \mathbin{+\!\!+} [lp])[\lvert D\rvert]^? = [lp][0]^? = lp`$。∎

<a id="t-nextrel1_snd_succ"></a>
### 定理 末尾列における行 1 の $`+1`$ 規律 (T.nextrel1_snd_succ)

**主張** $`\mathrm{r1ok}\,M`$ かつ $`j_0 \to^M_1 j_1`$（[(D.nextrel1)](Def.md#d-nextrel1)）ならば

```math
M_{1,j_1} = M_{1,j_0} + 1 .
```

**証明** [(D.nextrel1)](Def.md#d-nextrel1) の 6 条件を
$`h_{j_0} : j_0 < \lvert M\rvert`$、$`h_{j_1} : j_1 < \lvert M\rvert`$、$`h_{<} : j_0 < j_1`$、
$`h_{\mathrm{inc}} : M_{1,j_0} < M_{1,j_1}`$、$`h_{\le 0} : j_0 \le^M_0 j_1`$、
$`h_{\min} : \forall j,\ (j_0 < j \wedge j \le^M_0 j_1) \to M_{1,j_1} \le M_{1,j}`$ と名付ける。

**(i) 行 0 の祖先鎖の最初の 1 歩を取る。**
$`h_{\le 0}`$ の第 3 成分は $`\mathrm{ReflTransGen}(\to^M_0)\,j_0\,j_1`$ である。
反射推移閉包の先頭場合分け（$`\mathrm{ReflTransGen}\ r\ a\ b`$ ならば $`a = b`$、または
ある $`c`$ が存在して $`r\,a\,c`$ かつ $`\mathrm{ReflTransGen}\ r\ c\ b`$）を適用する。
$`j_0 = j_1`$ は $`h_{<}`$（$`j_0 < j_1`$）に矛盾する。
よってある $`c`$ について $`j_0 \to^M_0 c`$ かつ $`\mathrm{ReflTransGen}(\to^M_0)\,c\,j_1`$ である。
[(D.nextrel0)](Def.md#d-nextrel0) の条件 3, 2 より $`j_0 < c`$ かつ $`c < \lvert M\rvert`$、
したがって [(D.le0)](Def.md#d-le0) より $`c \le^M_0 j_1`$。

**(ii) 上からの評価。** $`h_{\min}`$ を $`j := c`$ に適用する（前提 $`j_0 < c`$ と $`c \le^M_0 j_1`$ は (i)）。

```math
M_{1,j_1} \le M_{1,c}. \tag{1}
```

**(iii) $`c`$ の行 0 の値は正。** $`j_0 \to^M_0 c`$ の条件 4 は $`M_{0,j_0} < M_{0,c}`$ であり、
[(T.entry_zero)](#t-entry_zero) によりこれは $`\pi_0(M\langle j_0\rangle) < \pi_0(M\langle c\rangle)`$。
よって $`0 < \pi_0(M\langle c\rangle)`$。

**(iv) $`\mathrm{r1ok}`$ を $`c`$ に適用する。** [(D.r1ok)](Nrmstep.md#d-r1ok) は

```math
\forall j < \lvert M\rvert,\ 0 < \pi_0(M\langle j\rangle) \to
\exists k,\ \Bigl(k < j \ \wedge\ \pi_0(M\langle k\rangle) + 1 = \pi_0(M\langle j\rangle)
 \ \wedge\ \bigl(\forall l,\ k < l < j \to \pi_0(M\langle j\rangle) \le \pi_0(M\langle l\rangle)\bigr)
 \ \wedge\ \pi_1(M\langle j\rangle) \le \pi_1(M\langle k\rangle) + 1\Bigr)
```

である。$`j := c`$（$`c < \lvert M\rvert`$ は (i)、$`0 < \pi_0(M\langle c\rangle)`$ は (iii)）に適用して
$`k`$ を得る。

**(v) $`k = j_0`$。** $`k \to^M_0 c`$ を [(D.nextrel0)](Def.md#d-nextrel0) の 5 条件で確認する。
条件 1 は $`k < c < \lvert M\rvert`$、条件 2 は $`c < \lvert M\rvert`$、条件 3 は $`k < c`$、
条件 4 は $`\pi_0(M\langle k\rangle) + 1 = \pi_0(M\langle c\rangle)`$ より
$`M_{0,k} < M_{0,c}`$（[(T.entry_zero)](#t-entry_zero)）、
条件 5 は $`\mathrm{r1ok}`$ の第 3 成分そのもの（[(T.entry_zero)](#t-entry_zero) で $`M_{0,\cdot}`$ に読み替える）。
一方 (i) より $`j_0 \to^M_0 c`$ でもあるから、
[(T.nextrel0_unique)](Nrmstep.md#t-nextrel0_unique) より $`k = j_0`$。

**(vi) 下からの評価。** $`\mathrm{r1ok}`$ の第 4 成分は $`\pi_1(M\langle c\rangle) \le \pi_1(M\langle k\rangle)+1`$
であり、(v) と [(T.entry_one)](#t-entry_one) により

```math
M_{1,c} \le M_{1,j_0} + 1. \tag{2}
```

**(vii) 結論。** $`h_{\mathrm{inc}}`$、(1)、(2) を並べると

```math
M_{1,j_0} < M_{1,j_1} \le M_{1,c} \le M_{1,j_0} + 1 .
```

$`\mathbb{N}`$ において $`a < b`$ かつ $`b \le a+1`$ ならば $`b = a+1`$ であるから
$`M_{1,j_1} = M_{1,j_0}+1`$。∎

<a id="t-oper_bad_blocks_all"></a>
### 定理 分岐 bad の分解（$`n`$ について一様） (T.oper_bad_blocks_all)

**主張** $`1 < \lvert M\rvert`$、$`\mathrm{steps}_1 M`$、$`\mathrm{r1ok}\,M`$、
$`\neg\bigl(M_{0,\lvert M\rvert-1}=0 \wedge M_{1,\lvert M\rvert-1}=0\bigr)`$、
$`\mathrm{hasParent}(M, \mathrm{idx}_1(M,\lvert M\rvert-1), \lvert M\rvert-1)`$ を仮定する。
このとき $`G, R \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0 \in \mathbb{N}`$、$`lp \in \mathbb{N}\times\mathbb{N}`$ が存在して

1. $`M = \bigl(G \mathbin{+\!\!+} ((v_0,w_0)\mathbin{::}R)\bigr) \mathbin{+\!\!+} [lp]`$、
2. $`\forall n \ge 1,\ M[n] = G \mathbin{+\!\!+} \mathrm{cop}_{d_0}\bigl((v_0,w_0)\mathbin{::}R,\ n\bigr)`$、
3. $`\forall x \in R,\ v_0 < \pi_0 x`$、
4. $`v_0 < \pi_0 lp`$、
5. 次のいずれか：
   - $`d_0 = 0 \ \wedge\ \pi_1 lp = 0 \ \wedge\ \pi_0 lp = v_0+1`$、
   - $`0 < d_0 \ \wedge\ \pi_1 lp = w_0+1 \ \wedge\ \pi_0 lp = v_0+d_0 \ \wedge\ \lvert G\rvert \to^M_1 (\lvert M\rvert-1)`$。

**証明** 以下 $`\mathrm{blk} := (v_0,w_0)\mathbin{::}R`$、$`j_1 := \lvert M\rvert-1`$、$`i_1 := \mathrm{idx}_1(M,j_1)`$ と書く。

**(a) $`n = 1`$ での分解を取る。**
[(T.oper_bad_blocks)](Mechanized.md#t-oper_bad_blocks) を $`n := 1`$ に適用する。その結論は
$`G, v_0, w_0, R, d_0, lp`$ の存在であって

- $`M = (G \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} [lp]`$、
- $`M[1] = G \mathbin{+\!\!+} \mathrm{flatMap}(\lambda k.\ \mathrm{map}\,(\lambda p.\ (\pi_0 p + k d_0, \pi_1 p))\,\mathrm{blk})\,\mathrm{range}(1)`$、
- $`\forall x\in R,\ v_0 < \pi_0 x`$、$`v_0 < \pi_0 lp`$、
- $`\bigl(d_0 = 0 \wedge i_1 = 0\bigr) \ \vee\ \bigl(0<d_0 \wedge w_0 < \pi_1 lp \wedge \pi_0 lp = v_0+d_0 \wedge \lvert G\rvert \to^M_1 j_1\bigr)`$、
- $`\lvert G\rvert \to^M_{i_1} j_1`$（[(D.nextR)](Def.md#d-nextR)）

を満たすもの。これで主張 1, 3, 4 が得られた。以下、この分解の選言を $`\mathrm{disj}`$、
最後の $`\lvert G\rvert \to^M_{i_1} j_1`$ を $`h_{nR}`$ と呼ぶ。

**(b) 落とされる列は末尾列である。**
主張 1 の右辺に [(T.getD_last_of_snoc)](#t-getD_last_of_snoc) を $`D := G \mathbin{+\!\!+} \mathrm{blk}`$ で適用して

```math
lp = M\langle j_1\rangle . \tag{$\ast$}
```

**(c) ブロック根の位置。** 主張 1 と連結の結合律より $`M = G \mathbin{+\!\!+} (\mathrm{blk} \mathbin{+\!\!+} [lp])`$
であるから、$`\lvert M\rvert = \lvert G\rvert + (\lvert R\rvert + 2)`$ であり、
[(T.getD_append_right')](#t-getD_append_right') を $`i := 0`$ に適用して

```math
M\langle \lvert G\rvert\rangle = (\mathrm{blk} \mathbin{+\!\!+} [lp])\langle 0\rangle = (v_0,w_0). \tag{$\ast\ast$}
```

**(d) 主張 5 の証明。** $`\mathrm{disj}`$ の 2 つの場合に分ける。

**場合 1：$`d_0 = 0`$ かつ $`i_1 = 0`$。**

*$`\pi_1 lp = 0`$。* [(D.idx1)](Def.md#d-idx1) より
$`i_1 = \mathrm{if}\ 0 < M_{1,j_1}\ \mathrm{then}\ 1\ \mathrm{else}\ 0`$ である。
条件 $`0 < M_{1,j_1}`$ が真ならば $`i_1 = 1`$ となり $`i_1 = 0`$ に矛盾する（$`1 \ne 0`$）。
よって条件は偽、すなわち $`M_{1,j_1} = 0`$。$`(\ast)`$ と [(T.entry_one)](#t-entry_one) より
$`\pi_1 lp = \pi_1(M\langle j_1\rangle) = M_{1,j_1} = 0`$。

*$`\pi_0 lp = v_0 + 1`$。* $`i_1 = 0`$ と [(T.nextR_zero_iff)](Nrmstep.md#t-nextR_zero_iff) により
$`h_{nR}`$ は $`\lvert G\rvert \to^M_0 j_1`$ である。(c) より $`j_1 = \lvert G\rvert + 1 + \lvert R\rvert`$ であり、
特に $`\lvert G\rvert + 1 \le j_1 < \lvert M\rvert`$。次の 3 つを合わせる。

- $`\mathrm{steps}_1 M`$ に [(T.steps1_iff)](Seqlex.md#t-steps1_iff) を適用し $`j := \lvert G\rvert`$
  （$`\lvert G\rvert + 1 < \lvert M\rvert`$ は $`\lvert M\rvert = \lvert G\rvert+\lvert R\rvert+2`$ による）とすると
  ```math
  M_{0,\lvert G\rvert+1} \le M_{0,\lvert G\rvert}+1 .
  ```
- $`(\ast\ast)`$ と [(T.entry_zero)](#t-entry_zero) より $`M_{0,\lvert G\rvert} = v_0`$。
- $`M_{0,j_1} \le M_{0,\lvert G\rvert+1}`$。実際 $`\lvert G\rvert+1 = j_1`$ ならば等号、
  $`\lvert G\rvert+1 < j_1`$ ならば $`\lvert G\rvert \to^M_0 j_1`$ の条件 5
  （[(D.nextrel0)](Def.md#d-nextrel0)）を $`j := \lvert G\rvert+1`$ に適用して得られる。

$`(\ast)`$ と [(T.entry_zero)](#t-entry_zero) より $`\pi_0 lp = M_{0,j_1}`$ であるから、上の 3 つより

```math
\pi_0 lp = M_{0,j_1} \le M_{0,\lvert G\rvert+1} \le M_{0,\lvert G\rvert}+1 = v_0+1 .
```

一方、主張 4 より $`v_0 < \pi_0 lp`$。$`\mathbb{N}`$ において $`v_0 < x \le v_0+1`$ ならば $`x = v_0+1`$ であるから
$`\pi_0 lp = v_0+1`$。これで主張 5 の第 1 の場合が成立する。

**場合 2：$`0<d_0`$、$`w_0 < \pi_1 lp`$、$`\pi_0 lp = v_0+d_0`$、$`\lvert G\rvert \to^M_1 j_1`$。**
[(T.nextrel1_snd_succ)](#t-nextrel1_snd_succ) を $`\mathrm{r1ok}\,M`$ と $`\lvert G\rvert \to^M_1 j_1`$ に適用して
$`M_{1,j_1} = M_{1,\lvert G\rvert}+1`$。
$`(\ast)`$ と [(T.entry_one)](#t-entry_one) より左辺は $`\pi_1 lp`$、
$`(\ast\ast)`$ と [(T.entry_one)](#t-entry_one) より $`M_{1,\lvert G\rvert} = \pi_1(v_0,w_0) = w_0`$。
よって $`\pi_1 lp = w_0+1`$ であり、主張 5 の第 2 の場合が成立する。

**(e) 主張 2 の証明。** $`n \ge 1`$ を任意に取る。
[(T.oper_bad_blocks)](Mechanized.md#t-oper_bad_blocks) をこの $`n`$ に適用し、
その分解を $`G', v_0', w_0', R', d_0', lp'`$、選言を $`\mathrm{disj}'`$、
最後の条件を $`h_{nR}' : \lvert G'\rvert \to^M_{i_1} j_1`$ とする。

*$`\lvert G'\rvert = \lvert G\rvert`$。* 仮定 $`\mathrm{hasParent}(M,i_1,j_1)`$ は
$`\exists!\,j_0,\ j_0 \to^M_{i_1} j_1`$（[(D.hasParent)](Def.md#d-hasParent)）であるから、
その一意性条項を $`h_{nR}'`$ と $`h_{nR}`$ に適用して $`\lvert G'\rvert = \lvert G\rvert`$。

*分解の一致。* 2 つの分解から
$`(G' \mathbin{+\!\!+} \mathrm{blk}') \mathbin{+\!\!+} [lp'] = (G \mathbin{+\!\!+} \mathrm{blk}) \mathbin{+\!\!+} [lp]`$
（ただし $`\mathrm{blk}' := (v_0',w_0')\mathbin{::}R'`$）。
$`\lvert [lp']\rvert = \lvert [lp]\rvert = 1`$ であるから連結の単射性により
$`G' \mathbin{+\!\!+} \mathrm{blk}' = G \mathbin{+\!\!+} \mathrm{blk}`$ かつ $`[lp'] = [lp]`$、すなわち $`lp' = lp`$。
さらに $`\lvert G'\rvert = \lvert G\rvert`$ であるから、再び連結の単射性により
$`G' = G`$ かつ $`\mathrm{blk}' = \mathrm{blk}`$。
$`\mathrm{blk}' = \mathrm{blk}`$ の先頭要素を比べて $`(v_0',w_0') = (v_0,w_0)`$、
すなわち $`v_0' = v_0`$ かつ $`w_0' = w_0`$、末尾を比べて $`R' = R`$。

*$`d_0' = d_0`$。* まず補助事実として、任意の $`e`$ について

```math
e \to^M_1 j_1 \ \Longrightarrow\ i_1 \ne 0 \tag{$\dagger$}
```

を示す。$`e \to^M_1 j_1`$ の条件 4 は $`M_{1,e} < M_{1,j_1}`$ であるから $`0 < M_{1,j_1}`$、
よって [(D.idx1)](Def.md#d-idx1) の条件が真となり $`i_1 = 1 \ne 0`$。
$`\mathrm{disj}`$ と $`\mathrm{disj}'`$ の 4 通りを見る。

- ともに第 1 の場合：$`d_0 = 0`$ かつ $`d_0' = 0`$。
- $`\mathrm{disj}`$ が第 1（$`i_1 = 0`$）、$`\mathrm{disj}'`$ が第 2（$`\lvert G\rvert \to^M_1 j_1`$）：
  $`(\dagger)`$ より $`i_1 \ne 0`$ となり矛盾。この場合は起こらない。
- $`\mathrm{disj}`$ が第 2（$`\lvert G\rvert \to^M_1 j_1`$）、$`\mathrm{disj}'`$ が第 1（$`i_1 = 0`$）：
  $`(\dagger)`$ より $`i_1 \ne 0`$ となり矛盾。この場合も起こらない。
- ともに第 2 の場合：$`\pi_0 lp = v_0+d_0`$ かつ $`\pi_0 lp' = v_0+d_0'`$ であり $`lp' = lp`$ だから
  $`v_0+d_0 = v_0+d_0'`$、よって $`d_0' = d_0`$。

*結論。* $`n`$ に対する分解の第 2 成分は

```math
M[n] = G \mathbin{+\!\!+} \mathrm{flatMap}\bigl(\lambda k.\ \mathrm{map}\,(\lambda p.\ (\pi_0 p + k d_0,\ \pi_1 p))\,\mathrm{blk}\bigr)\,\mathrm{range}(n)
```

である（$`G'=G`$, $`\mathrm{blk}'=\mathrm{blk}`$, $`d_0'=d_0`$ を代入した）。
一方 [(D.copies)](Wf.md#d-copies) と [(D.shiftr0)](Wf.md#d-shiftr0) より

```math
\mathrm{cop}_{d_0}(\mathrm{blk},n)
 = \mathrm{flatMap}\bigl(\lambda k.\ \sigma_{k d_0}\mathrm{blk}\bigr)\,\mathrm{range}(n)
 = \mathrm{flatMap}\bigl(\lambda k.\ \mathrm{map}\,(\lambda p.\ (\pi_0 p + k d_0,\ \pi_1 p))\,\mathrm{blk}\bigr)\,\mathrm{range}(n)
```

であるから、両者は定義により同一の列である。よって主張 2 が成り立つ。∎

---

## Part 4 — 要の $`d_0 = 0`$ 側（完全一致コピー）

$`d_0 = 0`$ のとき $`\sigma_0`$ は恒等写像である（[(T.shiftr0_zero)](Wf.md#t-shiftr0_zero)）から、
$`M[n]`$ はブロック $`\mathrm{blk} = (v_0,w_0)\mathbin{::}R`$ をそのまま $`n`$ 回並べた列
$`G \mathbin{+\!\!+} \mathrm{blk} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} \mathrm{blk}`$ である。
この場合に用いる性質は $`\mathrm{cnf}`$（[(D.cnf)](Wf.md#d-cnf), [(T.cnf_ST_PS)](Wf.md#t-cnf_ST_PS)）である。
$`\mathrm{cnf}\bigl(\mathsf{P}(a,b,\mathsf{P}(e,f,g))\bigr)`$ は（$`\mathsf{P}`$, $`\mathsf{Z}`$ は
[(D.Three)](Mechanized.md#d-Three) の構成子）
$`\neg\bigl(\mathsf{P}(a,b,\mathsf{Z}) \prec \mathsf{P}(e,f,\mathsf{Z})\bigr)`$ を含む
（[(T.cnf_P_P)](Wf.md#t-cnf_P_P)）から、深さ $`v_0`$ で $`\mathrm{blk}`$ の根の直後に来る列
$`y`$ の作る項 $`\mathsf{P}(\pi_1 y, \mathrm{tr}\,R', \cdot)`$ は
$`\mathsf{P}(w_0, \mathrm{tr}\,R, \cdot)`$ を超えない。
これを $`\pi_1 y < w_0`$ / $`\pi_1 y = w_0`$ の 2 通りに分けて使うのが
[(T.copy_dom_zero)](#t-copy_dom_zero) である。

<a id="t-seqlex_splice"></a>
### 定理 接合 (T.seqlex_splice)

**主張** $`A \prec_{\mathrm{lex}} B`$ とし、$`U`$ が

```math
U = [] \quad\text{または}\quad \forall x \in B,\ \mathrm{headI}\,U <_{\mathrm{p}} x
```

を満たすとする。このとき任意の $`C`$ に対し
$`A \mathbin{+\!\!+} U \prec_{\mathrm{lex}} B \mathbin{+\!\!+} C`$。

**証明** $`A`$ の構造に関する帰納法（$`B, U, C`$ は全称量化したまま動かす）。帰納法の述語は

```math
\Phi(A) :\equiv \forall B,\ A \prec_{\mathrm{lex}} B \to \forall U,\
 \bigl(U = [] \vee \forall x\in B,\ \mathrm{headI}\,U <_{\mathrm{p}} x\bigr) \to
 \forall C,\ A \mathbin{+\!\!+} U \prec_{\mathrm{lex}} B \mathbin{+\!\!+} C.
```

- **基底段 $`A = []`$。** $`[] \prec_{\mathrm{lex}} B`$ より $`B \ne []`$、$`B = b_0 \mathbin{::} B'`$ とおく。
  $`B \mathbin{+\!\!+} C = b_0 \mathbin{::} (B' \mathbin{+\!\!+} C)`$ である。
  - $`U = []`$：$`[] \mathbin{+\!\!+} [] = []`$ であり、
    $`b_0 \mathbin{::} (B'\mathbin{+\!\!+}C) \ne []`$ だから $`[] \prec_{\mathrm{lex}} B\mathbin{+\!\!+}C`$。
  - $`U = u \mathbin{::} U'`$：$`[] \mathbin{+\!\!+} U = u \mathbin{::} U'`$ である。
    $`U \ne []`$ であるから仮定の第 1 選言は成立せず、第 2 選言
    $`\forall x\in B,\ \mathrm{headI}\,U <_{\mathrm{p}} x`$ が成り立つ。
    $`\mathrm{headI}(u\mathbin{::}U') = u`$ であり $`b_0 \in B`$ であるから $`u <_{\mathrm{p}} b_0`$。
    [(T.seqlex_cons_cons)](Seqlex.md#t-seqlex_cons_cons) の第 1 選言により
    $`u\mathbin{::}U' \prec_{\mathrm{lex}} b_0 \mathbin{::} (B'\mathbin{+\!\!+}C)`$。
- **帰納段 $`A = a \mathbin{::} A'`$。** 帰納法の仮定は $`\Phi(A')`$。
  $`a\mathbin{::}A' \prec_{\mathrm{lex}} B`$ より $`B \ne []`$、$`B = b_0\mathbin{::}B'`$ とおく。
  [(T.seqlex_cons_cons)](Seqlex.md#t-seqlex_cons_cons) より
  $`a <_{\mathrm{p}} b_0`$ または $`(a = b_0 \wedge A' \prec_{\mathrm{lex}} B')`$。
  $`A \mathbin{+\!\!+} U = a \mathbin{::} (A' \mathbin{+\!\!+} U)`$、
  $`B \mathbin{+\!\!+} C = b_0 \mathbin{::} (B' \mathbin{+\!\!+} C)`$ である。
  - $`a <_{\mathrm{p}} b_0`$：第 1 選言により結論。
  - $`a = b_0`$ かつ $`A' \prec_{\mathrm{lex}} B'`$：$`U`$ についての仮定を $`B'`$ 用に落とす。
    $`U = []`$ ならそのまま。そうでなければ $`\forall x\in B = b_0\mathbin{::}B'`$ が成り立つので、
    特に $`\forall x \in B'`$（$`x \in B'`$ ならば $`x \in b_0\mathbin{::}B'`$）。
    帰納法の仮定 $`\Phi(A')`$ を $`B := B'`$, $`U := U`$, $`C := C`$ に適用して
    $`A' \mathbin{+\!\!+} U \prec_{\mathrm{lex}} B' \mathbin{+\!\!+} C`$、
    第 2 選言（$`a = b_0`$ と合わせて）により結論。

  よって $`\Phi(a\mathbin{::}A')`$。∎

<a id="t-split_block"></a>
### 定理 基準深さでのブロック分割 (T.split_block)

**主張** $`\forall x \in R,\ v_0 < \pi_0 x`$ かつ
$`\bigl(Y = [] \vee \neg\,(v_0 < \pi_0(\mathrm{headI}\,Y))\bigr)`$ ならば

```math
\mathrm{tw}_{v_0}(R \mathbin{+\!\!+} Y) = R \qquad\text{かつ}\qquad \mathrm{dw}_{v_0}(R \mathbin{+\!\!+} Y) = Y .
```

**証明** 述語 $`p := (\lambda q.\ v_0 < \pi_0 q)`$ とおく。第 1 仮定は $`\forall x\in R,\ p\,x`$ である。

- $`Y = []`$ のとき：$`R \mathbin{+\!\!+} [] = R`$ であり、(L4) より
  $`\mathrm{takeWhile}\,p\,R = R`$、$`\mathrm{dropWhile}\,p\,R = [] = Y`$。
- $`Y = y \mathbin{::} Y'`$ のとき：第 2 仮定の第 1 選言は成立しないので $`\neg\,p\,y`$ である。
  [(T.takeWhile_append_all)](Mechanized.md#t-takeWhile_append_all) より
  $`\mathrm{takeWhile}\,p\,(R\mathbin{+\!\!+}Y) = R \mathbin{+\!\!+} \mathrm{takeWhile}\,p\,Y`$ であり、
  $`\neg\,p\,y`$ より $`\mathrm{takeWhile}\,p\,(y\mathbin{::}Y') = []`$、よって全体は $`R`$。
  [(T.dropWhile_append_all)](Mechanized.md#t-dropWhile_append_all) より
  $`\mathrm{dropWhile}\,p\,(R\mathbin{+\!\!+}Y) = \mathrm{dropWhile}\,p\,Y`$ であり、
  $`\neg\,p\,y`$ より $`\mathrm{dropWhile}\,p\,(y\mathbin{::}Y') = y\mathbin{::}Y' = Y`$。∎

<a id="t-copy_dom_zero"></a>
### 定理 完全一致コピーによる支配 (T.copy_dom_zero)

**主張** 任意の $`d \in \mathbb{N}`$ について、次が成り立つ。
$`Y, R \in \mathrm{PairSeq}`$、$`v_0, w_0 \in \mathbb{N}`$ が

- $`\lvert Y\rvert \le d`$、
- $`\mathrm{blockok}\bigl(v_0,\ (v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}Y)\bigr)`$、
- $`\forall x\in R,\ v_0 < \pi_0 x`$、
- $`Y = [] \ \vee\ \neg\,(v_0 < \pi_0(\mathrm{headI}\,Y))`$、
- $`\mathrm{cnf}\bigl(\mathrm{tr}((v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}Y))\bigr)`$

を満たすならば、$`\exists m,\ \bigl(1 \le m \ \wedge\ Y \preceq_{\mathrm{lex}} \mathrm{cop}_0((v_0,w_0)\mathbin{::}R,\ m)\bigr)`$。

**証明** $`d`$ に関する自然数の帰納法。$`Y, v_0, w_0, R`$ は全称量化したまま動かす。帰納法の述語は

```math
\Phi(d) :\equiv \forall Y, v_0, w_0, R,\ \bigl(\text{上の 5 条件}\bigr) \to
 \exists m,\ \bigl(1 \le m \wedge Y \preceq_{\mathrm{lex}} \mathrm{cop}_0((v_0,w_0)\mathbin{::}R, m)\bigr).
```

以下 $`\mathrm{blk} := (v_0,w_0)\mathbin{::}R`$ と書く。

**基底段 $`d = 0`$。** $`\lvert Y\rvert \le 0`$ より $`Y = []`$。$`m := 1`$ とすると
[(T.copies_one)](Wf.md#t-copies_one) より $`\mathrm{cop}_0(\mathrm{blk},1) = \mathrm{blk} \ne []`$ であるから
$`[] \prec_{\mathrm{lex}} \mathrm{cop}_0(\mathrm{blk},1)`$、よって
$`Y \preceq_{\mathrm{lex}} \mathrm{cop}_0(\mathrm{blk},1)`$。

**帰納段 $`d+1`$。** 帰納法の仮定は $`\Phi(d)`$ である。$`Y`$ の構成子で分ける。

$`Y = []`$ のときは基底段と同じく $`m := 1`$ でよい。以下 $`Y = y \mathbin{::} Y'`$ とする。

**(i) $`\pi_0 y = v_0`$。** $`\mathrm{blockok}`$ の第 2 成分（[(D.blockok)](Seqlex.md#d-blockok)）は
$`\forall p \in \mathrm{blk}\mathbin{+\!\!+}(y\mathbin{::}Y')`$ の形で $`v_0 \le \pi_0 p`$ を与える。
$`y`$ はこの列の要素だから $`v_0 \le \pi_0 y`$。
第 4 仮定は $`Y \ne []`$ より $`\neg\,(v_0 < \pi_0(\mathrm{headI}\,Y)) = \neg\,(v_0 < \pi_0 y)`$、
すなわち $`\pi_0 y \le v_0`$。よって $`\pi_0 y = v_0`$、すなわち $`y = (v_0, \pi_1 y)`$。

**(ii) $`Y'`$ を分割する。** $`R' := \mathrm{tw}_{v_0}Y'`$、$`Y'' := \mathrm{dw}_{v_0}Y'`$ とおく。
(L1) より $`R' \mathbin{+\!\!+} Y'' = Y'`$。
(L2) より $`\forall x\in R',\ v_0 < \pi_0 x`$。
(L3) より $`Y'' = []`$ または $`\neg\,(v_0 < \pi_0(\mathrm{headI}\,Y''))`$。

**(iii) 2 つの翻訳の形。** [(T.translate_block_append)](Mechanized.md#t-translate_block_append) は
「$`\forall x\in A,\ a < \pi_0 x`$ かつ $`T = [] \vee \neg(a<\pi_0(\mathrm{headI}\,T))`$ ならば
$`\mathrm{tr}(((a,b)\mathbin{::}A)\mathbin{+\!\!+}T) = \mathsf{P}(b, \mathrm{tr}\,A, \mathrm{tr}\,T)`$」である。
これを 2 度使う。

- $`((v_0,\pi_1 y)\mathbin{::}R')\mathbin{+\!\!+}Y'' = (v_0,\pi_1 y)\mathbin{::}(R'\mathbin{+\!\!+}Y'') = (v_0,\pi_1 y)\mathbin{::}Y' = y\mathbin{::}Y'`$
  であるから（(i), (ii)）、
  ```math
  \mathrm{tr}(y\mathbin{::}Y') = \mathsf{P}\bigl(\pi_1 y,\ \mathrm{tr}\,R',\ \mathrm{tr}\,Y''\bigr).
  ```
- $`\mathrm{blk}\mathbin{+\!\!+}(y\mathbin{::}Y') = (v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}(y\mathbin{::}Y'))`$ であるから、
  ```math
  \mathrm{tr}\bigl((v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}(y\mathbin{::}Y'))\bigr)
   = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathrm{tr}(y\mathbin{::}Y')\bigr).
  ```

**(iv) $`\mathrm{cnf}`$ の展開。** 第 5 仮定は (iii) により

```math
\mathrm{cnf}\Bigl(\mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathsf{P}(\pi_1 y, \mathrm{tr}\,R', \mathrm{tr}\,Y'')\bigr)\Bigr)
```

であり、[(T.cnf_P_P)](Wf.md#t-cnf_P_P) によりこれは次の 3 条件の連言と同値：

```math
\mathrm{cnf}(\mathrm{tr}\,R),\qquad
h_{\mathrm{sib}} : \neg\bigl(\mathsf{P}(w_0,\mathrm{tr}\,R,\mathsf{Z}) \prec \mathsf{P}(\pi_1 y,\mathrm{tr}\,R',\mathsf{Z})\bigr),\qquad
c_{\mathrm{tail}} : \mathrm{cnf}\bigl(\mathsf{P}(\pi_1 y,\mathrm{tr}\,R',\mathrm{tr}\,Y'')\bigr).
```

**(v) $`\pi_1 y \le w_0`$。** $`w_0 < \pi_1 y`$ と仮定すると
[(T.olt_P_P)](Mechanized.md#t-olt_P_P) の第 1 選言により
$`\mathsf{P}(w_0,\mathrm{tr}\,R,\mathsf{Z}) \prec \mathsf{P}(\pi_1 y,\mathrm{tr}\,R',\mathsf{Z})`$ となり
$`h_{\mathrm{sib}}`$ に矛盾する。

**(vi) 場合 $`\pi_1 y < w_0`$。** $`m := 1`$ とする。
[(T.copies_one)](Wf.md#t-copies_one) より $`\mathrm{cop}_0(\mathrm{blk},1) = \mathrm{blk} = (v_0,w_0)\mathbin{::}R`$。
(i) より $`y = (v_0,\pi_1 y)`$ であり $`\pi_0 y = v_0 = \pi_0 (v_0,w_0)`$、$`\pi_1 y < w_0`$ だから
$`y <_{\mathrm{p}} (v_0,w_0)`$。[(T.seqlex_cons_cons)](Seqlex.md#t-seqlex_cons_cons) の第 1 選言より
$`y\mathbin{::}Y' \prec_{\mathrm{lex}} \mathrm{blk}`$。

**(vii) 場合 $`\pi_1 y = w_0`$。** このとき $`y = (v_0,w_0)`$ である。

*引数の比較。* $`\mathrm{tr}\,R \prec \mathrm{tr}\,R'`$ と仮定すると、
[(T.olt_P_P)](Mechanized.md#t-olt_P_P) の第 2 選言（$`w_0 = \pi_1 y`$ かつ $`\mathrm{tr}\,R \prec \mathrm{tr}\,R'`$）により
$`h_{\mathrm{sib}}`$ に矛盾する。よって

```math
h_{\mathrm{nolt}} : \neg\bigl(\mathrm{tr}\,R \prec \mathrm{tr}\,R'\bigr). 
```

*ブロック条件の継承。* [(T.split_block)](#t-split_block) を $`R`$, $`Y = y\mathbin{::}Y'`$ に適用すると
$`\mathrm{tw}_{v_0}(R\mathbin{+\!\!+}Y) = R`$、$`\mathrm{dw}_{v_0}(R\mathbin{+\!\!+}Y) = Y`$。したがって

- [(T.blockok_tail)](Seqlex.md#t-blockok_tail) を第 2 仮定に適用して
  $`\mathrm{blockok}(v_0,\ \mathrm{dw}_{v_0}(R\mathbin{+\!\!+}Y)) = \mathrm{blockok}(v_0,\ y\mathbin{::}Y')`$、
- [(T.blockok_arg)](Seqlex.md#t-blockok_arg) を第 2 仮定に適用して
  $`\mathrm{blockok}(v_0+1,\ \mathrm{tw}_{v_0}(R\mathbin{+\!\!+}Y)) = \mathrm{blockok}(v_0+1,\ R)`$、
- $`y = (v_0,\pi_1 y)`$ より上の第 1 の結論は $`\mathrm{blockok}(v_0, (v_0,\pi_1 y)\mathbin{::}Y')`$ であるから、
  再び [(T.blockok_arg)](Seqlex.md#t-blockok_arg) を適用して
  $`\mathrm{blockok}(v_0+1,\ \mathrm{tw}_{v_0}Y') = \mathrm{blockok}(v_0+1,\ R')`$。

*場合 $`R' = R`$（ブロックの再現）。* このとき

```math
y\mathbin{::}Y' = (v_0,w_0)\mathbin{::}(R'\mathbin{+\!\!+}Y'') = (v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}Y'')
 = \mathrm{blk}\mathbin{+\!\!+}Y'' .
```

帰納法の仮定 $`\Phi(d)`$ を $`Y := Y''`$, $`v_0, w_0, R`$ に適用する。5 条件を確認する。

- $`\lvert Y''\rvert \le d`$：$`\lvert R'\rvert + \lvert Y''\rvert = \lvert Y'\rvert`$（(ii)）であり、
  $`\lvert y\mathbin{::}Y'\rvert = \lvert Y'\rvert+1 \le d+1`$ より $`\lvert Y'\rvert \le d`$。よって
  $`\lvert Y''\rvert \le \lvert Y'\rvert \le d`$。
- $`\mathrm{blockok}(v_0,\ (v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}Y''))`$：これは上式により
  $`\mathrm{blockok}(v_0,\ y\mathbin{::}Y')`$ と同じ命題であり、既に得ている。
- $`\forall x\in R,\ v_0<\pi_0 x`$：第 3 仮定。
- $`Y'' = [] \vee \neg(v_0<\pi_0(\mathrm{headI}\,Y''))`$：(ii)。
- $`\mathrm{cnf}(\mathrm{tr}((v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}Y'')))`$：これは上式と (iii) により
  $`\mathrm{cnf}(\mathsf{P}(\pi_1 y,\mathrm{tr}\,R',\mathrm{tr}\,Y''))`$ と同じ命題であり、
  (iv) の $`c_{\mathrm{tail}}`$ である。

こうして $`m \ge 1`$ と $`Y'' \preceq_{\mathrm{lex}} \mathrm{cop}_0(\mathrm{blk},m)`$ を得る。答を $`m+1`$ とする。
[(T.copies_succ_cons)](Wf.md#t-copies_succ_cons) と
[(T.shiftr0_zero)](Wf.md#t-shiftr0_zero)（$`\sigma_0`$ は恒等）より

```math
\mathrm{cop}_0(\mathrm{blk},m+1) = (v_0,w_0)\mathbin{::}\bigl(R \mathbin{+\!\!+} \mathrm{cop}_0(\mathrm{blk},m)\bigr)
 = \mathrm{blk} \mathbin{+\!\!+} \mathrm{cop}_0(\mathrm{blk},m).
```

したがって示すべきは
$`\mathrm{blk}\mathbin{+\!\!+}Y'' \preceq_{\mathrm{lex}} \mathrm{blk}\mathbin{+\!\!+}\mathrm{cop}_0(\mathrm{blk},m)`$
であり、[(T.sle_append_cancel)](#t-sle_append_cancel) によりこれは
$`Y'' \preceq_{\mathrm{lex}} \mathrm{cop}_0(\mathrm{blk},m)`$ と同値、これは得たものである。

*場合 $`R' \ne R`$（引数が真に小さい）。* [(T.seqlex_total)](Seqlex.md#t-seqlex_total) より
$`R' = R`$、$`R' \prec_{\mathrm{lex}} R`$、$`R \prec_{\mathrm{lex}} R'`$ のいずれかである。
第 1 はこの場合の仮定 $`R' \ne R`$ に反する。第 3 の場合、
[(T.seqlex_imp_olt)](Seqlex.md#t-seqlex_imp_olt) を深さ $`v_0+1`$、$`\mathrm{blockok}(v_0+1,R)`$、
$`\mathrm{blockok}(v_0+1,R')`$ に適用して $`\mathrm{tr}\,R \prec \mathrm{tr}\,R'`$ となり $`h_{\mathrm{nolt}}`$ に矛盾。
よって $`R' \prec_{\mathrm{lex}} R`$。

答を $`m := 2`$ とする。$`2 = 1+1`$ と
[(T.copies_succ_cons)](Wf.md#t-copies_succ_cons)、[(T.shiftr0_zero)](Wf.md#t-shiftr0_zero)、
[(T.copies_one)](Wf.md#t-copies_one) より

```math
\mathrm{cop}_0(\mathrm{blk},2) = (v_0,w_0)\mathbin{::}\bigl(R \mathbin{+\!\!+} \mathrm{blk}\bigr).
```

$`y = (v_0,w_0)`$ であるから、[(T.seqlex_cons_cons)](Seqlex.md#t-seqlex_cons_cons) の第 2 選言により
$`Y' \prec_{\mathrm{lex}} R \mathbin{+\!\!+} \mathrm{blk}`$ を示せばよい。
$`Y' = R' \mathbin{+\!\!+} Y''`$ であるから、[(T.seqlex_splice)](#t-seqlex_splice) を
$`A := R'`$, $`B := R`$, $`U := Y''`$, $`C := \mathrm{blk}`$ に適用する。
$`U`$ についての仮定は次のように確認する：(ii) より $`Y'' = []`$ か、
$`\neg(v_0 < \pi_0(\mathrm{headI}\,Y''))`$ すなわち $`\pi_0(\mathrm{headI}\,Y'') \le v_0`$。
後者の場合、$`x \in R`$ なら第 3 仮定より $`v_0 < \pi_0 x`$ だから
$`\pi_0(\mathrm{headI}\,Y'') \le v_0 < \pi_0 x`$、よって $`\mathrm{headI}\,Y'' <_{\mathrm{p}} x`$。
[(T.seqlex_splice)](#t-seqlex_splice) より
$`R'\mathbin{+\!\!+}Y'' \prec_{\mathrm{lex}} R\mathbin{+\!\!+}\mathrm{blk}`$、これが求めるものである。

以上で $`\Phi(d+1)`$ が示された。∎

---

## Part 5 — 要の $`d_0 = 0`$ 側の解消

<a id="t-copies_zero_succ"></a>
### 定理 幅 0 コピーの後方展開 (T.copies_zero_succ)

**主張** $`\mathrm{cop}_0(B,\ m+1) = \mathrm{cop}_0(B,\ m) \mathbin{+\!\!+} B`$。

**証明** [(D.copies)](Wf.md#d-copies) より
$`\mathrm{cop}_0(B,n) = \mathrm{flatMap}(\lambda k.\ \sigma_{k\cdot 0}B)\,\mathrm{range}(n)`$。
$`\mathrm{range}(m+1) = \mathrm{range}(m) \mathbin{+\!\!+} [m]`$ であり、$`\mathrm{flatMap}`$ は連結を連結に写すから

```math
\mathrm{cop}_0(B,m+1)
 = \mathrm{flatMap}(\lambda k.\ \sigma_{k\cdot 0}B)\,\mathrm{range}(m) \mathbin{+\!\!+} \sigma_{m\cdot 0}B
 = \mathrm{cop}_0(B,m) \mathbin{+\!\!+} \sigma_0 B .
```

$`m \cdot 0 = 0`$ であり [(T.shiftr0_zero)](Wf.md#t-shiftr0_zero) より $`\sigma_0 B = B`$。∎

<a id="t-crux_zero"></a>
### 定理 完全一致コピー分岐の要 (T.crux_zero)

**主張** $`\bigl(G \mathbin{+\!\!+} ((v_0,w_0)\mathbin{::}R)\bigr) \mathbin{+\!\!+} q\mathbin{::}S \in \mathrm{ST\_PS}`$、
$`\forall x\in R,\ v_0<\pi_0 x`$、$`\pi_1 lp = 0`$、$`\pi_0 lp = v_0+1`$、$`q <_{\mathrm{p}} lp`$ ならば

```math
\exists m,\ \bigl(1 \le m \ \wedge\ q\mathbin{::}S \preceq_{\mathrm{lex}} \mathrm{cop}_0((v_0,w_0)\mathbin{::}R,\ m)\bigr).
```

**証明** $`\mathrm{blk} := (v_0,w_0)\mathbin{::}R`$、$`N := (G\mathbin{+\!\!+}\mathrm{blk})\mathbin{+\!\!+}q\mathbin{::}S`$ と書く。

**(i) $`\pi_0 q \le v_0`$。** $`q <_{\mathrm{p}} lp`$ は
$`\pi_0 q < \pi_0 lp`$ または $`(\pi_0 q = \pi_0 lp \wedge \pi_1 q < \pi_1 lp)`$ である。
第 1 の場合は $`\pi_0 q < v_0+1`$ より $`\pi_0 q \le v_0`$。
第 2 の場合は $`\pi_1 q < \pi_1 lp = 0`$ となり $`\mathbb{N}`$ で不可能であるから、この場合は起こらない。

**(ii) $`\pi_0 q < v_0`$ のとき。** $`m := 1`$ とする。
[(T.copies_one)](Wf.md#t-copies_one) より $`\mathrm{cop}_0(\mathrm{blk},1) = \mathrm{blk}`$ であり、
$`\pi_0 q < v_0`$ より $`q <_{\mathrm{p}} (v_0,w_0)`$、よって
[(T.seqlex_cons_cons)](Seqlex.md#t-seqlex_cons_cons) の第 1 選言により
$`q\mathbin{::}S \prec_{\mathrm{lex}} \mathrm{blk}`$。以下 $`\pi_0 q = v_0`$ とする。

**(iii) 継続部を深さ $`v_0`$ で切る。**
$`Y := \mathrm{tw}^{\ge}_{v_0}(q\mathbin{::}S)`$、$`V := \mathrm{dw}^{\ge}_{v_0}(q\mathbin{::}S)`$ とおく。
(L1) より $`Y \mathbin{+\!\!+} V = q\mathbin{::}S`$。
$`v_0 \le \pi_0 q`$ であるから `takeWhile` の先頭段が通り
$`Y = q \mathbin{::} \mathrm{tw}^{\ge}_{v_0}S`$、特に $`\pi_0(\mathrm{headI}\,Y) = \pi_0 q = v_0`$。
(L2) より $`\forall x\in Y,\ v_0 \le \pi_0 x`$。
(L3) より、$`V = []`$ であるか、$`V = z\mathbin{::}Z`$ と書けて $`\neg(v_0 \le \pi_0 z)`$、すなわち $`\pi_0 z < v_0`$。

**(iv) $`N`$ の 2 通りの分解。** (iii) より

```math
N = (G\mathbin{+\!\!+}\mathrm{blk})\mathbin{+\!\!+}(Y\mathbin{+\!\!+}V)
 = \bigl(G\mathbin{+\!\!+}(\mathrm{blk}\mathbin{+\!\!+}Y)\bigr)\mathbin{+\!\!+}V .
```

**(v) $`\mathrm{blockok}(v_0,\ \mathrm{blk}\mathbin{+\!\!+}Y)`$。**
[(D.blockok)](Seqlex.md#d-blockok) の 3 条件を確認する。

- 先頭条件：$`\mathrm{headI}(\mathrm{blk}\mathbin{+\!\!+}Y) = (v_0,w_0)`$ であり $`\pi_0(v_0,w_0) = v_0`$。
- 下界条件：$`x \in \mathrm{blk}\mathbin{+\!\!+}Y`$ とする。$`x \in \mathrm{blk}`$ なら
  $`x = (v_0,w_0)`$（$`v_0 \le v_0`$）か $`x \in R`$（$`v_0 < \pi_0 x`$）。
  $`x \in Y`$ なら (iii) より $`v_0 \le \pi_0 x`$。
- $`\mathrm{steps}_1`$：[(T.blockok_ST_PS)](Seqlex.md#t-blockok_ST_PS) を $`N \in \mathrm{ST\_PS}`$ に適用して
  $`\mathrm{blockok}(0,N)`$、その第 3 成分が $`\mathrm{steps}_1 N`$ である。
  (iv) の分解と [(T.steps1_append)](Seqlex.md#t-steps1_append) を 2 回使う：
  まず $`\mathrm{steps}_1\bigl((G\mathbin{+\!\!+}(\mathrm{blk}\mathbin{+\!\!+}Y))\mathbin{+\!\!+}V\bigr)`$ から
  $`\mathrm{steps}_1(G\mathbin{+\!\!+}(\mathrm{blk}\mathbin{+\!\!+}Y))`$ を取り出し、
  そこから $`\mathrm{steps}_1(\mathrm{blk}\mathbin{+\!\!+}Y)`$ を取り出す。

**(vi) 窓の $`\mathrm{cnf}`$。** [(T.cnf_ST_PS)](Wf.md#t-cnf_ST_PS) より $`\mathrm{cnf}(\mathrm{tr}\,N)`$。
(iv) により $`\mathrm{cnf}\bigl(\mathrm{tr}((G\mathbin{+\!\!+}(\mathrm{blk}\mathbin{+\!\!+}Y))\mathbin{+\!\!+}V)\bigr)`$。
[(T.cnf_take)](Wf.md#t-cnf_take) を $`k := \lvert G\mathbin{+\!\!+}(\mathrm{blk}\mathbin{+\!\!+}Y)\rvert`$ に適用すると、
$`\mathrm{take}\,k`$ はこの連結の左側そのものであるから

```math
\mathrm{cnf}\bigl(\mathrm{tr}(G\mathbin{+\!\!+}(\mathrm{blk}\mathbin{+\!\!+}Y))\bigr).
```

$`\mathrm{blk}\mathbin{+\!\!+}Y = (v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}Y)`$ であるから、これは
$`\mathrm{cnf}\bigl(\mathrm{tr}(G\mathbin{+\!\!+}((v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}Y)))\bigr)`$ である。
[(T.cnf_tail)](Wf.md#t-cnf_tail) を $`t := (v_0,w_0)`$、$`T' := R\mathbin{+\!\!+}Y`$ に適用する
（その仮定 $`\forall x\in R\mathbin{+\!\!+}Y,\ v_0 \le \pi_0 x`$ は (v) の下界条件から従う）と

```math
\mathrm{cnf}\bigl(\mathrm{tr}((v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}Y))\bigr).
```

**(vii) 完全一致コピー支配を適用する。**
[(T.copy_dom_zero)](#t-copy_dom_zero) を $`d := \lvert Y\rvert`$、$`Y`$、$`v_0`$、$`w_0`$、$`R`$ に適用する。5 条件は

- $`\lvert Y\rvert \le \lvert Y\rvert`$、
- $`\mathrm{blockok}(v_0,(v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}Y))`$：(v)（$`\mathrm{blk}\mathbin{+\!\!+}Y = (v_0,w_0)\mathbin{::}(R\mathbin{+\!\!+}Y)`$）、
- $`\forall x\in R,\ v_0<\pi_0 x`$：仮定、
- $`Y = [] \vee \neg(v_0 < \pi_0(\mathrm{headI}\,Y))`$：(iii) より $`\pi_0(\mathrm{headI}\,Y) = v_0`$ であり $`\neg(v_0<v_0)`$、
- $`\mathrm{cnf}`$ 条件：(vi)

であり、$`m \ge 1`$ と $`Y \preceq_{\mathrm{lex}} \mathrm{cop}_0(\mathrm{blk},m)`$ を得る。

**(viii) 結論。** 答を $`m+1`$ とする。
[(T.copies_zero_succ)](#t-copies_zero_succ) より
$`\mathrm{cop}_0(\mathrm{blk},m+1) = \mathrm{cop}_0(\mathrm{blk},m)\mathbin{+\!\!+}\mathrm{blk}`$。
また $`q\mathbin{::}S = Y\mathbin{+\!\!+}V`$（(iii)）。よって示すべきは

```math
Y \mathbin{+\!\!+} V \ \prec_{\mathrm{lex}}\ \mathrm{cop}_0(\mathrm{blk},m) \mathbin{+\!\!+} \mathrm{blk} .
```

(vii) の $`\preceq_{\mathrm{lex}}`$ を 2 つに分ける。

- $`Y = \mathrm{cop}_0(\mathrm{blk},m)`$ のとき：
  [(T.seqlex_append_cancel)](Seqlex.md#t-seqlex_append_cancel) により
  $`V \prec_{\mathrm{lex}} \mathrm{blk}`$ を示せばよい。
  (iii) より $`V = []`$ ならば $`\mathrm{blk} \ne []`$ から従う。
  $`V = z\mathbin{::}Z`$ ($`\pi_0 z < v_0`$) ならば $`z <_{\mathrm{p}} (v_0,w_0)`$ であり
  [(T.seqlex_cons_cons)](Seqlex.md#t-seqlex_cons_cons) の第 1 選言により従う。
- $`Y \prec_{\mathrm{lex}} \mathrm{cop}_0(\mathrm{blk},m)`$ のとき：
  [(T.seqlex_splice)](#t-seqlex_splice) を $`A := Y`$, $`B := \mathrm{cop}_0(\mathrm{blk},m)`$,
  $`U := V`$, $`C := \mathrm{blk}`$ に適用する。$`U`$ についての仮定は次による。
  $`V = []`$ ならそのまま。$`V = z\mathbin{::}Z`$（$`\pi_0 z < v_0`$）のとき、
  [(T.copies_v0_le)](Wf.md#t-copies_v0_le)（$`\forall y\in R,\ v_0\le\pi_0 y`$ を仮定として）より
  $`\forall x\in\mathrm{cop}_0(\mathrm{blk},m),\ v_0 \le \pi_0 x`$ であるから
  $`\pi_0(\mathrm{headI}\,V) = \pi_0 z < v_0 \le \pi_0 x`$、よって $`\mathrm{headI}\,V <_{\mathrm{p}} x`$。∎

<a id="d-AscCrux"></a>
### 定義 上昇コピー分岐の要 (D.AscCrux)

$`G, R, S \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0 \in \mathbb{N}`$、$`lp, q \in \mathbb{N}\times\mathbb{N}`$ に対し
$`\mathrm{blk} := (v_0,w_0)\mathbin{::}R`$、$`H := (G\mathbin{+\!\!+}\mathrm{blk})\mathbin{+\!\!+}[lp]`$ と書く。
$`\mathrm{AscCrux}`$ とは、これらすべてについて次が成り立つという命題である。

次の 8 条件

1. $`H \in \mathrm{ST\_PS}`$、
2. $`(G\mathbin{+\!\!+}\mathrm{blk})\mathbin{+\!\!+}q\mathbin{::}S \in \mathrm{ST\_PS}`$、
3. $`\forall x\in R,\ v_0<\pi_0 x`$、
4. $`0<d_0`$、
5. $`\pi_1 lp = w_0+1`$、
6. $`\pi_0 lp = v_0+d_0`$、
7. $`\lvert G\rvert \to^{H}_1 \lvert G\mathbin{+\!\!+}\mathrm{blk}\rvert`$、
8. $`q <_{\mathrm{p}} lp`$

の下で

```math
\exists m,\ \Bigl(1\le m \ \wedge\ q\mathbin{::}S \preceq_{\mathrm{lex}}
 \sigma_{d_0}\bigl(\mathrm{cop}_{d_0}(\mathrm{blk},\ m)\bigr)\Bigr).
```

条件 7 は [(D.nextrel1)](Def.md#d-nextrel1) を列 $`H`$ に対して
$`j_0 := \lvert G\rvert`$、$`j_1 := \lvert G\mathbin{+\!\!+}\mathrm{blk}\rvert`$ で読んだものである。
$`\lvert H\rvert = \lvert G\mathbin{+\!\!+}\mathrm{blk}\rvert + 1`$ であるから、$`j_1`$ は $`H`$ の末尾列 $`lp`$ の添字である。

<a id="d-AscCrux1"></a>
### 定義 先頭段を済ませた要 (D.AscCrux1)

$`G, R, S \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0 \in \mathbb{N}`$ に対し
$`\mathrm{blk} := (v_0,w_0)\mathbin{::}R`$、$`H_1 := (G\mathbin{+\!\!+}\mathrm{blk})\mathbin{+\!\!+}[(v_0+d_0,\ w_0+1)]`$ と書く。
$`\mathrm{AscCrux}_1`$ とは、これらすべてについて次が成り立つという命題である。

次の 5 条件

1. $`H_1 \in \mathrm{ST\_PS}`$、
2. $`(G\mathbin{+\!\!+}\mathrm{blk})\mathbin{+\!\!+}(v_0+d_0,\ w_0)\mathbin{::}S \in \mathrm{ST\_PS}`$、
3. $`\forall x\in R,\ v_0<\pi_0 x`$、
4. $`0<d_0`$、
5. $`\lvert G\rvert \to^{H_1}_1 \lvert G\mathbin{+\!\!+}\mathrm{blk}\rvert`$

の下で

```math
\exists m,\ \Bigl(1\le m \ \wedge\ (v_0+d_0,w_0)\mathbin{::}S \preceq_{\mathrm{lex}}
 \sigma_{d_0}\bigl(\mathrm{cop}_{d_0}(\mathrm{blk},\ m)\bigr)\Bigr).
```

$`\mathrm{AscCrux}`$ との違いは、落とされる列 $`lp`$ が
[(T.nextrel1_snd_succ)](#t-nextrel1_snd_succ) により $`(v_0+d_0, w_0+1)`$ に確定し、
継続列 $`q`$ が $`(v_0+d_0,w_0)`$ に固定されている点である
（それ以外の $`q`$ は [(T.asc_head_step)](#t-asc_head_step) で直接処理される）。

---

## Part 6 — 上昇コピー（$`d_0>0`$）側：単一の $`\preceq`$ への還元

上昇コピーは入れ子である：第 $`k`$ コピーの根は深さ $`v_0+k\,d_0`$ にあり、$`k`$ が増えると深くなる。
そのため、完全一致コピーの場合と異なりコピー数についての再帰は生じず、
分岐全体が「崩れた節点 $`q=(v_0+d_0,w_0)`$ の引数が、元のブロック本体の平行移動で上から抑えられる」
という 1 本の不等式に帰着する。

<a id="t-shiftr0_length"></a>
### 定理 平行移動は長さを変えない (T.shiftr0_length)

**主張** $`\lvert \sigma_d X\rvert = \lvert X\rvert`$。

**証明** [(D.shiftr0)](Wf.md#d-shiftr0) より $`\sigma_d X = \mathrm{map}\,(\lambda p.(\pi_0 p+d,\pi_1 p))\,X`$
であり、$`\mathrm{map}`$ は長さを保つ。∎

<a id="t-mem_shiftr0_le"></a>
### 定理 平行移動と下界 (T.mem_shiftr0_le)

**主張** $`\forall x\in X,\ d \le \pi_0 x`$ ならば $`\forall x\in \sigma_e X,\ d+e \le \pi_0 x`$。

**証明** $`x \in \sigma_e X`$ とする。[(T.mem_shiftr0)](Wf.md#t-mem_shiftr0) より、ある $`p \in X`$ について
$`x = (\pi_0 p + e,\ \pi_1 p)`$ である。仮定より $`d \le \pi_0 p`$、よって
$`\pi_0 x = \pi_0 p + e \ge d + e`$。∎

<a id="t-shiftr0_copies"></a>
### 定理 平行移動とコピー塔の交換 (T.shiftr0_copies)

**主張** $`\sigma_d\bigl(\mathrm{cop}_d(B,n)\bigr) = \mathrm{cop}_d\bigl(\sigma_d B,\ n\bigr)`$。

**証明** [(D.copies)](Wf.md#d-copies), [(D.shiftr0)](Wf.md#d-shiftr0) を展開する。
$`\mathrm{map}`$ は $`\mathrm{flatMap}`$ を通り抜ける（$`\mathrm{map}\,f\,(\mathrm{flatMap}\,g\,L) = \mathrm{flatMap}\,(\mathrm{map}\,f\circ g)\,L`$）から

```math
\sigma_d(\mathrm{cop}_d(B,n)) = \mathrm{flatMap}\bigl(\lambda k.\ \sigma_d(\sigma_{k d}B)\bigr)\,\mathrm{range}(n),
\qquad
\mathrm{cop}_d(\sigma_d B,n) = \mathrm{flatMap}\bigl(\lambda k.\ \sigma_{k d}(\sigma_d B)\bigr)\,\mathrm{range}(n).
```

各 $`k`$ について、$`\mathrm{map}`$ の合成則より両者の第 $`k`$ 成分はともに $`B`$ の各要素 $`p`$ を写した列であり、
その第 0 成分はそれぞれ $`(\pi_0 p + k d) + d`$ と $`(\pi_0 p + d) + k d`$、第 1 成分はともに $`\pi_1 p`$ である。
$`\mathbb{N}`$ の加法の結合律と交換律より $`(\pi_0 p + k d) + d = (\pi_0 p + d) + k d`$。
よって両辺は一致する。∎

<a id="d-AscArgDom"></a>
### 定義 崩れた節点の引数支配 (D.AscArgDom)

$`G, R, S \in \mathrm{PairSeq}`$、$`v_0, w_0, d_0 \in \mathbb{N}`$ に対し、記号は
[(D.AscCrux1)](#d-AscCrux1) と同じとする（$`\mathrm{blk} = (v_0,w_0)\mathbin{::}R`$、
$`H_1 = (G\mathbin{+\!\!+}\mathrm{blk})\mathbin{+\!\!+}[(v_0+d_0,w_0+1)]`$）。
$`\mathrm{AscArgDom}`$ とは、これらすべてについて、
[(D.AscCrux1)](#d-AscCrux1) と同じ 5 条件の下で

```math
\exists m,\quad
\mathrm{tw}_{v_0+d_0} S \ \preceq_{\mathrm{lex}}\
\sigma_{d_0}\Bigl(R \mathbin{+\!\!+} \mathrm{cop}_{d_0}\bigl(\sigma_{d_0}\mathrm{blk},\ m\bigr)\Bigr)
```

が成り立つという命題である（$`\mathrm{AscCrux}_1`$ と違い $`m \ge 1`$ は要求しない）。

左辺 $`\mathrm{tw}_{v_0+d_0}S`$ は、列 $`(G\mathbin{+\!\!+}\mathrm{blk})\mathbin{+\!\!+}(v_0+d_0,w_0)\mathbin{::}S`$ の中で
コピー根 $`(v_0+d_0,w_0)`$ に続く、行 0 の値が $`v_0+d_0`$ より真に大きい列が続く極大の並びである。
右辺は、[(T.oper_bad_blocks_all)](#t-oper_bad_blocks_all) の結論 2 により
宿主 $`M`$ の展開 $`M[m+1]`$ の中で $`(v_0,w_0)`$ に続く並び
$`R \mathbin{+\!\!+} \mathrm{cop}_{d_0}(\sigma_{d_0}\mathrm{blk},m)`$ を $`\sigma_{d_0}`$ で送ったものである。

この命題は本章では証明しない。証明は [`AscArg.md`](AscArg.md) の
[(T.ascArgDom_of_core)](AscArg.md#t-ascArgDom_of_core) と
[(T.argDomCore_holds)](AscArg.md#t-argDomCore_holds) で与えられる。

<a id="t-shiftr0_append"></a>
### 定理 平行移動と連結 (T.shiftr0_append)

**主張** $`\sigma_d(A\mathbin{+\!\!+}B) = \sigma_d A \mathbin{+\!\!+} \sigma_d B`$。

**証明** [(D.shiftr0)](Wf.md#d-shiftr0) より両辺は $`\mathrm{map}`$ であり、
$`\mathrm{map}\,f\,(A\mathbin{+\!\!+}B) = \mathrm{map}\,f\,A \mathbin{+\!\!+} \mathrm{map}\,f\,B`$ による。∎

<a id="t-copies_succ_back"></a>
### 定理 コピー塔の後方展開 (T.copies_succ_back)

**主張** $`\mathrm{cop}_d(B,\ n+1) = \mathrm{cop}_d(B,\ n) \mathbin{+\!\!+} \sigma_{n\cdot d}B`$。

**証明** [(D.copies)](Wf.md#d-copies) と $`\mathrm{range}(n+1) = \mathrm{range}(n)\mathbin{+\!\!+}[n]`$、
および $`\mathrm{flatMap}`$ が連結を連結に写すことによる。
第 2 項は $`\mathrm{flatMap}(\lambda k.\sigma_{kd}B)\,[n] = \sigma_{nd}B`$ である。∎

<a id="t-asc_crux1_of_argdom"></a>
### 定理 引数支配から要へ (T.asc_crux1_of_argdom)

**主張** $`\mathrm{AscArgDom}`$（[(D.AscArgDom)](#d-AscArgDom)）ならば
$`\mathrm{AscCrux}_1`$（[(D.AscCrux1)](#d-AscCrux1)）。

**証明** $`\mathrm{AscCrux}_1`$ の 5 条件を仮定する。
$`\mathrm{blk} := (v_0,w_0)\mathbin{::}R`$、$`\mathrm{blk}' := \sigma_{d_0}\mathrm{blk}`$ とおく。
[(T.shiftr0_cons)](Wf.md#t-shiftr0_cons) より

```math
\mathrm{blk}' = (v_0+d_0,\ w_0)\mathbin{::}\sigma_{d_0}R. \tag{1}
```

$`\mathrm{AscArgDom}`$ を同じ 5 条件に適用して $`m`$ を得る。すなわち
$`S_{\mathrm{hi}} := \mathrm{tw}_{v_0+d_0}S`$、$`S_{\mathrm{lo}} := \mathrm{dw}_{v_0+d_0}S`$ とおくと
(L1) より $`S_{\mathrm{hi}}\mathbin{+\!\!+}S_{\mathrm{lo}} = S`$ であり

```math
S_{\mathrm{hi}} \preceq_{\mathrm{lex}} \sigma_{d_0}\bigl(R \mathbin{+\!\!+} \mathrm{cop}_{d_0}(\mathrm{blk}',m)\bigr). \tag{2}
```

**(i) 宿主側引数の各列は深さ $`v_0`$ より真に深い。**
$`x \in R \mathbin{+\!\!+} \mathrm{cop}_{d_0}(\mathrm{blk}',m)`$ とする。
$`x\in R`$ なら条件 3 より $`v_0 < \pi_0 x`$。
$`x \in \mathrm{cop}_{d_0}(\mathrm{blk}',m)`$ のときは、(1) と
[(T.copies_v0_le)](Wf.md#t-copies_v0_le) を基準深さ $`v_0+d_0`$、本体 $`\sigma_{d_0}R`$ に適用する。
その仮定 $`\forall y \in \sigma_{d_0}R,\ v_0+d_0 \le \pi_0 y`$ は
[(T.mem_shiftr0_le)](#t-mem_shiftr0_le) を $`\forall y\in R,\ v_0\le\pi_0 y`$（条件 3）に適用して得られる。
よって $`v_0+d_0 \le \pi_0 x`$、条件 4（$`0<d_0`$）より $`v_0 < \pi_0 x`$。

**(ii) $`S_{\mathrm{lo}}`$ の先頭。** (L3) より $`S_{\mathrm{lo}} = []`$ であるか、
$`S_{\mathrm{lo}} = z\mathbin{::}Z`$ と書けて $`\neg(v_0+d_0 < \pi_0 z)`$、すなわち
$`\pi_0(\mathrm{headI}\,S_{\mathrm{lo}}) \le v_0+d_0`$。

**(iii) 答は $`m+2`$。** 目標の右辺を展開する。
$`E := \sigma_{d_0}\bigl(\sigma_{m d_0}\mathrm{blk}'\bigr)`$ とおく。
[(T.shiftr0_copies)](#t-shiftr0_copies)、[(T.copies_succ_front)](Wf.md#t-copies_succ_front)、
[(T.copies_succ_back)](#t-copies_succ_back)、[(T.shiftr0_append)](#t-shiftr0_append)、
連結の結合律、(1) を順に使うと

```math
\begin{aligned}
\sigma_{d_0}\bigl(\mathrm{cop}_{d_0}(\mathrm{blk},m+2)\bigr)
&= \mathrm{cop}_{d_0}(\mathrm{blk}',m+2)
= \mathrm{blk}' \mathbin{+\!\!+} \sigma_{d_0}\bigl(\mathrm{cop}_{d_0}(\mathrm{blk}',m+1)\bigr)\\
&= \mathrm{blk}' \mathbin{+\!\!+} \Bigl(\sigma_{d_0}\bigl(\mathrm{cop}_{d_0}(\mathrm{blk}',m)\bigr) \mathbin{+\!\!+} E\Bigr)\\
&= (v_0+d_0,w_0)\mathbin{::}\Bigl(\sigma_{d_0}R \mathbin{+\!\!+} \sigma_{d_0}\bigl(\mathrm{cop}_{d_0}(\mathrm{blk}',m)\bigr) \mathbin{+\!\!+} E\Bigr)\\
&= (v_0+d_0,w_0)\mathbin{::}\Bigl(\sigma_{d_0}\bigl(R \mathbin{+\!\!+} \mathrm{cop}_{d_0}(\mathrm{blk}',m)\bigr) \mathbin{+\!\!+} E\Bigr).
\end{aligned}
```

（第 2 行では [(T.copies_succ_back)](#t-copies_succ_back) を $`n:=m`$ に使って
$`\mathrm{cop}_{d_0}(\mathrm{blk}',m+1) = \mathrm{cop}_{d_0}(\mathrm{blk}',m)\mathbin{+\!\!+}\sigma_{m d_0}\mathrm{blk}'`$ とし、
[(T.shiftr0_append)](#t-shiftr0_append) で $`\sigma_{d_0}`$ を分配した。
最終行では [(T.shiftr0_append)](#t-shiftr0_append) を逆向きに使った。）

$`D := \sigma_{d_0}\bigl(R\mathbin{+\!\!+}\mathrm{cop}_{d_0}(\mathrm{blk}',m)\bigr)`$ と書く。
示すべきは

```math
(v_0+d_0,w_0)\mathbin{::}S \ \preceq_{\mathrm{lex}}\ (v_0+d_0,w_0)\mathbin{::}(D \mathbin{+\!\!+} E)
```

であり、両辺を $`[(v_0+d_0,w_0)]\mathbin{+\!\!+}(\cdot)`$ と見て
[(T.sle_append_cancel)](#t-sle_append_cancel) を使うと、示すべきは

```math
S \ \preceq_{\mathrm{lex}}\ D \mathbin{+\!\!+} E. \tag{3}
```

**(iv) $`E`$ の形。** (1) と [(T.shiftr0_cons)](Wf.md#t-shiftr0_cons) を 2 回使うと
$`E \ne []`$ であり、その先頭列の第 0 成分は

```math
\pi_0(\mathrm{headI}\,E) = v_0 + d_0 + m\,d_0 + d_0. \tag{4}
```

**(v) (2) の 2 つの場合。**

*場合 $`S_{\mathrm{hi}} = D`$。* このとき $`S = S_{\mathrm{hi}}\mathbin{+\!\!+}S_{\mathrm{lo}} = D \mathbin{+\!\!+} S_{\mathrm{lo}}`$
であるから、(3) は [(T.sle_append_cancel)](#t-sle_append_cancel) により
$`S_{\mathrm{lo}} \preceq_{\mathrm{lex}} E`$ に帰着する。
(ii) より $`S_{\mathrm{lo}} = []`$ ならば $`E \ne []`$ から $`[] \prec_{\mathrm{lex}} E`$。
$`S_{\mathrm{lo}} = z\mathbin{::}Z`$、$`E = b\mathbin{::}B`$ のときは、(ii) と (4) と条件 4 より

```math
\pi_0 z \le v_0+d_0 < v_0+d_0+m\,d_0+d_0 = \pi_0 b
```

（最後の狭義不等号は $`0 < d_0`$ による）。よって $`z <_{\mathrm{p}} b`$ であり
[(T.seqlex_cons_cons)](Seqlex.md#t-seqlex_cons_cons) の第 1 選言により $`S_{\mathrm{lo}} \prec_{\mathrm{lex}} E`$。

*場合 $`S_{\mathrm{hi}} \prec_{\mathrm{lex}} D`$。* [(T.seqlex_splice)](#t-seqlex_splice) を
$`A := S_{\mathrm{hi}}`$, $`B := D`$, $`U := S_{\mathrm{lo}}`$, $`C := E`$ に適用する。
$`U`$ についての仮定は次による。$`S_{\mathrm{lo}} = []`$ ならそのまま。
そうでなければ $`x \in D`$ とすると、[(T.mem_shiftr0)](Wf.md#t-mem_shiftr0) よりある
$`y \in R\mathbin{+\!\!+}\mathrm{cop}_{d_0}(\mathrm{blk}',m)`$ について $`x = (\pi_0 y + d_0, \pi_1 y)`$ であり、
(i) より $`v_0 < \pi_0 y`$ だから $`\pi_0 x = \pi_0 y + d_0 > v_0 + d_0 \ge \pi_0(\mathrm{headI}\,S_{\mathrm{lo}})`$（(ii)）。
よって $`\mathrm{headI}\,S_{\mathrm{lo}} <_{\mathrm{p}} x`$。
[(T.seqlex_splice)](#t-seqlex_splice) より
$`S = S_{\mathrm{hi}}\mathbin{+\!\!+}S_{\mathrm{lo}} \prec_{\mathrm{lex}} D\mathbin{+\!\!+}E`$、これが (3) である。∎

---

## Part 6b — $`\mathrm{ST\_PS}`$ の列規律

Lean 側にはこの節見出し（`/-! ## Part 6b ... -/`）が残っているが、その下に宣言は 1 つも置かれていない。
節見出しのコメントが挙げる 2 つの補題名 `snd_le_fst_ST_PS`, `le_diag_ST_PS` は
`lean/YAPSS/` のどのファイルにも存在しない。したがって本章として記すべき命題はない。

---

## Part 7 — 組み立て（上昇側の要を仮定して）

<a id="t-asc_head_step"></a>
### 定理 上昇側の先頭段 (T.asc_head_step)

**主張** $`\mathrm{AscCrux}_1`$（[(D.AscCrux1)](#d-AscCrux1)）ならば
$`\mathrm{AscCrux}`$（[(D.AscCrux)](#d-AscCrux)）。

**証明** $`\mathrm{AscCrux}`$ の 8 条件を仮定する。
条件 5, 6 より $`\pi_0 lp = v_0+d_0`$ かつ $`\pi_1 lp = w_0+1`$、対は成分で決まるから

```math
lp = (v_0+d_0,\ w_0+1). \tag{1}
```

$`q = (v_0+d_0,w_0)`$ か否かで分ける。

- $`q = (v_0+d_0,w_0)`$ のとき：(1) により条件 1, 7 はそれぞれ
  $`\mathrm{AscCrux}_1`$ の条件 1, 5 の形になり、条件 2 は条件 2、条件 3 は条件 3、条件 4 は条件 4 である。
  よって $`\mathrm{AscCrux}_1`$ を適用して結論を得る。
- $`q \ne (v_0+d_0,w_0)`$ のとき：$`m := 1`$ とする。
  [(T.copies_one)](Wf.md#t-copies_one) と [(T.shiftr0_cons)](Wf.md#t-shiftr0_cons) より

  ```math
  \sigma_{d_0}\bigl(\mathrm{cop}_{d_0}((v_0,w_0)\mathbin{::}R,1)\bigr)
   = \sigma_{d_0}\bigl((v_0,w_0)\mathbin{::}R\bigr) = (v_0+d_0,w_0)\mathbin{::}\sigma_{d_0}R .
  ```

  [(T.seqlex_cons_cons)](Seqlex.md#t-seqlex_cons_cons) の第 1 選言により
  $`q <_{\mathrm{p}} (v_0+d_0,w_0)`$ を示せばよい。
  条件 8 と (1) より

  ```math
  \pi_0 q < v_0+d_0 \quad\text{または}\quad \bigl(\pi_0 q = v_0+d_0 \ \wedge\ \pi_1 q < w_0+1\bigr),
  ```

  また $`q \ne (v_0+d_0,w_0)`$ より $`\neg\bigl(\pi_0 q = v_0+d_0 \wedge \pi_1 q = w_0\bigr)`$ である。
  第 1 の場合はそのまま $`q <_{\mathrm{p}} (v_0+d_0,w_0)`$ の第 1 選言。
  第 2 の場合は $`\pi_1 q \le w_0`$ であり、$`\pi_1 q = w_0`$ とすると
  $`\pi_0 q = v_0+d_0 \wedge \pi_1 q = w_0`$ となって上の否定に反する。よって $`\pi_1 q < w_0`$、
  $`q <_{\mathrm{p}} (v_0+d_0,w_0)`$ の第 2 選言。∎

<a id="t-seqlex_cof_bad"></a>
### 定理 分岐 bad の共終性 (T.seqlex_cof_bad)

**主張** $`\mathrm{AscCrux}`$ を仮定する。$`M, N \in \mathrm{ST\_PS}`$、$`1 < \lvert M\rvert`$、
$`\neg\bigl(M_{0,\lvert M\rvert-1}=0 \wedge M_{1,\lvert M\rvert-1}=0\bigr)`$、
$`N \prec_{\mathrm{lex}} M`$ ならば
$`\exists n,\ (1\le n \wedge N \preceq_{\mathrm{lex}} M[n])`$。

**証明** [(T.hasParent_last_ST_PS)](#t-hasParent_last_ST_PS) を $`M`$ に適用して
$`\mathrm{hasParent}(M,\mathrm{idx}_1(M,\lvert M\rvert-1),\lvert M\rvert-1)`$ を得る
（$`0<\lvert M\rvert`$ は $`1<\lvert M\rvert`$ から）。
[(T.oper_bad_blocks_all)](#t-oper_bad_blocks_all) を、$`\mathrm{steps}_1 M`$ として
[(T.blockok_ST_PS)](Seqlex.md#t-blockok_ST_PS) の第 3 成分を、$`\mathrm{r1ok}\,M`$ として
[(T.r1ok_ST_PS)](Nrmstep.md#t-r1ok_ST_PS) を用いて適用し、
$`G, v_0, w_0, R, d_0, lp`$ と 5 つの結論を得る。$`\mathrm{blk} := (v_0,w_0)\mathbin{::}R`$ と書く。

結論 1 より $`M = (G\mathbin{+\!\!+}\mathrm{blk})\mathbin{+\!\!+}[lp]`$ であるから、
仮定 $`N \prec_{\mathrm{lex}} M`$ に [(T.seqlex_snoc_cases)](#t-seqlex_snoc_cases) を
$`D := G\mathbin{+\!\!+}\mathrm{blk}`$ で適用する。

**場合 1：$`N \preceq_{\mathrm{lex}} G\mathbin{+\!\!+}\mathrm{blk}`$。**
$`n := 1`$ とする。結論 2（$`n=1`$）と [(T.copies_one)](Wf.md#t-copies_one) より
$`M[1] = G\mathbin{+\!\!+}\mathrm{cop}_{d_0}(\mathrm{blk},1) = G\mathbin{+\!\!+}\mathrm{blk}`$ であり、
これがそのまま $`N \preceq_{\mathrm{lex}} M[1]`$ を与える。

**場合 2：$`N = (G\mathbin{+\!\!+}\mathrm{blk})\mathbin{+\!\!+}q\mathbin{::}S`$ かつ $`q <_{\mathrm{p}} lp`$。**
まず

```math
\exists m,\ \Bigl(1\le m \wedge q\mathbin{::}S \preceq_{\mathrm{lex}} \sigma_{d_0}\bigl(\mathrm{cop}_{d_0}(\mathrm{blk},m)\bigr)\Bigr) \tag{$\sharp$}
```

を示す。[(T.oper_bad_blocks_all)](#t-oper_bad_blocks_all) の結論 5 で分ける。

- 第 1 の場合（$`d_0=0`$、$`\pi_1 lp = 0`$、$`\pi_0 lp = v_0+1`$）：
  [(T.shiftr0_zero)](Wf.md#t-shiftr0_zero) より $`\sigma_0`$ は恒等であるから、
  $`(\sharp)`$ は [(T.crux_zero)](#t-crux_zero) そのものである。
  その仮定 $`N \in \mathrm{ST\_PS}`$ は $`N`$ の上の表示に書き換えたもの、
  $`\forall x\in R,\ v_0<\pi_0 x`$ は結論 3、残りはこの場合の条件である。
- 第 2 の場合（$`0<d_0`$、$`\pi_1 lp = w_0+1`$、$`\pi_0 lp = v_0+d_0`$、$`\lvert G\rvert \to^M_1 (\lvert M\rvert-1)`$）：
  結論 1 より $`\lvert M\rvert-1 = \lvert G\mathbin{+\!\!+}\mathrm{blk}\rvert`$ であり、
  $`M = (G\mathbin{+\!\!+}\mathrm{blk})\mathbin{+\!\!+}[lp]`$ であるから、
  行 1 の親子関係は [(D.AscCrux)](#d-AscCrux) の条件 7 の形に書き換えられる。
  $`\mathrm{AscCrux}`$ を条件 1（$`M\in\mathrm{ST\_PS}`$ の書き換え）、条件 2（$`N\in\mathrm{ST\_PS}`$ の書き換え）、
  条件 3（結論 3）、条件 4–6（この場合の条件）、条件 7、条件 8（$`q<_{\mathrm{p}}lp`$）に適用して $`(\sharp)`$ を得る。

$`(\sharp)`$ の $`m`$ に対し $`n := m+1`$ とする。結論 2 と
[(T.copies_succ_front)](Wf.md#t-copies_succ_front) より

```math
M[m+1] = G \mathbin{+\!\!+} \mathrm{cop}_{d_0}(\mathrm{blk},m+1)
 = G \mathbin{+\!\!+} \Bigl(\mathrm{blk} \mathbin{+\!\!+} \sigma_{d_0}\bigl(\mathrm{cop}_{d_0}(\mathrm{blk},m)\bigr)\Bigr),
```

また $`N = G \mathbin{+\!\!+} (\mathrm{blk} \mathbin{+\!\!+} q\mathbin{::}S)`$（連結の結合律）。
[(T.sle_append_cancel)](#t-sle_append_cancel) を $`A := G`$ に適用し、続いて $`A := \mathrm{blk}`$ に適用すると、
示すべきは $`q\mathbin{::}S \preceq_{\mathrm{lex}} \sigma_{d_0}(\mathrm{cop}_{d_0}(\mathrm{blk},m))`$ に帰着し、
これは $`(\sharp)`$ である。∎

<a id="t-seqlex_cofinality_of_crux"></a>
### 定理 要を仮定した $`\prec_{\mathrm{lex}}`$ 版共終性 (T.seqlex_cofinality_of_crux)

**主張** $`\mathrm{AscCrux}`$ ならば $`\mathrm{SeqCof}`$（[(D.SeqlexCofinality)](#d-SeqlexCofinality)）。

**証明** $`M, N \in \mathrm{ST\_PS}`$、$`N \prec_{\mathrm{lex}} M`$ とする。
$`\lvert M\rvert - 1 = 0`$ か否かで分ける。

- $`\lvert M\rvert-1 = 0`$：[(T.seqlex_cof_short)](#t-seqlex_cof_short)。
- $`\lvert M\rvert-1 \ne 0`$：このとき $`\lvert M\rvert \ge 2`$、すなわち $`1 < \lvert M\rvert`$ である
  （$`\lvert M\rvert \le 1`$ ならば切り捨て減法により $`\lvert M\rvert-1 = 0`$）。
  さらに $`M_{0,\lvert M\rvert-1}=0 \wedge M_{1,\lvert M\rvert-1}=0`$ か否かで分ける。
  - 成り立つとき：[(T.seqlex_cof_zero)](#t-seqlex_cof_zero)。
  - 成り立たないとき：[(T.seqlex_cof_bad)](#t-seqlex_cof_bad)。∎

<a id="t-pss_cofinality_of_crux"></a>
### 定理 要からの PSS Bachmann 共終性 (T.pss_cofinality_of_crux)

**主張** $`\mathrm{AscCrux}_1`$（[(D.AscCrux1)](#d-AscCrux1)）を仮定する。
$`M, N \in \mathrm{ST\_PS}`$ かつ $`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$ ならば

```math
\exists n,\ \bigl(1 \le n \ \wedge\ \mathrm{tr}\,N \preceq \mathrm{tr}(M[n])\bigr).
```

**証明** [(T.asc_head_step)](#t-asc_head_step) により $`\mathrm{AscCrux}`$ を得る。
[(T.seqlex_cofinality_of_crux)](#t-seqlex_cofinality_of_crux) により $`\mathrm{SeqCof}`$ を得る。
[(T.pss_cofinality_of_seqlex)](#t-pss_cofinality_of_seqlex) に $`\mathrm{SeqCof}`$ と
$`M, N \in \mathrm{ST\_PS}`$、$`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$ を与えて結論を得る。∎

<a id="t-pss_cofinality_of_argdom"></a>
### 定理 引数支配からの PSS Bachmann 共終性 (T.pss_cofinality_of_argdom)

**主張** $`\mathrm{AscArgDom}`$（[(D.AscArgDom)](#d-AscArgDom)）を仮定する。
$`M, N \in \mathrm{ST\_PS}`$ かつ $`\mathrm{tr}\,N \prec \mathrm{tr}\,M`$ ならば

```math
\exists n,\ \bigl(1 \le n \ \wedge\ \mathrm{tr}\,N \preceq \mathrm{tr}(M[n])\bigr).
```

**証明** [(T.asc_crux1_of_argdom)](#t-asc_crux1_of_argdom) により $`\mathrm{AscCrux}_1`$ を得、
[(T.pss_cofinality_of_crux)](#t-pss_cofinality_of_crux) を適用する。∎

これが本章の到達点である。すなわち PSS Bachmann 共終性は、
[(D.AscArgDom)](#d-AscArgDom) という単一の $`\preceq_{\mathrm{lex}}`$ 不等式のみに依存する。
$`\mathrm{AscArgDom}`$ は [`AscArg.md`](AscArg.md) で無仮定に証明され、
その結果は [`Wset.md`](Wset.md) の
[(T.wf_olt_ST_PS_of_cofinality)](Wset.md#t-wf_olt_ST_PS_of_cofinality) の共終性仮定に渡される。
