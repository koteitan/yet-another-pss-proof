[← 目次](README.md)

# Gterm0Olt — 連結による翻訳の弱増加と前部分列による弱減少

本章は翻訳 $\mathrm{tr}$（[(D.translate)](Mechanized.md#d-translate)）の 2 つの単調性を示す。
第 1 は、列の末尾に任意の列を連結しても $\mathrm{tr}$ の値は $\preceq$ について減らないこと
（[(T.translate_append_ge)](#t-translate_append_ge)）。
第 2 は、その系として、列の先頭から $m$ 個を取った前部分列の $\mathrm{tr}$ が元の列の $\mathrm{tr}$ 以下であること
（[(T.translate_take_le)](#t-translate_take_le)）。
本章の宣言はこの 2 つの定理のみであり、新しい定義は導入しない。

## 記法

本章は新しい Lean 名を導入しない。用いる記号はすべて既出であり、対応は次のとおりである。

| Lean | 本文 | 意味 |
|---|---|---|
| `PairSeq` | $\mathrm{PairSeq}$ | 自然数の対の有限列全体 |
| `Three` | $\mathrm{Three}$ | 三分岐記法の項の型 |
| `Z` | $\mathsf{Z}$ | 項 $0$ |
| `P a b c` | $\mathsf{P}(a,b,c)$ | 項 $p_a(b)+c$ |
| `translate M` | $\mathrm{tr}\,M$ | ペア列 $M$ の項への翻訳 |
| `x <o y` | $x \prec y$ | 添字優先辞書式順序 |
| `x ≤o y` | $x \preceq y$ | $x \prec y \vee x = y$ |
| `xs ++ ys` | $xs \mathbin{+\!\!+} ys$ | 連結 |
| `L.take m` | $\mathrm{take}\,m\,L$ | 先頭 $m$ 個からなる前部分列 |
| `L.drop m` | $\mathrm{drop}\,m\,L$ | 先頭 $m$ 個を除いた残り |
| `L.dropLast` | $\mathrm{dropLast}\,L$ | 末尾 1 個を除いた列 |
| `L.length` | $\lvert L\rvert$ | 長さ |
| `Gterm u t` | $\mathrm{Gterm}\,u\,t$ | 項 $t$ から定まる項の集合（定義は [(D.Gterm)](Otembed.md#d-Gterm)） |
| `tsize t` | $\mathrm{tsize}\,t$ | 項 $t$ に含まれる $\mathsf{P}$ の個数 |

定義の所在は次のとおり。
$\mathrm{PairSeq}$ は [(D.PairSeq)](Def.md#d-PairSeq)、
$\mathrm{Three}$・$\mathsf{Z}$・$\mathsf{P}$ は [(D.Three)](Mechanized.md#d-Three)、
$\mathrm{tr}$ は [(D.translate)](Mechanized.md#d-translate)、
$\prec$ は [(D.olt)](Mechanized.md#d-olt)、
$\preceq$ は [(D.ole)](Mechanized.md#d-ole)、
$\mathrm{Gterm}$ は [(D.Gterm)](Otembed.md#d-Gterm)、
$\mathrm{tsize}$ は [(D.tsize)](Wfsum.md#d-tsize)。
最後の 2 つは、本章の末尾の注でのみ用いる。

さらに、標準ライブラリの次の 2 つの等式を用いる。

- `List.append_assoc` : $xs \mathbin{+\!\!+} (ys \mathbin{+\!\!+} zs) = (xs \mathbin{+\!\!+} ys) \mathbin{+\!\!+} zs$。
- `List.take_append_drop` : $\mathrm{take}\,m\,L \mathbin{+\!\!+} \mathrm{drop}\,m\,L = L$（任意の $m \in \mathbb{N}$、任意の $L$）。

また、本章で用いる**末尾帰納法**の原理（Lean の `List.reverseRecOn`）を明示しておく。

> ペア列の述語 $\Psi$ が
> 1. $\Psi([])$、
> 2. $\forall D' \in \mathrm{PairSeq},\ \forall m \in \mathbb{N}\times\mathbb{N},\ \Psi(D') \to \Psi(D' \mathbin{+\!\!+} [m])$
>
> をみたすならば、$\forall D \in \mathrm{PairSeq},\ \Psi(D)$。

これは $\lvert D\rvert$ に関する強帰納法である。実際、$D = []$ なら条件 1 が結論そのものであり、
$D \ne []$ なら標準ライブラリの `List.dropLast_append_getLast` により
$D = \mathrm{dropLast}\,D \mathbin{+\!\!+} [\,\mathrm{getLast}\,D\,]$ と書け、
$\lvert \mathrm{dropLast}\,D\rvert = \lvert D\rvert - 1 < \lvert D\rvert$ であるから
$D' := \mathrm{dropLast}\,D$ に強帰納法の仮定 $\Psi(D')$ が使え、条件 2 が適用できる。

---

## 連結と前部分列に関する $\mathrm{tr}$ の単調性

<a id="t-translate_append_ge"></a>
### 定理 連結による弱増加 (T.translate_append_ge)

**主張** 任意のペア列 $C, D \in \mathrm{PairSeq}$ に対し
```math
\mathrm{tr}\,C \ \preceq\ \mathrm{tr}(C \mathbin{+\!\!+} D).
```

**証明** $C$ を固定し、$D$ に関する末尾帰納法（上の「記法」節に明示した `List.reverseRecOn`）を行う。
帰納法の述語は
```math
\Psi(D) :\equiv \bigl(\mathrm{tr}\,C \preceq \mathrm{tr}(C \mathbin{+\!\!+} D)\bigr)
```
である（$C$ は固定されているので $\Psi$ は $D$ のみの述語である）。

- **基底段** $D = []$：$C \mathbin{+\!\!+} [] = C$ であるから、示すべきは $\mathrm{tr}\,C \preceq \mathrm{tr}\,C$ である。
  [(D.ole)](Mechanized.md#d-ole) より $x \preceq y$ は $x \prec y \vee x = y$ であり、
  ここでは第 2 選言 $\mathrm{tr}\,C = \mathrm{tr}\,C$ が反射律により成立する。よって $\Psi([])$。

- **帰納段** $D = D' \mathbin{+\!\!+} [m]$（$D' \in \mathrm{PairSeq}$、$m \in \mathbb{N}\times\mathbb{N}$）：
  帰納法の仮定は
  ```math
  \Psi(D') \equiv \bigl(\mathrm{tr}\,C \preceq \mathrm{tr}(C \mathbin{+\!\!+} D')\bigr)
  ```
  である。示すべきは $\mathrm{tr}\,C \preceq \mathrm{tr}\bigl(C \mathbin{+\!\!+} (D' \mathbin{+\!\!+} [m])\bigr)$ であるが、
  `List.append_assoc` により
  ```math
  C \mathbin{+\!\!+} (D' \mathbin{+\!\!+} [m]) \ =\ (C \mathbin{+\!\!+} D') \mathbin{+\!\!+} [m]
  ```
  であるから、示すべき命題は
  ```math
  \mathrm{tr}\,C \ \preceq\ \mathrm{tr}\bigl((C \mathbin{+\!\!+} D') \mathbin{+\!\!+} [m]\bigr)
  ```
  と同一である。ここで [(T.translate_snoc_increase)](Mechanized.md#t-translate_snoc_increase) を
  $C := C \mathbin{+\!\!+} D'$、$m := m$ として適用すると
  ```math
  \mathrm{tr}(C \mathbin{+\!\!+} D') \ \prec\ \mathrm{tr}\bigl((C \mathbin{+\!\!+} D') \mathbin{+\!\!+} [m]\bigr)
  ```
  を得る。[(D.ole)](Mechanized.md#d-ole) の第 1 選言により、これは
  $\mathrm{tr}(C \mathbin{+\!\!+} D') \preceq \mathrm{tr}\bigl((C \mathbin{+\!\!+} D') \mathbin{+\!\!+} [m]\bigr)$ を与える。
  帰納法の仮定 $\Psi(D')$ とこれに [(T.ole_trans)](Wfsum.md#t-ole_trans) を
  $x := \mathrm{tr}\,C$、$y := \mathrm{tr}(C \mathbin{+\!\!+} D')$、$z := \mathrm{tr}\bigl((C \mathbin{+\!\!+} D') \mathbin{+\!\!+} [m]\bigr)$
  として適用すれば
  ```math
  \mathrm{tr}\,C \ \preceq\ \mathrm{tr}\bigl((C \mathbin{+\!\!+} D') \mathbin{+\!\!+} [m]\bigr),
  ```
  すなわち $\Psi(D' \mathbin{+\!\!+} [m])$ を得る。

末尾帰納法の 2 条件が示されたので、すべての $D$ について $\Psi(D)$ が成り立つ。∎

**注（$\prec$ ではなく $\preceq$ であること）**
$D = []$ のとき $C \mathbin{+\!\!+} D = C$ であり両辺は等しいから、$\prec$ に強めることはできない。
$D \ne []$ の場合には、上の帰納段が示すとおり
$\mathrm{tr}(C\mathbin{+\!\!+}D') \prec \mathrm{tr}\bigl((C\mathbin{+\!\!+}D')\mathbin{+\!\!+}[m]\bigr)$ という真の減少が各段で生じている。

<a id="t-translate_take_le"></a>
### 定理 前部分列による弱減少 (T.translate_take_le)

**主張** 任意の $m \in \mathbb{N}$ と任意のペア列 $L \in \mathrm{PairSeq}$ に対し
```math
\mathrm{tr}(\mathrm{take}\,m\,L) \ \preceq\ \mathrm{tr}\,L.
```

**証明** 標準ライブラリの `List.take_append_drop` より
```math
\mathrm{take}\,m\,L \mathbin{+\!\!+} \mathrm{drop}\,m\,L \ =\ L
```
である。主張の**右辺**に現れる $L$ をこの等式の左辺で置き換えると、示すべき命題は
```math
\mathrm{tr}(\mathrm{take}\,m\,L) \ \preceq\ \mathrm{tr}\bigl(\mathrm{take}\,m\,L \mathbin{+\!\!+} \mathrm{drop}\,m\,L\bigr)
```
と同一である。これは [(T.translate_append_ge)](#t-translate_append_ge) に
$C := \mathrm{take}\,m\,L$、$D := \mathrm{drop}\,m\,L$ を代入したものである。∎

**注（書き換えを右辺に限る理由）**
Lean の証明では書き換えを右辺に限定している（`conv_rhs`）。
左辺に現れる $L$ まで同時に書き換えると、示すべき命題が
```math
\mathrm{tr}\bigl(\mathrm{take}\,m\,(\mathrm{take}\,m\,L \mathbin{+\!\!+} \mathrm{drop}\,m\,L)\bigr)
 \ \preceq\ \mathrm{tr}\bigl(\mathrm{take}\,m\,L \mathbin{+\!\!+} \mathrm{drop}\,m\,L\bigr)
```
という形になり、[(T.translate_append_ge)](#t-translate_append_ge) の
$\mathrm{tr}\,C \preceq \mathrm{tr}(C \mathbin{+\!\!+} D)$ という形に一致しないためである。

**注（$\prec$ ではなく $\preceq$ であること）**
$m \ge \lvert L\rvert$ のとき $\mathrm{take}\,m\,L = L$ であり両辺は等しいから、$\prec$ に強めることはできない。
なお $m = \lvert L\rvert - 1$ かつ $L \ne []$ の場合には
$\mathrm{take}\,(\lvert L\rvert-1)\,L = \mathrm{dropLast}\,L$ であり、そのときは
[(T.translate_dropLast_decrease)](Mechanized.md#t-translate_dropLast_decrease) が
$\mathrm{tr}(\mathrm{dropLast}\,L) \prec \mathrm{tr}\,L$ という真の減少を与える。
本定理はこの $\mathrm{dropLast}$ の場合を任意の前部分列長 $m$ へ一般化したものであり、
その代償として結論が $\preceq$ に弱まっている。

---

## 頭部 $0$ の条項の再帰に対する兄弟方向の簡約補題 (Sibling-direction reduction lemmas for the head-`0` clause recursion)

Lean ソースはこの節見出しの下に宣言を 1 つも持たない。したがって本節に命題と証明の対はない。
見出しに付されたコメントが記録している事実は次のものであり、これは本章の宣言が上の 2 つに留まる理由を述べたものである。

**注（述語 $Q$ に対する構造帰納法は成立しない）**
項の述語
```math
Q(t) :\equiv \forall x \in \mathrm{Gterm}\,0\,t,\ x \prec t
```
（$\mathrm{Gterm}$ は [(D.Gterm)](Otembed.md#d-Gterm)）について、
「$t$ のすべての真部分項で $Q$ が成り立つ」ことから $Q(t)$ を導くことはできない。
実際、$b := \mathsf{P}(1,\mathsf{Z},\mathsf{Z})$、$t := \mathsf{P}(0,b,\mathsf{Z})$ とおくと次が成り立つ。

1. $\mathrm{Gterm}\,0\,\mathsf{Z} = \emptyset$（[(T.Gterm_Z)](Otembed.md#t-Gterm_Z)）。
   よって $Q(\mathsf{Z})$ は空な全称命題として真である。
2. $\mathrm{Gterm}\,0\,b = \{\mathsf{Z}\}$。
   実際 [(T.Gterm_P)](Otembed.md#t-Gterm_P) より
   $\mathrm{Gterm}\,0\,\mathsf{P}(1,\mathsf{Z},\mathsf{Z}) = \bigl(\text{if } 0 \le 1 \text{ then } \{\mathsf{Z}\} \cup \mathrm{Gterm}\,0\,\mathsf{Z} \text{ else } \emptyset\bigr) \cup \mathrm{Gterm}\,0\,\mathsf{Z}$
   であり、$0 \le 1$ は真、$\mathrm{Gterm}\,0\,\mathsf{Z} = \emptyset$ だから値は $\{\mathsf{Z}\}$ である。
   $\mathsf{Z} \prec \mathsf{P}(1,\mathsf{Z},\mathsf{Z})$ は [(T.olt_Z_P)](Mechanized.md#t-olt_Z_P) により成立するから、$Q(b)$ は真である。
3. $t$ の真部分項は $b$ と $\mathsf{Z}$ のみである（$b$ の真部分項は $\mathsf{Z}$ のみ）。
   よって 1, 2 より $t$ のすべての真部分項で $Q$ が成り立つ。
4. しかし $Q(t)$ は偽である。
   [(T.Gterm_P)](Otembed.md#t-Gterm_P) より
   $\mathrm{Gterm}\,0\,t = \bigl(\text{if } 0 \le 0 \text{ then } \{b\} \cup \mathrm{Gterm}\,0\,b \text{ else } \emptyset\bigr) \cup \mathrm{Gterm}\,0\,\mathsf{Z} = \{b, \mathsf{Z}\}$
   であるから $b \in \mathrm{Gterm}\,0\,t$ である。
   一方 [(T.olt_P_P)](Mechanized.md#t-olt_P_P) を
   $\mathsf{P}(1,\mathsf{Z},\mathsf{Z}) \prec \mathsf{P}(0,b,\mathsf{Z})$ に適用すると
   ```math
   b \prec t \iff 1 < 0 \ \vee\ (1 = 0 \wedge \mathsf{Z} \prec b) \ \vee\ (1 = 0 \wedge \mathsf{Z} = b \wedge \mathsf{Z} \prec \mathsf{Z})
   ```
   であり、$1 < 0$ は偽、$1 = 0$ も偽であるから 3 つの選言肢すべてが偽、すなわち $\neg(b \prec t)$ である。
   よって $Q(t)$ は偽である。
5. 項の大きさ $\mathrm{tsize}$（[(D.tsize)](Wfsum.md#d-tsize)）で測っても同じことが起こる。
   $\mathrm{tsize}\,\mathsf{Z} = 0$、$\mathrm{tsize}\,\mathsf{P}(a,x,y) = \mathrm{tsize}\,x + \mathrm{tsize}\,y + 1$ であるから
   $\mathrm{tsize}\,b = 0 + 0 + 1 = 1$、$\mathrm{tsize}\,t = 1 + 0 + 1 = 2$ である。
   $\mathrm{tsize}\,s < 2$ をみたす項 $s$ は $\mathsf{Z}$ と $\mathsf{P}(a,\mathsf{Z},\mathsf{Z})$（$a \in \mathbb{N}$）に限る。
   $Q(\mathsf{Z})$ は 1 より真であり、任意の $a$ について
   [(T.Gterm_P)](Otembed.md#t-Gterm_P) より
   $\mathrm{Gterm}\,0\,\mathsf{P}(a,\mathsf{Z},\mathsf{Z}) = \{\mathsf{Z}\}$（$0 \le a$ は任意の $a$ で真）であり、
   [(T.olt_Z_P)](Mechanized.md#t-olt_Z_P) より $\mathsf{Z} \prec \mathsf{P}(a,\mathsf{Z},\mathsf{Z})$ だから
   $Q(\mathsf{P}(a,\mathsf{Z},\mathsf{Z}))$ も真である。
   すなわち $\mathrm{tsize}\,s < \mathrm{tsize}\,t$ なるすべての項 $s$ で $Q(s)$ が成り立つが、4 より $Q(t)$ は偽である。

したがって、$Q$ 自身を帰納法の述語とする項の構造に関する帰納法（3, 4 による）も、
$\mathrm{tsize}$ に関する強帰納法（5 による）も、$Q$ の証明には使えない。
