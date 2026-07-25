[← 目次](README.md)

# Gterm — Buchholz の係数集合 $`G_u`$

三分岐記法 $`\mathrm{Three}`$（[(D.Three)](Mechanized.md#d-Three)）の項 $`t`$ に対し、
$`t`$ の中に添字 $`u`$ 以上の主要項の引数として現れる項の集合 $`G_u(t)`$ を定義し、
その要素判定と、要素が構造サイズを真に減らすことを証明する。
本章の宣言は 5 個で、うち定義が 1 個、定理が 4 個である。定理のうち
[(T.Gterm_tsize)](#t-Gterm_tsize) は項の構造に関する帰納法で証明され、
残る 3 個は定義の展開と 2 通りの場合分けのみで証明される。

$`G_u`$ は項から項の集合への**構文的**な操作である。順序数、値写像、崩壊関数
$`\psi`$ はこの章には現れず、
[(T.PSS_terminates_unconditional)](Final.md#t-PSS_terminates_unconditional) に至る経路の
どこにも現れない。

## 記法

この章で導入する Lean 名と数学記法の対応。

| Lean | 本文 | 意味 |
|---|---|---|
| `Gterm u t` | $`G_u(t)`$ | Buchholz の係数集合（項の集合） |

他の章で定義済みの記号については次のように書く。

| Lean | 本文 | 定義箇所 |
|---|---|---|
| `Three`, `Z`, `P a b c` | $`\mathrm{Three}`$, $`\mathsf{Z}`$, $`\mathsf{P}(a,b,c)`$ | [(D.Three)](Mechanized.md#d-Three) |
| `tsize t` | $`\lVert t\rVert`$ | [(D.tsize)](Wfsum.md#d-tsize) |

集合については、$`\mathrm{Three}`$ の部分集合を $`\mathrm{Set}\ \mathrm{Three}`$ と書き、
$`\emptyset`$ は空集合、$`X\cup Y`$ は和集合、$`\{b\}\cup X`$ は Lean の `insert b X` を表す。
和集合の要素判定 $`x\in X\cup Y \iff x\in X \vee x\in Y`$、
空集合の要素判定 $`\neg(x\in\emptyset)`$、
$`x\in\{b\}\cup X \iff x=b \vee x\in X`$ を随時用いる。

<a id="d-Gterm"></a>
### 定義 係数集合 (D.Gterm)

$`u\in\mathbb{N}`$ に対し、写像 $`G_u : \mathrm{Three}\to \mathrm{Set}\ \mathrm{Three}`$ を
項の構造に関する再帰で定める。

```math
G_u(\mathsf{Z}) := \emptyset, \qquad
G_u(\mathsf{P}(a,b,c)) := \Bigl(\text{if } u\le a \text{ then } \{b\}\cup G_u(b) \text{ else } \emptyset\Bigr)\ \cup\ G_u(c) .
```

すなわち

```math
G_u(\mathsf{P}(a,b,c)) = \begin{cases}
\{b\}\cup G_u(b)\cup G_u(c) & (u\le a) \cr
G_u(c) & (u>a)
\end{cases}
```

である（$`u\gt a`$ の場合は $`\emptyset\cup G_u(c)=G_u(c)`$ による）。
再帰呼び出しの引数 $`b`$, $`c`$ はいずれも $`\mathsf{P}(a,b,c)`$ の真部分項であるから、
この定義は構造帰納として整合的である。
条件式の中の再帰呼び出しの添字は $`u`$ のままであって $`a`$ ではないことに注意する。

<a id="t-Gterm_Z"></a>
### 定理 $`\mathsf{Z}`$ の係数集合 (T.Gterm_Z)

**主張** 任意の $`u\in\mathbb{N}`$ に対し $`G_u(\mathsf{Z}) = \emptyset`$。

**証明** [(D.Gterm)](#d-Gterm) の第 1 式そのものであり、両辺は定義により同一である。∎

この定理は Lean で `@[simp]` 補題として登録されているので、後続の章の `simp` 呼び出しから
暗黙に使われうる。

<a id="t-Gterm_P"></a>
### 定理 主要項の係数集合 (T.Gterm_P)

**主張** 任意の $`u,a\in\mathbb{N}`$, $`b,c\in\mathrm{Three}`$ に対し
```math
G_u(\mathsf{P}(a,b,c)) = \Bigl(\text{if } u\le a \text{ then } \{b\}\cup G_u(b) \text{ else } \emptyset\Bigr)\ \cup\ G_u(c) .
```

**証明** [(D.Gterm)](#d-Gterm) の第 2 式そのものであり、両辺は定義により同一である。∎

<a id="t-mem_Gterm_P"></a>
### 定理 主要項の係数集合の要素判定 (T.mem_Gterm_P)

**主張** 任意の $`u,a\in\mathbb{N}`$, $`b,c,x\in\mathrm{Three}`$ に対し
```math
x\in G_u(\mathsf{P}(a,b,c)) \iff \bigl(u\le a \ \wedge\ (x=b \ \vee\ x\in G_u(b))\bigr)\ \vee\ x\in G_u(c) .
```

**証明** [(T.Gterm_P)](#t-Gterm_P) で左辺を書き換えたうえで、命題 $`u\le a`$ の真偽で場合分けする。

- $`u\le a`$ が真のとき。条件式は $`\{b\}\cup G_u(b)`$ に簡約され、左辺は
  $`x\in(\{b\}\cup G_u(b))\cup G_u(c)`$ である。和集合の要素判定を 2 回用いて、これは
  ```math
  (x=b \ \vee\ x\in G_u(b))\ \vee\ x\in G_u(c)
  ```
  と同値である。他方、右辺の第 1 選言子 $`u\le a \wedge (x=b\vee x\in G_u(b))`$ において
  $`u\le a`$ は真であるから、右辺は $`(x=b\vee x\in G_u(b))\vee x\in G_u(c)`$ と同値である。
  両者は同一の命題であるから同値。

- $`u\le a`$ が偽のとき。条件式は $`\emptyset`$ に簡約され、左辺は $`x\in\emptyset\cup G_u(c)`$ である。
  和集合の要素判定と $`\neg(x\in\emptyset)`$ より、これは $`x\in G_u(c)`$ と同値である。
  他方、右辺の第 1 選言子は $`u\le a`$ が偽であるから偽であり、右辺は $`x\in G_u(c)`$ と同値である。
  よって同値。∎

<a id="t-Gterm_tsize"></a>
### 定理 係数は構造サイズを真に減らす (T.Gterm_tsize)

**主張** $`t,x\in\mathrm{Three}`$, $`v\in\mathbb{N}`$ とする。
$`x\in G_v(t)`$ ならば $`\lVert x\rVert \lt \lVert t\rVert`$。

ここで $`\lVert\cdot\rVert`$ は [(D.tsize)](Wfsum.md#d-tsize) の構造サイズ、すなわち
$`\lVert\mathsf{Z}\rVert = 1`$、$`\lVert\mathsf{P}(a,b,c)\rVert = \lVert b\rVert+\lVert c\rVert+1`$ である。

**証明** $`x`$ と $`v`$ を固定し、$`t`$ の構造に関する帰納法を行う。帰納法の述語は

```math
\Phi(t) :\equiv x\in G_v(t) \to \lVert x\rVert < \lVert t\rVert .
```

- **基底段** $`t=\mathsf{Z}`$：[(T.Gterm_Z)](#t-Gterm_Z) より $`G_v(\mathsf{Z})=\emptyset`$ であり、
  $`\neg(x\in\emptyset)`$ であるから前提が偽である。よって $`\Phi(\mathsf{Z})`$ が成り立つ。

- **帰納段** $`t=\mathsf{P}(a,b,c)`$：帰納法の仮定は $`\Phi(b)`$ と $`\Phi(c)`$ の 2 つである。
  前提 $`x\in G_v(\mathsf{P}(a,b,c))`$ を仮定し、[(T.mem_Gterm_P)](#t-mem_Gterm_P) を適用して
  次の 3 つの場合に分ける。
  結論は $`\lVert x\rVert \lt \lVert \mathsf{P}(a,b,c)\rVert = \lVert b\rVert+\lVert c\rVert+1`$ である。

  1. $`v\le a`$ かつ $`x=b`$ のとき。示すべきは $`\lVert b\rVert \lt \lVert b\rVert+\lVert c\rVert+1`$ である。
     $`\lVert c\rVert \ge 0`$ であるから $`\lVert b\rVert+\lVert c\rVert+1 \ge \lVert b\rVert+1 \gt \lVert b\rVert`$。

  2. $`v\le a`$ かつ $`x\in G_v(b)`$ のとき。帰納法の仮定 $`\Phi(b)`$ を適用して
     $`\lVert x\rVert \lt \lVert b\rVert`$ を得る。
     また 1 と同じ計算で $`\lVert b\rVert \lt \lVert b\rVert+\lVert c\rVert+1`$ であるから、
     $`\mathbb{N}`$ の $`\lt `$ の推移律により $`\lVert x\rVert \lt \lVert b\rVert+\lVert c\rVert+1`$。

  3. $`x\in G_v(c)`$ のとき。帰納法の仮定 $`\Phi(c)`$ を適用して
     $`\lVert x\rVert \lt \lVert c\rVert`$ を得る。
     $`\lVert b\rVert\ge 0`$ より $`\lVert c\rVert \le \lVert b\rVert+\lVert c\rVert \lt \lVert b\rVert+\lVert c\rVert+1`$
     であるから、$`\lVert x\rVert \lt \lVert b\rVert+\lVert c\rVert+1`$。

  （1–3 の自然数の不等式計算を Lean では `omega` が行っている。）
  いずれの場合も結論が得られたので $`\Phi(\mathsf{P}(a,b,c))`$。∎

## 後続の章での用いられ方

本章の宣言のうち後続の章の証明本文が名指しで引用するのは
[(D.Gterm)](#d-Gterm), [(T.mem_Gterm_P)](#t-mem_Gterm_P), [(T.Gterm_tsize)](#t-Gterm_tsize) の
3 つであり、引用するのは `Nrm`, `Nrmstep` の 2 モジュールのみである。
[(T.Gterm_Z)](#t-Gterm_Z) は `@[simp]` として `simp` から暗黙に使われ、
[(T.Gterm_P)](#t-Gterm_P) は本章の [(T.mem_Gterm_P)](#t-mem_Gterm_P) の証明でのみ用いられる。
