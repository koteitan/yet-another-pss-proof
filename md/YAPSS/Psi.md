[← 目次](README.md)

# Psi — Buchholz の崩壊関数 $\psi_v$（順序数の上での構成）

本章は Buchholz 1986 §1 の崩壊関数 $\psi_v$ を Mathlib の順序数型 `Ordinal` の上に移植する。
基数 $\Omega_v$、生成作用素 $\mathrm{Cstep}$ とその有限反復 $\mathrm{Citer}$、その可算合併 $\mathrm{Cset}$、
そして $<$ に関する整礎再帰で定義される $\psi$、および加法主性の述語 $\mathrm{addprinc}$ を導入する。
宣言は 9 個で、うち定義が 7 個、定理が 2 個である。本章は順序数を使う唯一の章であり、
ここで定義した記号は [(D.oV)](Otembed.md#d-oV) が用いるが、停止性の最終結論
[(T.PSS_terminates_unconditional)](Final.md#t-PSS_terminates_unconditional) に至る経路は順序数を用いない。

## 記法

この章で用いる Lean 名と数学記法の対応。

| Lean | 本文 | 意味 |
|---|---|---|
| `Ordinal.{u}` | $\mathrm{Ord}$ | 順序数の型（宇宙 $u$） |
| `Cardinal.{u}` | — | 濃度の型 |
| `ℵ_ v` | $\aleph_v$ | `Cardinal.aleph` の $v$ 番目の値（$v:\mathbb{N}$ を順序数とみなして適用） |
| `c.ord` | $\mathrm{ord}(c)$ | 濃度 $c$ をもつ最小の順序数 |
| `Om v` | $\Omega_v$ | 本章で定める基数（[(D.Om)](#d-Om)） |
| `Set.Iio α` | $\mathrm{Iio}(\alpha)$ | $\{\xi\in\mathrm{Ord}\mid \xi<\alpha\}$ |
| `Set.image2 (· + ·) X X` | $\{\beta+\gamma \mid \beta\in X,\ \gamma\in X\}$ | $X$ の 2 元の和全体 |
| `f '' A` | $f\,''A$ | $\{f(x)\mid x\in A\}$ |
| `⋃ u : ℕ, S u` | $\bigcup_{u\in\mathbb{N}} S_u$ | 可算合併 |
| `f^[n]` | $f^{[n]}$ | $f$ の $n$ 回反復 |
| `sInf S` | $\inf S$ | 順序数の集合 $S$ の下限（[(D.psi)](#d-psi) の補足で意味を固定する） |
| `Cstep p α X` | $\mathrm{Cstep}_{p,\alpha}(X)$ | 1 段生成作用素（[(D.Cstep)](#d-Cstep)） |
| `Citer p α v n` | $C^{(n)}_{p,\alpha,v}$ | 生成作用素の $n$ 回反復（[(D.Citer)](#d-Citer)） |
| `Cset p α v` | $C^{p}_{v}(\alpha)$ | その可算合併（[(D.Cset)](#d-Cset)） |
| `psi α v` | $\psi_v(\alpha)$ | 崩壊関数（[(D.psi)](#d-psi)） |
| `Psi v α` | $\Psi_v(\alpha)$ | 引数順序を入れ替えた別名（[(D.Psi)](#d-Psi)） |
| `addprinc δ` | $\mathrm{addprinc}(\delta)$ | 加法主性（[(D.addprinc)](#d-addprinc)） |

以下で用いる順序数側の約束を固定しておく。

- $\mathrm{Ord}$ 上の $<$ は整礎である（Mathlib の `Ordinal.lt_wf`）。すなわち
  $\mathrm{WellFounded}\,(<)$ が成り立つ。
- $+$ は順序数の加法であり、可換ではない。
- $0$ は $\mathrm{Ord}$ の最小元であり、$1$ は $0$ の後続である。したがって
  $\xi<1 \iff \xi = 0$、すなわち $\mathrm{Iio}(1)=\{0\}$ である。
- 集合演算の記号は Mathlib の `Set` のものであり、$X\subseteq Y$ は
  $\forall \delta,\ \delta\in X \to \delta\in Y$ を意味する。
- Lean の `p : Ordinal → ℕ → Ordinal` はカリー化された 2 引数関数である。本文では
  $p(\xi,u)$ と書く。

Lean ファイル冒頭の移植規約（Isabelle の `ord/psi.thy` からの移植）は次の通りである。
集合論の $V$ を順序数型 `Ordinal.{0}` に、$x\in\mathrm{elts}\,\alpha$ を $x<\alpha$ に、
順序数の $V$-集合を `Set Ordinal` に、超限再帰 `transrec` を `WellFounded.fix Ordinal.lt_wf` に、
`LEAST` を `sInf` に対応させる。

---

## 基数 $\Omega_v$

<a id="d-Om"></a>
### 定義 $\Omega_v$ (D.Om)

$v\in\mathbb{N}$ に対し

$$\Omega_v := \begin{cases}
1 & (v = 0)\\
\mathrm{ord}(\aleph_v) & (v \ne 0)
\end{cases}$$

Lean では

```lean
noncomputable def Om (v : ℕ) : Ordinal.{u} := if v = 0 then 1 else (ℵ_ v).ord
```

である。ここで $\aleph_v$ は Mathlib の `Cardinal.aleph` に $v\in\mathbb{N}$ を順序数として与えた値、
$\mathrm{ord}(c)$ は濃度が $c$ である最小の順序数である。
場合分けの条件は $v=0$ か否かのみであるから、$v\ne 0$ のすべての $v$ について
$\Omega_v = \mathrm{ord}(\aleph_v)$ である。

$v=0$ の場合に $\mathrm{ord}(\aleph_0)=\omega$ ではなく $1$ と定めるのは Buchholz 1986 の規約であり、
Lean ファイル冒頭のコメント「`Ω_v = ℵ_v` (`v > 0`), `Ω_0 = 1`」がこれを述べている。
この規約により $\mathrm{Iio}(\Omega_0) = \mathrm{Iio}(1) = \{0\}$ である。

PSS の記法 [(D.Three)](Mechanized.md#d-Three) の添字は自然数のみであるから、崩壊関数の添字も
$\mathbb{N}$ で添字づけられている。$\psi_\omega$ は本章のどこにも現れない。

<a id="t-Om_zero"></a>
### 定理 $\Omega_0 = 1$ (T.Om_zero)

**主張** $\Omega_0 = 1$。

**証明** [(D.Om)](#d-Om) の右辺の場合分けの条件は $v = 0$ である。$v := 0$ に対しこの条件は
$0 = 0$ であり真であるから、`if` 式は第 1 分岐の値 $1$ に簡約される。よって $\Omega_0 = 1$。∎

（Lean 側は `simp [Om]`。`simp` が行うのは `Om` の展開と、真である分岐条件による `if` の簡約の 2 段である。）

<a id="t-Om_of_pos"></a>
### 定理 正の添字での $\Omega_v$ (T.Om_of_pos)

**主張** $v\in\mathbb{N}$ が $0<v$ をみたすならば $\Omega_v = \mathrm{ord}(\aleph_v)$。

**証明** まず $\mathbb{N}$ において $0<v$ から $v\ne 0$ が従う。実際、$v=0$ と仮定すると
$0<v$ は $0<0$ となり、$<$ の非反射性に反する（Lean 側の `Nat.pos_iff_ne_zero.1 hv` がこの含意である）。
よって [(D.Om)](#d-Om) の場合分けの条件 $v=0$ は偽であり、`if` 式は第 2 分岐の値
$\mathrm{ord}(\aleph_v)$ に簡約される。∎

---

## 集合 $C_v(\alpha)$ と崩壊関数 $\psi_v(\alpha)$（Buchholz §1）

Lean ファイルのこの節のコメントは、$C_v(\alpha)$ を
「$\mathrm{Iio}(\Omega_v)$ を含み、$+$ と $\xi\mapsto \psi_u(\xi)$（$\xi<\alpha$, $u\in\mathbb{N}$）で
生成される最小の集合」と述べ、それを $\mathrm{Iio}(\Omega_v)$ から出発する有限反復の可算合併として
構成すると述べている（Buchholz の付加条件 $\xi\in C_u(\xi)$ は彼の Remark に従って落とす）。
以下の 3 つの定義がこの構成であり、[(D.Cset)](#d-Cset) の補足 2・補足 3 でこの「最小性」を
述語 $\mathrm{Cl}_{p,\alpha,v}$ として書き下して証明する。

<a id="d-Cstep"></a>
### 定義 1 段生成作用素 (D.Cstep)

$p : \mathrm{Ord}\to\mathbb{N}\to\mathrm{Ord}$、$\alpha\in\mathrm{Ord}$、$X\subseteq\mathrm{Ord}$ に対し

$$\mathrm{Cstep}_{p,\alpha}(X) :=
X \ \cup\ \{\beta+\gamma \mid \beta\in X,\ \gamma\in X\}
\ \cup\ \bigcup_{u\in\mathbb{N}}\ \{\, p(\xi,u) \mid \xi\in X\cap\mathrm{Iio}(\alpha) \,\}.$$

Lean では

```lean
def Cstep (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u}) (X : Set Ordinal.{u}) :
    Set Ordinal.{u} :=
  X ∪ Set.image2 (· + ·) X X ∪ ⋃ u : ℕ, (fun ξ => p ξ u) '' (X ∩ Set.Iio α)
```

である（`∪` は左結合であるが、合併は結合的であるから括弧の付け方によらず同じ集合である）。

**補足 1（成分表示）.** 任意の $\delta\in\mathrm{Ord}$ について

$$\delta\in\mathrm{Cstep}_{p,\alpha}(X)
\iff
\delta\in X
\ \vee\ \bigl(\exists \beta\,\gamma,\ \beta\in X \wedge \gamma\in X \wedge \delta=\beta+\gamma\bigr)
\ \vee\ \bigl(\exists u\in\mathbb{N},\ \exists\xi,\ \xi\in X \wedge \xi<\alpha \wedge \delta=p(\xi,u)\bigr).$$

*証明.* Mathlib の集合演算の定義を順に開く。
$\delta\in A\cup B \iff \delta\in A \vee \delta\in B$、
$\delta\in \mathrm{image2}\ f\ X\ Y \iff \exists \beta\,\gamma,\ \beta\in X\wedge\gamma\in Y\wedge f(\beta,\gamma)=\delta$、
$\delta\in\bigcup_{u} S_u \iff \exists u,\ \delta\in S_u$、
$\delta\in f\,''A \iff \exists \xi,\ \xi\in A \wedge f(\xi)=\delta$、
$\xi\in X\cap\mathrm{Iio}(\alpha) \iff \xi\in X \wedge \xi<\alpha$。
これらを合成すると右辺の 3 選言が得られる。$\square$

**補足 2（$X$ は自分自身の像に含まれる）.** $X \subseteq \mathrm{Cstep}_{p,\alpha}(X)$。

*証明.* $\delta\in X$ ならば補足 1 の第 1 選言がみたされる。$\square$

**補足 3（$X$ に関する単調性）.** $X\subseteq Y$ ならば
$\mathrm{Cstep}_{p,\alpha}(X)\subseteq \mathrm{Cstep}_{p,\alpha}(Y)$。

*証明.* $\delta\in\mathrm{Cstep}_{p,\alpha}(X)$ とし、補足 1 の 3 選言で場合分けする。
第 1 の場合、$\delta\in X\subseteq Y$ より第 1 選言が $Y$ について成立する。
第 2 の場合、$\beta,\gamma\in X\subseteq Y$ かつ $\delta=\beta+\gamma$ であるから第 2 選言が成立する。
第 3 の場合、$\xi\in X\subseteq Y$、$\xi<\alpha$、$\delta=p(\xi,u)$ であるから第 3 選言が成立する。
いずれの場合も補足 1 により $\delta\in\mathrm{Cstep}_{p,\alpha}(Y)$。$\square$

**補足 4（$p$ は $\mathrm{Iio}(\alpha)$ 上の値でしか効かない）.**
$p, q : \mathrm{Ord}\to\mathbb{N}\to\mathrm{Ord}$ が
$\forall \xi,\ \xi<\alpha \to \forall u\in\mathbb{N},\ p(\xi,u)=q(\xi,u)$ をみたすならば、
すべての $X$ について $\mathrm{Cstep}_{p,\alpha}(X)=\mathrm{Cstep}_{q,\alpha}(X)$。

*証明.* 補足 1 の第 1・第 2 選言は $p$ を含まない。第 3 選言に現れる $\xi$ は $\xi<\alpha$ を
みたすものに限られるから、仮定より $\delta=p(\xi,u)$ と $\delta=q(\xi,u)$ は同値である。
よって 3 選言の全体が同値であり、外延性から 2 つの集合は等しい。$\square$

この補足 4 は [(D.psi)](#d-psi) で使う。そこでは $p$ として「$\xi<\alpha$ のとき $\psi_u(\xi)$、
そうでないとき $0$」という切り詰めた関数が現れるが、補足 4 により切り詰めの外側の値 $0$ は
結果に影響しない。

<a id="d-Citer"></a>
### 定義 生成作用素の有限反復 (D.Citer)

$p$、$\alpha$、$v\in\mathbb{N}$、$n\in\mathbb{N}$ に対し

$$C^{(n)}_{p,\alpha,v} := \bigl(\mathrm{Cstep}_{p,\alpha}\bigr)^{[n]}\bigl(\mathrm{Iio}(\Omega_v)\bigr).$$

Lean では

```lean
def Citer (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u}) (v : ℕ) (n : ℕ) :
    Set Ordinal.{u} :=
  (Cstep p α)^[n] (Set.Iio (Om v))
```

である（[(D.Om)](#d-Om)、[(D.Cstep)](#d-Cstep)）。反復 $f^{[n]}$ は Mathlib の `Nat.iterate` であり、
$f^{[0]}(a) = a$、$f^{[k+1]}(a) = f^{[k]}(f(a))$ で定義される。

**補足 1（漸化式）.** 次の 2 式が成り立つ。

$$C^{(0)}_{p,\alpha,v} = \mathrm{Iio}(\Omega_v),
\qquad
C^{(n+1)}_{p,\alpha,v} = \mathrm{Cstep}_{p,\alpha}\bigl(C^{(n)}_{p,\alpha,v}\bigr).$$

*証明.* 第 1 式は $f^{[0]}(a)=a$ そのものである。第 2 式のために、任意の
$f:\mathrm{Set}\,\mathrm{Ord}\to\mathrm{Set}\,\mathrm{Ord}$ と $a$ について

$$\Phi(n) :\equiv \forall a,\ f^{[n+1]}(a) = f\bigl(f^{[n]}(a)\bigr)$$

を $n$ に関する自然数の帰納法で示す。

- 基底段 $n=0$：$f^{[1]}(a) = f^{[0]}(f(a)) = f(a)$ であり、また $f(f^{[0]}(a)) = f(a)$ である。
  よって $\Phi(0)$。
- 帰納段：帰納法の仮定を $\Phi(n)$、すなわち $\forall a,\ f^{[n+1]}(a)=f(f^{[n]}(a))$ とする。
  任意の $a$ について
  $$f^{[n+2]}(a) = f^{[n+1]}(f(a)) \overset{\Phi(n)}{=} f\bigl(f^{[n]}(f(a))\bigr) = f\bigl(f^{[n+1]}(a)\bigr)$$
  である（第 1 と第 3 の等号は定義式 $f^{[k+1]}(a)=f^{[k]}(f(a))$）。よって $\Phi(n+1)$。

$f := \mathrm{Cstep}_{p,\alpha}$、$a := \mathrm{Iio}(\Omega_v)$ とおけば第 2 式を得る。$\square$
（これは Mathlib の `Function.iterate_succ_apply'` である。）

**補足 2（$n$ について増大する）.** 任意の $m,n\in\mathbb{N}$ について
$m\le n \Rightarrow C^{(m)}_{p,\alpha,v}\subseteq C^{(n)}_{p,\alpha,v}$。

*証明.* 2 段階に分ける。

第 1 段：$\Psi(n) :\equiv C^{(n)}_{p,\alpha,v}\subseteq C^{(n+1)}_{p,\alpha,v}$ を
$n$ に関する自然数の帰納法で示す。

- 基底段 $n=0$：補足 1 より $C^{(1)} = \mathrm{Cstep}_{p,\alpha}(C^{(0)})$ であり、
  [(D.Cstep)](#d-Cstep) の補足 2 より $C^{(0)}\subseteq \mathrm{Cstep}_{p,\alpha}(C^{(0)})=C^{(1)}$。
  よって $\Psi(0)$。
- 帰納段：帰納法の仮定を $\Psi(n)$、すなわち $C^{(n)}\subseteq C^{(n+1)}$ とする。
  [(D.Cstep)](#d-Cstep) の補足 3（単調性）を $X:=C^{(n)}$、$Y:=C^{(n+1)}$ に適用すると
  $\mathrm{Cstep}_{p,\alpha}(C^{(n)})\subseteq \mathrm{Cstep}_{p,\alpha}(C^{(n+1)})$、
  すなわち補足 1 により $C^{(n+1)}\subseteq C^{(n+2)}$。よって $\Psi(n+1)$。

第 2 段：$\Theta(k) :\equiv \forall m\in\mathbb{N},\ C^{(m)}\subseteq C^{(m+k)}$ を
$k$ に関する自然数の帰納法で示す。

- 基底段 $k=0$：$C^{(m)}\subseteq C^{(m)}$ は $\subseteq$ の反射性である。よって $\Theta(0)$。
- 帰納段：帰納法の仮定を $\Theta(k)$ とする。任意の $m$ について
  $C^{(m)}\subseteq C^{(m+k)}$ であり、第 1 段の $\Psi(m+k)$ より
  $C^{(m+k)}\subseteq C^{(m+k+1)}$ であるから、$\subseteq$ の推移性により
  $C^{(m)}\subseteq C^{(m+k+1)}$。よって $\Theta(k+1)$。

$m\le n$ ならば $k := n-m$ とおくと $m+k=n$ であるから、$\Theta(k)$ が結論を与える。$\square$

**補足 3（$p$ の切り詰めに依らない）.**
$p,q$ が $\forall \xi,\ \xi<\alpha\to\forall u\in\mathbb{N},\ p(\xi,u)=q(\xi,u)$ をみたすならば、
すべての $n$ について $C^{(n)}_{p,\alpha,v} = C^{(n)}_{q,\alpha,v}$。

*証明.* $\Xi(n) :\equiv C^{(n)}_{p,\alpha,v}=C^{(n)}_{q,\alpha,v}$ を $n$ に関する自然数の帰納法で示す。

- 基底段 $n=0$：補足 1 よりどちらも $\mathrm{Iio}(\Omega_v)$ であるから $\Xi(0)$。
- 帰納段：帰納法の仮定を $\Xi(n)$ とする。補足 1 と
  [(D.Cstep)](#d-Cstep) の補足 4 により
  $$C^{(n+1)}_{p,\alpha,v}
  = \mathrm{Cstep}_{p,\alpha}\bigl(C^{(n)}_{p,\alpha,v}\bigr)
  = \mathrm{Cstep}_{q,\alpha}\bigl(C^{(n)}_{p,\alpha,v}\bigr)
  \overset{\Xi(n)}{=} \mathrm{Cstep}_{q,\alpha}\bigl(C^{(n)}_{q,\alpha,v}\bigr)
  = C^{(n+1)}_{q,\alpha,v}$$
  である。よって $\Xi(n+1)$。$\square$

<a id="d-Cset"></a>
### 定義 生成集合 $C^p_v(\alpha)$ (D.Cset)

$$C^p_v(\alpha) := \bigcup_{n\in\mathbb{N}} C^{(n)}_{p,\alpha,v}$$

（[(D.Citer)](#d-Citer)）。Lean では

```lean
def Cset (p : Ordinal.{u} → ℕ → Ordinal.{u}) (α : Ordinal.{u}) (v : ℕ) : Set Ordinal.{u} :=
  ⋃ n : ℕ, Citer p α v n
```

である。

**補足 1（成分表示）.**
$\delta\in C^p_v(\alpha) \iff \exists n\in\mathbb{N},\ \delta\in C^{(n)}_{p,\alpha,v}$。

*証明.* 可算合併の定義 $\delta\in\bigcup_{n} S_n \iff \exists n,\ \delta\in S_n$ そのものである。$\square$

**補足 2（生成条件）.** 集合 $Y\subseteq\mathrm{Ord}$ について、条件 $\mathrm{Cl}_{p,\alpha,v}(Y)$ を

$$\mathrm{Cl}_{p,\alpha,v}(Y) :\iff
\mathrm{Iio}(\Omega_v)\subseteq Y
\ \wedge\ \bigl(\forall \beta\,\gamma,\ \beta\in Y \to \gamma\in Y \to \beta+\gamma\in Y\bigr)
\ \wedge\ \bigl(\forall u\in\mathbb{N},\ \forall\xi,\ \xi\in Y \to \xi<\alpha \to p(\xi,u)\in Y\bigr)$$

と定める。このとき $\mathrm{Cl}_{p,\alpha,v}\bigl(C^p_v(\alpha)\bigr)$ が成り立つ。

*証明.* 3 つの連言子を順に示す。

1. [(D.Citer)](#d-Citer) の補足 1 より $C^{(0)}_{p,\alpha,v}=\mathrm{Iio}(\Omega_v)$ であり、
   本項の補足 1 の $n:=0$ の場合により $C^{(0)}_{p,\alpha,v}\subseteq C^p_v(\alpha)$。
2. $\beta,\gamma\in C^p_v(\alpha)$ とする。本項の補足 1 より $\beta\in C^{(m)}$、$\gamma\in C^{(n)}$ なる
   $m,n$ が取れる。$k := \max(m,n)$ とおくと $m\le k$ かつ $n\le k$ であるから、
   [(D.Citer)](#d-Citer) の補足 2 より $\beta,\gamma\in C^{(k)}$。
   [(D.Cstep)](#d-Cstep) の補足 1 の第 2 選言により
   $\beta+\gamma\in\mathrm{Cstep}_{p,\alpha}(C^{(k)}) = C^{(k+1)}$
   （最後の等号は [(D.Citer)](#d-Citer) の補足 1）。再び本項の補足 1 より $\beta+\gamma\in C^p_v(\alpha)$。
3. $u\in\mathbb{N}$、$\xi\in C^p_v(\alpha)$、$\xi<\alpha$ とする。本項の補足 1 より $\xi\in C^{(n)}$ なる
   $n$ が取れる。[(D.Cstep)](#d-Cstep) の補足 1 の第 3 選言により
   $p(\xi,u)\in\mathrm{Cstep}_{p,\alpha}(C^{(n)})=C^{(n+1)}$（[(D.Citer)](#d-Citer) の補足 1）
   であり、本項の補足 1 より $p(\xi,u)\in C^p_v(\alpha)$。$\square$

**補足 3（最小性）.** $\mathrm{Cl}_{p,\alpha,v}(Y)$ をみたす任意の $Y$ について
$C^p_v(\alpha)\subseteq Y$。

*証明.* $\Lambda(n) :\equiv C^{(n)}_{p,\alpha,v}\subseteq Y$ を $n$ に関する自然数の帰納法で示す。

- 基底段 $n=0$：$C^{(0)}_{p,\alpha,v}=\mathrm{Iio}(\Omega_v)\subseteq Y$ は
  $\mathrm{Cl}_{p,\alpha,v}(Y)$ の第 1 連言子である。よって $\Lambda(0)$。
- 帰納段：帰納法の仮定を $\Lambda(n)$、すなわち $C^{(n)}\subseteq Y$ とする。
  $\delta\in C^{(n+1)} = \mathrm{Cstep}_{p,\alpha}(C^{(n)})$ を取り、
  [(D.Cstep)](#d-Cstep) の補足 1 の 3 選言で場合分けする。
  - $\delta\in C^{(n)}$ の場合：$\Lambda(n)$ より $\delta\in Y$。
  - $\delta=\beta+\gamma$、$\beta,\gamma\in C^{(n)}$ の場合：$\Lambda(n)$ より $\beta,\gamma\in Y$、
    $\mathrm{Cl}_{p,\alpha,v}(Y)$ の第 2 連言子より $\beta+\gamma\in Y$。
  - $\delta=p(\xi,u)$、$\xi\in C^{(n)}$、$\xi<\alpha$ の場合：$\Lambda(n)$ より $\xi\in Y$、
    $\mathrm{Cl}_{p,\alpha,v}(Y)$ の第 3 連言子より $p(\xi,u)\in Y$。

  よって $\Lambda(n+1)$。

本項の補足 1 より $\delta\in C^p_v(\alpha)$ ならある $n$ で $\delta\in C^{(n)}\subseteq Y$ であるから、
$C^p_v(\alpha)\subseteq Y$。$\square$

補足 2 と補足 3 が、Lean のコメントにいう「$\mathrm{Iio}(\Omega_v)$ を含み、$+$ と
$\xi\mapsto p(\xi,u)$（$\xi<\alpha$）で生成される最小の集合」の内容である。有限反復の可算合併がこれを与えるのは、条件
$\mathrm{Cl}_{p,\alpha,v}$ の生成規則がいずれも有限個（2 個または 1 個）の要素からの生成であり、
$C^p_v(\alpha)$ の元はすべて有限回の生成で得られるからである（補足 2 の証明の 2, 3 で
$\max(m,n)$ と $n+1$ を取った箇所がこの有限性の使用である）。

**補足 4（$p$ の切り詰めに依らない）.**
$p,q$ が $\forall\xi,\ \xi<\alpha\to\forall u\in\mathbb{N},\ p(\xi,u)=q(\xi,u)$ をみたすならば
$C^p_v(\alpha)=C^q_v(\alpha)$。

*証明.* [(D.Citer)](#d-Citer) の補足 3 よりすべての $n$ で
$C^{(n)}_{p,\alpha,v}=C^{(n)}_{q,\alpha,v}$ であるから、本項の補足 1 の右辺
$\exists n,\ \delta\in C^{(n)}$ が両者で同値であり、外延性から 2 つの集合は等しい。$\square$

---

## 小ささ（Smallness）

Lean ファイルのこの節見出し（`/-! ### Smallness -/`）の下に宣言はない。
この節が担うはずだった内容（$C^p_v(\alpha)$ の濃度が $\Omega_{v+1}$ 未満であること）は、
現在の Lean ファイルには形式化されていない。

---

## $\psi$ の定義可能性

<a id="d-psi"></a>
### 定義 崩壊関数 $\psi$ (D.psi)

$\mathrm{Ord}$ 上の $<$ に関する整礎再帰で、関数 $\psi : \mathrm{Ord}\to\mathbb{N}\to\mathrm{Ord}$ を定める。
Lean では

```lean
noncomputable def psi : Ordinal.{u} → ℕ → Ordinal.{u} :=
  Ordinal.lt_wf.fix (C := fun _ => ℕ → Ordinal.{u}) fun α IH v =>
    sInf {γ | γ ∉ Cset (fun ξ u => if h : ξ < α then IH ξ h u else 0) α v}
```

である。$\psi_v(\alpha) := \psi(\alpha, v)$ と書く。

**整礎再帰の道具.** `WellFounded.fix` は、整礎関係 $r$ 上の関数を
$F : \forall x,\ (\forall y,\ r\,y\,x \to C(y)) \to C(x)$ から作る作用素であり、
その唯一の性質は

$$\mathrm{fix}\,F\,x = F\,x\,\bigl(\lambda y\,\_.\ \mathrm{fix}\,F\,y\bigr)$$

（Lean の `WellFounded.fix_eq`）である。本定義では
$r$ は $\mathrm{Ord}$ 上の $<$（整礎性は `Ordinal.lt_wf`）、$C(x)$ は $\mathbb{N}\to\mathrm{Ord}$、
$F$ は

$$F(\alpha)(g)(v) := \inf\ \bigl\{\gamma \ \bigm|\ \gamma\notin C^{\,p_{\alpha,g}}_v(\alpha)\bigr\},
\qquad
p_{\alpha,g}(\xi,u) := \begin{cases} g(\xi)(u) & (\xi<\alpha)\\ 0 & (\xi\not<\alpha)\end{cases}$$

である（[(D.Cset)](#d-Cset)）。Lean の `if h : ξ < α then IH ξ h u else 0` は依存条件分岐であり、
真の分岐では条件の証明 $h : \xi<\alpha$ が `IH` に渡される。これが「$\xi<\alpha$ でのみ再帰呼び出しをしてよい」
という整礎再帰の制約の実現である。

**補足 1（不動点方程式）.** 任意の $\alpha\in\mathrm{Ord}$、$v\in\mathbb{N}$ について

$$\psi_v(\alpha) = \inf\ \bigl\{\gamma \ \bigm|\ \gamma\notin C^{\,p_\alpha}_v(\alpha)\bigr\},
\qquad
p_\alpha(\xi,u) = \begin{cases}\psi_u(\xi) & (\xi<\alpha)\\ 0 & (\xi\not<\alpha)\end{cases}$$

が成り立つ。

*証明.* $\psi = \mathrm{fix}\,F$ であるから、`fix_eq` を $x:=\alpha$ に適用して

$$\psi(\alpha) = F(\alpha)\bigl(\lambda \xi\,\_.\ \psi(\xi)\bigr)$$

を得る。両辺を $v$ に適用すると、$F$ の定義より右辺は
$\inf\{\gamma\mid\gamma\notin C^{\,p_{\alpha,g}}_v(\alpha)\}$（ただし $g := \lambda\xi\,\_.\ \psi(\xi)$）である。
この $g$ に対して
$p_{\alpha,g}(\xi,u) = g(\xi)(u) = \psi(\xi)(u) = \psi_u(\xi)$（$\xi<\alpha$ のとき）、
$p_{\alpha,g}(\xi,u)=0$（$\xi\not<\alpha$ のとき）であるから、$p_{\alpha,g}=p_\alpha$ である。$\square$

**補足 2（切り詰めの除去）.** $\bar\psi(\xi,u):=\psi_u(\xi)$ とおくと
$C^{\,p_\alpha}_v(\alpha) = C^{\,\bar\psi}_v(\alpha)$ である。

*証明.* $\xi<\alpha$ なるすべての $\xi$ と $u$ について $p_\alpha(\xi,u)=\psi_u(\xi)=\bar\psi(\xi,u)$
であるから、[(D.Cset)](#d-Cset) の補足 4 が適用できる。$\square$

そこで

$$C_v(\alpha) := C^{\,\bar\psi}_v(\alpha)$$

と書くと、補足 1 と補足 2 から

$$\psi_v(\alpha) = \inf\ \bigl\{\gamma \ \bigm|\ \gamma\notin C_v(\alpha)\bigr\}$$

を得る。$C_v(\alpha)$ の定義に $\psi$ が現れるが、[(D.Cstep)](#d-Cstep) の補足 4 により
$\psi$ が参照されるのは $\mathrm{Iio}(\alpha)$ 上の値のみであるから、この式は $\alpha$ に関する
整礎再帰として整合的である。

**補足 3（`sInf` の意味）.** Mathlib において `Ordinal` は
`WellFoundedLT.conditionallyCompleteLinearOrderBot` による
`ConditionallyCompleteLinearOrderBot` のインスタンスであり、そこでの `sInf` は

$$\inf S = \begin{cases} S\ \text{の最小元} & (S\ne\emptyset)\\ 0 & (S=\emptyset)\end{cases}$$

である（$S\ne\emptyset$ の場合は整礎性から最小元が存在し、`WellFounded.min` がそれを与える。
$S=\emptyset$ の場合の値は $\bot$ であり、$\mathrm{Ord}$ では $\bot=0$）。したがって

$$\bigl\{\gamma \mid \gamma\notin C_v(\alpha)\bigr\} \ne \emptyset
\ \Longrightarrow\
\psi_v(\alpha)\notin C_v(\alpha)\ \wedge\ \forall\gamma\notin C_v(\alpha),\ \psi_v(\alpha)\le\gamma$$

であり、この場合に限り $\psi_v(\alpha)$ は「$C_v(\alpha)$ に属さない最小の順序数」である。

**補足 4（補集合の非空性は本ファイルで証明されていない）.**
補足 3 の前提 $\{\gamma\mid\gamma\notin C_v(\alpha)\}\ne\emptyset$ が成り立つべき理由として
Lean のコメントが挙げているのは Buchholz 補題 1.2(c)、すなわち
$C_v(\alpha)$ の濃度が $\aleph_{v+1}$ 未満であること（$C_v(\alpha)$ は $\mathrm{Iio}(\Omega_v)$ から
$+$ と可算個の写像 $\psi_u$ で生成されるから）である。濃度が $\aleph_{v+1}$ 未満の集合は
濃度 $\aleph_{v+1}$ の集合 $\mathrm{Iio}(\Omega_{v+1})$ を包含しないから、
$\mathrm{Iio}(\Omega_{v+1})\setminus C_v(\alpha)\ne\emptyset$ が従う。
ただしこの論法も、その結論も、現在の Lean ファイルには宣言として存在しない
（「小ささ（Smallness）」節および「濃度評価」節に宣言がない）。
`sInf` は空集合に対しても値 $0$ を返すから、`psi` は関数としては全域に定義されている。
本文で $\psi_v(\alpha)$ に「$C_v(\alpha)$ に属さない最小の順序数」という読みを与えるときは、
つねにこの非空性を前提としていることに注意する。

<a id="d-Psi"></a>
### 定義 引数順序を入れ替えた $\Psi$ (D.Psi)

$$\Psi_v(\alpha) := \psi_v(\alpha) \qquad (v\in\mathbb{N},\ \alpha\in\mathrm{Ord})$$

（[(D.psi)](#d-psi)）。Lean では

```lean
noncomputable def Psi (v : ℕ) (α : Ordinal) : Ordinal := psi α v
```

であり、`psi` の 2 引数を入れ替えただけの別名である（Buchholz の慣用的な引数順序
$\psi_v(\alpha)$ に合わせた表記）。新しい内容はもたない。

---

## $C_v(\alpha)$ の生成に関する性質（Buchholz §1, 条件 C1–C3）

Lean ファイルのこの節見出し（`/-! ## Closure properties of C_v(α) (Buchholz §1, conditions C1–C3) -/`）
の下に宣言はない。Buchholz の条件 C1–C3 は現在の Lean ファイルには形式化されていない。
$C^p_v(\alpha)$ が [(D.Cset)](#d-Cset) の補足 2 の条件 $\mathrm{Cl}_{p,\alpha,v}$ をみたすことと
その最小性は、Lean 側には宣言がないので本文でも [(D.Cset)](#d-Cset) の補足として示した。

---

## $\psi_v$ の基本性質（Buchholz 補題 1.2）

Lean ファイルのこの節見出しの下に宣言はない。

---

## $\alpha$ に関する $C_v(\alpha)$ と $\psi_v(\alpha)$ の単調性（Buchholz 補題 1.2(d)）

Lean ファイルのこの節見出しの下に宣言はない。

---

## $\psi_v(\alpha)$ の加法主性（Buchholz 補題 1.2(b)）

Lean ファイルのこの節見出しの下に宣言はない。
下の [(D.addprinc)](#d-addprinc) は加法主性を述語として切り出したものであるが、
$\psi_v(\alpha)$ がそれをみたすという主張は現在の Lean ファイルには存在しない。

---

## 濃度評価（Buchholz 補題 1.2(c)）：$\psi_v(\alpha) < \Omega_{v+1}$

Lean ファイルのこの節見出しの下に宣言はない。この節のコメントは、
「`|C_v(α)| ≤ Ω_v ⊔ ω < Ω_{v+1}`（$C_v(\alpha)$ は
$\mathrm{Iio}(\Omega_v)$ から $+$ と可算個の写像 $\psi_u$ で生成されるから）」という論法と、
濃度計算を `Cardinal.{1}` で行う（`Set Ordinal.{0}` が `Type 1` に属するため）という移植上の
方針を述べているが、対応する宣言は存在しない。
[(D.psi)](#d-psi) の補足 4 で述べた通り、この評価は $\psi_v(\alpha)$ の読みに必要な非空性の
出所である。

---

## 加法主性の抽象化

<a id="d-addprinc"></a>
### 定義 加法主性 (D.addprinc)

$\delta\in\mathrm{Ord}$ に対し

$$\mathrm{addprinc}(\delta) :\iff
0<\delta \ \wedge\ \forall \beta\,\gamma,\ \beta<\delta \to \gamma<\delta \to \beta+\gamma<\delta .$$

Lean では

```lean
def addprinc (δ : Ordinal) : Prop :=
  0 < δ ∧ ∀ β γ, β < δ → γ < δ → β + γ < δ
```

である。第 2 連言子は Mathlib の `Ordinal.IsPrincipal (· + ·) δ`
（$\forall \beta\,\gamma,\ \beta<\delta\to\gamma<\delta\to\beta+\gamma<\delta$）と同じ主張であり、
$\mathrm{addprinc}$ はそれに $0<\delta$ を加えたものである（Mathlib の `IsPrincipal` は $\delta=0$ を
除外しない規約を採っている）。

順序数の加法は可換ではないが、この条件は $\beta$ と $\gamma$ の両方を全称量化しているから、
$\beta+\gamma<\delta$ と $\gamma+\beta<\delta$ の双方を含意する。

この述語は [(T.oV_lt_of_allprinc)](Otembed.md#t-oV_lt_of_allprinc) の仮定として使われる。
そこでは、項 $t \in \mathrm{Three}$（[(D.Three)](Mechanized.md#d-Three)。構成子は $\mathsf{Z}$ と
$\mathsf{P}(a,b,c)$）の主要項の値がすべて $\delta$ 未満ならば $oV\,t<\delta$ であることが、
$\mathrm{addprinc}(\delta)$ の第 1 連言子（$t=\mathsf{Z}$ の場合、$oV\,\mathsf{Z}=0<\delta$）と
第 2 連言子（$t=\mathsf{P}(a,b,c)$ の場合、$oV\,t = \psi_a(oV\,b)+oV\,c$ の 2 項がともに $\delta$ 未満）
から従う形で使われる。

---

## 条件付き崩壊関数 $\psi^w_v$（Buchholz の忠実な §1）

Lean ファイルのこの節見出しの下に宣言はない。この節のコメントは、
Buchholz 1986 が $C_v(\alpha)$ の生成規則に付ける正準性の側条件 $\xi\in C_u(\xi)$ を
（上の [(D.Cstep)](#d-Cstep) では落としているのに対し）復活させた版 $\psi^w$ を、
`CstepW` = 生成規則を $\{\xi\mid \xi\in \mathrm{Cset}\ p\ \xi\ u\}$ で絞った `Cstep`、として
既存の展開と並行に追加する設計を述べている。対応する宣言（`CstepW`, `psiW` など）は
現在の Lean ファイルには存在しない。

---

## $\psi^w$ に対する §1 の移植（Buchholz 1.2–1.4(a)）

Lean ファイルのこの節見出しの下に宣言はない。

---

## $\psi^w$ の加法主性と引数抽出

Lean ファイルのこの節見出しの下に宣言はない。

---

## 自己参照的な条件付き $C$ 集合 $C^s_v(\alpha)$

Lean ファイルのこの節見出しの下に宣言はない。この節のコメントは、
正準性の判定を定義中の同じ $C$ 自身で行う版（$\xi\in \mathrm{CsetSelf}\ p\ \xi\ u$）を、
判定が上限 $\alpha$ に依存しないことを利用して上限に関する整礎再帰で定義する設計を述べている。
対応する宣言（`CsetSelf`, `psiSelf` など）は現在の Lean ファイルには存在しない。

---

## 上限・パラメータ単調性

Lean ファイルのこの節見出しの下に宣言はない。

---

## $\psi^s$ の定義可能性

Lean ファイルのこの節見出しの下に宣言はない。

---

## $\psi^s$ に対する §1 の移植（Buchholz 1.2–1.4）

Lean ファイルのこの節見出しの下に宣言はない。

---

## $\psi^s$ の加法主性と無条件の引数抽出

Lean ファイルのこの節見出しの下に宣言はない。

---

## 本章の位置づけ

本章で定義された記号のうち、後続の章が実際に参照するのは
[(D.psi)](#d-psi) と [(D.addprinc)](#d-addprinc) の 2 つであり、いずれも
[`Otembed.md`](Otembed.md) の評価写像 [(D.oV)](Otembed.md#d-oV)
（$oV\,\mathsf{Z}=0$、$oV\,\mathsf{P}(a,b,c) = \psi_a(oV\,b) + oV\,c$）とその周辺で使われる。
[(D.Om)](#d-Om)、[(D.Cstep)](#d-Cstep)、[(D.Citer)](#d-Citer)、[(D.Cset)](#d-Cset)、
[(D.Psi)](#d-Psi) は他の章から参照されない。
停止性の最終結論 [(T.PSS_terminates_unconditional)](Final.md#t-PSS_terminates_unconditional) に至る
経路は順序数を用いず、したがって本章の内容には依存しない。
