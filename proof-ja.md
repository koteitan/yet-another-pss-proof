[README](README-ja.md)

# ペア数列システムの停止性（`p_a(b)+c` アプローチ）

P進大好きbot 氏のペア数列システム (Pair Sequence System, PSS) の停止性を、
ペア数列を独自のオーダー記法 `p_a(b)+c` へ変換 (`translate`) し、
その記法上の整礎な順序 `≺` に関して**展開の各ステップで測度が真に減少する**こと
を示して証明する。これは原始数列システム (PrSS) の停止証明
（[`prss-proof`](https://github.com/koteitan/prss-proof)）の戦略
——数列をカントール標準形に写し、`expand` の各ステップで順序数が真に減少する——
をペア数列へ一般化したものである。Buchholz の ψ への変換とは異なる記法を用いる。

PSS の証明論的強さは **ψ₀(ψ_ω(0))**（Buchholz ordinal, Ω_ω の崩壊）と
考えられており、記法 `p_a(b)` の添字 `a` を自然数（0,1,2,… とその上限 ω）に
取ることに対応する。

> **記法の凡例**: 「Isabelle ✓」は形式証明済み（`def.thy` / `mechanized.thy` /
> `proofs.thy`、`isbman build -d . -v YAPSS` で検証）。「経験的」は `yaBMS` による
> 数値的確認のみ。「未了」は今後の課題。

---

## 1. ペア数列システム（§5 の定式化）

**ペア数列** $M$ は空でない $(\mathbb N\times\mathbb N)$ 値の有限列
$M=(M_0,\dots,M_{X-1})$、$X=\mathrm{Lng}\,M$。第 $j$ 対の第 $i$ 成分を
$M_{i,j}=\mathrm{entry}\,M\,i\,j$ と書く（行 $i\in\{0,1\}$）。

**親子関係（§5.1, `nextrel0`/`le0`/`nextrel1`/`le1`）。** 行 0 は
「直前のより小さい行0値」で親を定める：

$$ (0,j_0)\stackrel{\mathrm{Next}}{<}_M(0,j_1) \iff j_0<j_1\ \wedge\ M_{0,j_0}<M_{0,j_1}\ \wedge\ \forall j\,(j_0<j<j_1\Rightarrow M_{0,j}\ge M_{0,j_1}). $$

$\le_M$（行 0）はその反射推移閉包。行 1 (`nextrel1`) は行 0 の祖先関係 $\le_M$
の上で同様に定める。

**基本列（§5.3, `oper`, $M[n]$）。** $j_1=\mathrm{Lng}\,M-1$ とする。

- $j_1=0$ なら $M[n]=M$;
- $M_{j_1}=(0,0)$ なら $M[n]=\mathrm{Pred}\,M$（末尾を落とす）;
- 行 $i_1=\mathrm{idx1}\,M\,j_1$（$M_{1,j_1}>0$ なら 1、さもなくば 0）で
  $j_1$ に一意の親 $j_0$ が無ければ $M[n]=\mathrm{Pred}\,M$;
- さもなくば、良部 $G=(M_0,\dots,M_{j_0-1})$ と悪部 $B=(M_{j_0},\dots,M_{j_1-1})$ により

$$ M[n]=G \oplus \bigoplus_{k=0}^{n-1}\bigl((M_{0,j}+k\,\delta_0,\ M_{1,j}+k\,\delta_1)\bigr)_{j=j_0}^{j_1-1}, $$

ここで $\delta_0=M_{0,j_1}-M_{0,j_0}$（$i_1=1$ のときのみ非零）、$\delta_1=0$
（$i_1\le1$ ゆえ常に 0）。すなわち悪部を $n$ 個コピーし、$i_1=1$ のとき
各コピーの**行 0 を $k\delta_0$ ずつ上昇**させ、末尾対は落とす。
PrSS の「悪部コピー」に**行 0 の上昇**が加わったものである。

**標準形（§6.7, `ST_PS`）。** 対角列
$\mathrm{diagSeq}\,u\,v=((u,u),(u{+}1,u{+}1),\dots,(v,v))$（$u\le v$）を基点に、
$M\mapsto M[n]$（$n\ge1$）で閉じた最小集合。**本証明は `ST_PS` を対象とする。**

**停止性。** 1ステップ関係 `step`（$\mathrm{Lng}\,M>1$ で $M\to M[n]$、$n\ge1$）に
無限前進列が無いこと。

> §5・§6.7 の上記定義はすべて [`def.thy`](def.thy) に形式化（Isabelle ✓）。

---

## 2. オーダー記法 `p_a(b)+c`（`mechanized.thy`）

**定義 2.1（項, `ord`）。** 二分木ならぬ三項木

$$ \mathsf{ord} ::= Z \ \mid\ P\ a\ b\ c\qquad (a\in\mathbb N,\ b,c\in\mathsf{ord}) $$

$Z=0$、$P\,a\,b\,c = p_a(b)+c$ と読む。主要項 $p_a(b)$ は添字 $a$（自然数）と引数
$b$ をもち、$c$ は和の残り（同レベルの兄弟）。これは PrSS の
$E\,a\,b=\omega^{a}+b$ の一般化（単一指数 $\omega^a$ を $p_a(b)$ に置換）である。

**定義 2.2（添字優先順序, `olt` / $\prec$）。** 主要項を**添字優先**で辞書式比較する：

$$ Z\prec P\,a\,b\,c,\qquad
P\,a\,b\,c \prec P\,e\,f\,g \iff a<e \ \vee\ (a=e\wedge b\prec f)\ \vee\ (a=e\wedge b=f\wedge c\prec g). $$

すなわち $(a,b,c)$ の 3 次元辞書式順序（$a$ は自然数の $<$、$b,c$ は再帰的に $\prec$）。

> $\prec$ は線形順序（**`olt_irrefl`, `olt_trans`, `olt_total`** すべて Isabelle ✓）。

**順序の向きについて（重要）。** 主要項の lex には「添字優先」と「引数優先」の
2 通りがあるが、**展開で減少するのは添字優先のみ**である（§4）。これは Buchholz の
「添字が大きいほど大きい」と同じ向きで、ペア数列が Buchholz の ψ と微妙にずれる
本質に対応する。

---

## 3. 変換 `translate`（`mechanized.thy`）

**定義 3.1（`translate`）。** ペア数列を左から行 0（第1成分）で森として読む。
先頭対 $(x,y)$ は主要項 $p_y(\cdot)$ になり、その引数は「直後の行0値 $>x$ の
最長ブロック」（子孫の森）の変換、和の残りは残り接尾辞（兄弟）の変換：

$$ \mathrm{translate}([])=Z,\qquad
\mathrm{translate}((x,y)\mathbin{::}\mathit{rest}) = P\ y\ \bigl(\mathrm{translate}\,\mathit{tw}\bigr)\ \bigl(\mathrm{translate}\,\mathit{dw}\bigr), $$
$$ \mathit{tw}=\mathrm{takeWhile}\,(\lambda q.\ x<\mathrm{fst}\,q)\,\mathit{rest},\quad
\mathit{dw}=\mathrm{dropWhile}\,(\lambda q.\ x<\mathrm{fst}\,q)\,\mathit{rest}. $$

添字は行 1 の値 $y$。これは PrSS の森オーダー写像 `omap` の $\omega^{\bullet}$ を
$p_y(\bullet)$ に置換したものである。

**例（task の対応, すべて Isabelle ✓ `by simp`）。**

| ペア数列 | `translate` |
|---|---|
| $(0,0)$ | $p_0(0)$ |
| $(0,0)(1,0)$ | $p_0(p_0(0))$ |
| $(0,0)(1,1)$ | $p_0(p_1(0))$ |
| $(0,0)(1,0)(1,0)$ | $p_0(p_0(0)+p_0(0))$ |
| $(0,0)(1,1)(2,2)(3,3)$ | $p_0(p_1(p_2(p_3(0)))) $ |

---

## 4. 展開での減少（経験的）

`yaBMS` で生成した標準列 $M\in\mathrm{ST_{PS}}$ とその展開 $M[n]$（$n=1,2,3$）に
ついて、$\mathrm{translate}(M[n])\prec\mathrm{translate}(M)$ を全数チェックした：

| 順序 | 減少 | 等 | **増大** |
|---|---|---|---|
| **添字優先** | 4002 | 0 | **0** |
| 引数優先 | 3762 | 0 | **240** |

**添字優先では全ステップで真に減少**する（経験的）。具体例：
$M=(0,0)(1,1)\to M[2]=(0,0)(1,0)(2,0)$ で

$$ \mathrm{translate}(M)=p_0(p_1(0)),\qquad \mathrm{translate}(M[2])=p_0(p_0(p_0(0))). $$

両者 $p_0(\cdot)$ なので引数 $p_1(0)$ vs $p_0(p_0(0))$ の比較に帰着し、添字
$1>0$ より $p_0(p_0(0))\prec p_1(0)$、よって減少。引数優先だと逆に増大する。

> **減少補題（未了, `m_step_decreases`）。** $M\in\mathrm{ST_{PS}}$, $\mathrm{Lng}\,M>1$,
> $n\ge1 \Rightarrow \mathrm{translate}(M[n])\prec\mathrm{translate}(M)$。
> PrSS の `omap_core`/`omap_BADCTX` を、添字付き・行0上昇コピーの場合へ拡張する。

---

## 5. 整礎性——本質的難所

PrSS では CNF 項上で $\prec$ が整礎で、`omap` が常に CNF を出力するため停止性が
従った。本記法でも同じ枠組みを目指すが、**添字優先の純 lex は一般には整礎でない**：

$$ x_n := \underbrace{p_0(p_0(\cdots p_0}_{n}(p_1(0))\cdots))\quad\Longrightarrow\quad x_0\succ x_1\succ x_2\succ\cdots $$

は無限下降列（$p_0(p_1(0))\prec p_1(0)$ を内側にネストし続けられる、Isabelle ✓ で
個別に確認可能）。したがって、**`translate` の像を含む構文的正規形 NF を定め、
その NF 上で $\prec$ の整礎性を示す**必要がある（PrSS の CNF に相当）。

**NF の定義（構文的特徴づけは不要）。** 標準形の構文的特徴づけを求める必要は
ない。**NF を「対角列 $(0,0)(1,1)\cdots(n,n)$ から `expand` で到達可能な列の
`translate` 像」と定義**すればよい。これは本稿の標準形 $\mathrm{ST_{PS}}$
（[`def.thy`](def.thy) の `ST_PS`、対角列 + $M[n]$ 閉包）の `translate` 像
$\mathrm{NF}:=\mathrm{translate}(\mathrm{ST_{PS}})$ に他ならない。無限下降の証人
$x_n$（$n\ge2$）に対応するペア数列 $(0,0)(1,0)(2,1),\dots$ はこの到達可能集合に
**入らない**（`yaBMS` で確認）ので、$\prec$ は $\mathrm{NF}$ 上では整礎な可能性が高い。

**整礎性の道筋——最大添字 $n$ の帰納。** 鍵となる不変量：

> **補題（添字単調性, 未了）。** $M[n]$ は悪部のコピー（行 1 値は保存、行 0 のみ
> 上昇）＋末尾削除なので、**列中の行 1 値の最大（= `translate` の添字の最大）は
> 展開で非増加**。ゆえに対角列 $(0,0)\cdots(n,n)$ から到達可能な列の `translate` は
> **添字 $\le n$** に収まる。

これにより $\mathrm{NF}$ は最大添字 $n$ で階層化され、**$n$ に関する帰納**で
$\prec$ の整礎性を示せる（各レベルが下位レベルの整礎順序上の CNF となる、
崩壊関数の整礎性の素直な形）。$n=0$ は単項 $p_0$ のみで PrSS の CNF（$\omega^b+c$）
と同型ゆえ PrSS の整礎性証明に帰着する。

**現状認識（重要）。** PSS の強さ ψ₀(ψ_ω(0)) ゆえ、$\mathrm{NF}$ 上の整礎性は
本質的に Buchholz の ψ の整礎性（崩壊関数の整礎性）と同等の内容をもつ。
**`p_a(b)+c` 化は減少の側を綺麗にする**（§4, 経験的に全ステップ減少）一方、
整礎性の難所は残る。ただし上記の $n$ 帰納＋ PrSS 帰着により、Buchholz ψ を直接
扱うより見通しよく形式化できる見込みである。これが本アプローチの設計方針である。

---

## 6. 停止性の組み立て（未了）

減少（§4）と NF 上の整礎性（§5）が揃えば、PrSS と同様に

$$ \{(T,M)\mid \mathrm{step}\,M\,T\}\ \subseteq\ \mathrm{translate}^{-1}(\prec) $$

の右辺が整礎（整礎関係の逆像）ゆえ `step` は整礎、すなわち無限展開列は存在しない。

---

## 7. Isabelle 形式化との対応（現状）

| 対象 | Isabelle | 状態 |
|---|---|---|
| §5 定義, $M[n]$, `ST_PS`, `step` | [`def.thy`](def.thy) | ✓ |
| 記法 $\mathsf{ord}$（$Z$, $P\,a\,b\,c$） | `datatype ord` | ✓ |
| 添字優先順序 $\prec$ | `olt` (`<o`) | ✓ |
| 線形性 | `olt_irrefl`/`olt_trans`/`olt_total` | ✓ |
| $\mathrm{translate}$ | `translate` | ✓ |
| task の例 | 各 sanity 補題 | ✓ |
| 正規形 NF | — | 未了 |
| NF 上の整礎性 | — | 未了 |
| 減少補題 `m_step_decreases` | — | 未了 |
| 停止性定理 | — | 未了 |

---

出典：Koteitan「[Purely mathematical definition of BMS](https://googology.fandom.com/wiki/User_blog:Koteitan/Purely_mathematical_definition_of_BMS)」巨大数研究 Wiki；
P進大好きbot「ペア数列の停止性」巨大数研究 Wiki。
