[← README](README-ja.md) | [English](Term.md) | [Japanese](Term-ja.md)

<a id="d-Three"></a>
## 定義: 三分岐記法 (D.Three)

集合 $`\mathrm{Three}`$ を、次の 2 つの構成子で生成される最小の集合として定める。

```math
\begin{aligned}
&\mathsf{Z} \in \mathrm{Three}, \cr
&a \in \mathbb{N},\ b \in \mathrm{Three},\ c \in \mathrm{Three}
   \ \Longrightarrow\ \mathsf{P}(a,b,c) \in \mathrm{Three}.
\end{aligned}
```

構成子は単射であり、像は互いに交わらない。すなわち $`\mathsf{Z} \ne \mathsf{P}(a,b,c)`$ であり、
$`\mathsf{P}(a,b,c) = \mathsf{P}(a',b',c')`$ ならば $`a = a'`$、$`b = b'`$、$`c = c'`$ である。

最小性は次の帰納法の原理として使う。$`\mathrm{Three}`$ 上の述語 $`\Phi`$ が
$`\Phi(\mathsf{Z})`$ をみたし、かつ任意の $`a, b, c`$ について
$`\Phi(b) \wedge \Phi(c) \to \Phi(\mathsf{P}(a,b,c))`$ をみたすならば、
$`\forall t \in \mathrm{Three},\ \Phi(t)`$ が成り立つ。
以下ではこれを「項の構造に関する帰納法」と呼ぶ。

$`\mathsf{P}(a,b,c)`$ は $`p_a(b) + c`$ と読む。$`a`$ を**添字**、$`b`$ を**引数**、$`c`$ を**後続和**と呼ぶ。

<a id="d-olt"></a>
## 定義: 添字優先辞書式順序 (D.olt)

関係 $`\prec\ \subseteq \mathrm{Three} \times \mathrm{Three}`$ を、両引数の構成子による場合分けで定める。

```math
\begin{aligned}
\mathsf{Z} &\prec \mathsf{Z} &&:\iff \bot, \cr
\mathsf{Z} &\prec \mathsf{P}(a,b,c) &&:\iff \top, \cr
\mathsf{P}(a,b,c) &\prec \mathsf{Z} &&:\iff \bot, \cr
\mathsf{P}(a,b,c) &\prec \mathsf{P}(e,f,g) &&:\iff
  a \lt e \ \vee\ (a = e \wedge b \prec f) \ \vee\ (a = e \wedge b = f \wedge c \prec g).
\end{aligned}
```

第 4 式の右辺の再帰呼び出しは $`b \prec f`$ と $`c \prec g`$ であり、いずれも引数が
$`\mathsf{P}(a,b,c)`$, $`\mathsf{P}(e,f,g)`$ の真部分項であるから、この定義は整合的である。

すなわち $`\prec`$ は、主要項を「添字、引数、後続和」の順に比べる辞書式順序である。

<a id="d-ole"></a>
## 定義: 広義順序 (D.ole)

```math
x \preceq y :\iff x \prec y \ \vee\ x = y .
```

<a id="t-olt_Z_Z"></a>
## 定理: $`\mathsf{Z}`$ どうしは比較不能 (T.olt_Z_Z)

### 定理

$`\neg(\mathsf{Z} \prec \mathsf{Z})`$。

### 証明

$`\prec`$ の定義（D.olt）の第 1 式により $`\mathsf{Z} \prec \mathsf{Z}`$ は $`\bot`$ と定義により同一の命題である。
よってその仮定から $`\bot`$ が得られる。∎

<a id="t-olt_Z_P"></a>
## 定理: $`\mathsf{Z}`$ は主要項より小さい (T.olt_Z_P)

### 定理

任意の $`a \in \mathbb{N}`$, $`b, c \in \mathrm{Three}`$ に対し $`\mathsf{Z} \prec \mathsf{P}(a,b,c)`$。

### 証明

$`\prec`$ の定義（D.olt）の第 2 式により $`\mathsf{Z} \prec \mathsf{P}(a,b,c)`$ は $`\top`$ と定義により
同一の命題であり、$`\top`$ は成り立つ。∎

<a id="t-olt_P_Z"></a>
## 定理: 主要項は $`\mathsf{Z}`$ より小さくない (T.olt_P_Z)

### 定理

任意の $`a \in \mathbb{N}`$, $`b, c \in \mathrm{Three}`$ に対し $`\neg\bigl(\mathsf{P}(a,b,c) \prec \mathsf{Z}\bigr)`$。

### 証明

$`\prec`$ の定義（D.olt）の第 3 式により $`\mathsf{P}(a,b,c) \prec \mathsf{Z}`$ は $`\bot`$ と定義により
同一の命題である。∎

<a id="t-olt_P_P"></a>
## 定理: 主要項どうしの比較 (T.olt_P_P)

### 定理

任意の $`a, e \in \mathbb{N}`$, $`b, c, f, g \in \mathrm{Three}`$ に対し

```math
\mathsf{P}(a,b,c) \prec \mathsf{P}(e,f,g) \iff
  a \lt e \ \vee\ (a = e \wedge b \prec f) \ \vee\ (a = e \wedge b = f \wedge c \prec g).
```

### 証明

$`\prec`$ の定義（D.olt）の第 4 式そのものであり、両辺は定義により同一の命題である。∎

<a id="d-lead"></a>
## 定義: 先頭添字 (D.lead)

```math
\mathrm{lead}\,\mathsf{Z} := 0, \qquad \mathrm{lead}\,\mathsf{P}(a,b,c) := a .
```

<a id="t-lead_Z"></a>
## 定理: $`\mathsf{Z}`$ の先頭添字 (T.lead_Z)

### 定理

$`\mathrm{lead}\,\mathsf{Z} = 0`$。

### 証明

$`\mathrm{lead}`$ の定義（D.lead）の第 1 式そのものである。∎

<a id="t-lead_P"></a>
## 定理: 主要項の先頭添字 (T.lead_P)

### 定理

任意の $`a \in \mathbb{N}`$, $`b, c \in \mathrm{Three}`$ に対し $`\mathrm{lead}\,\mathsf{P}(a,b,c) = a`$。

### 証明

$`\mathrm{lead}`$ の定義（D.lead）の第 2 式そのものである。∎

<a id="t-olt_P_of_lead_lt"></a>
## 定理: 先頭添字による支配 (T.olt_P_of_lead_lt)

### 定理

$`t \in \mathrm{Three}`$、$`w \in \mathbb{N}`$、$`b, c \in \mathrm{Three}`$ とする。
$`t = \mathsf{Z}`$ または $`\mathrm{lead}\,t \lt w`$ ならば $`t \prec \mathsf{P}(w,b,c)`$。

### 証明

$`t`$ の構成子で場合分けする。

- $`t = \mathsf{Z}`$ のとき。[T.olt_Z_P](#t-olt_Z_P) より $`\mathsf{Z} \prec \mathsf{P}(w,b,c)`$。

- $`t = \mathsf{P}(a,b',c')`$ のとき。仮定の第 1 選言 $`t = \mathsf{Z}`$ は、構成子の像が
  交わらないことから偽である。よって第 2 選言が成り立ち、[T.lead_P](#t-lead_P) より
  $`\mathrm{lead}\,t = a`$ であるから $`a \lt w`$。
  [T.olt_P_P](#t-olt_P_P) の右辺の第 1 選言がこれであるから
  $`\mathsf{P}(a,b',c') \prec \mathsf{P}(w,b,c)`$。∎

<a id="t-olt_irrefl"></a>
## 定理: 非反射性 (T.olt_irrefl)

### 定理

任意の $`x \in \mathrm{Three}`$ に対し $`\neg(x \prec x)`$。

### 証明

$`x`$ の構造に関する帰納法。帰納法の述語は

```math
\Phi(x) :\equiv \neg(x \prec x).
```

- **基底段** $`x = \mathsf{Z}`$：[T.olt_Z_Z](#t-olt_Z_Z) が $`\Phi(\mathsf{Z})`$ そのものである。

- **帰納段** $`x = \mathsf{P}(a,b,c)`$：$`\Phi(b)`$ と $`\Phi(c)`$、すなわち
  $`\neg(b \prec b)`$ と $`\neg(c \prec c)`$ を仮定する。
  $`\mathsf{P}(a,b,c) \prec \mathsf{P}(a,b,c)`$ を仮定すると、[T.olt_P_P](#t-olt_P_P) より
  次の 3 つのいずれかが成り立つ。
  - $`a \lt a`$：$`\mathbb{N}`$ の $`\lt`$ の非反射性に矛盾。
  - $`a = a \wedge b \prec b`$：帰納法の仮定 $`\Phi(b)`$ に矛盾。
  - $`a = a \wedge b = b \wedge c \prec c`$：帰納法の仮定 $`\Phi(c)`$ に矛盾。

  いずれも矛盾であるから $`\Phi(\mathsf{P}(a,b,c))`$。∎

<a id="t-not_olt_Z"></a>
## 定理: $`\mathsf{Z}`$ は最小 (T.not_olt_Z)

### 定理

任意の $`x \in \mathrm{Three}`$ に対し $`\neg(x \prec \mathsf{Z})`$。

### 証明

$`x`$ の構成子で場合分けする。$`x = \mathsf{Z}`$ のときは [T.olt_Z_Z](#t-olt_Z_Z)、
$`x = \mathsf{P}(a,b,c)`$ のときは [T.olt_P_Z](#t-olt_P_Z) である。∎

<a id="t-olt_trans"></a>
## 定理: 推移律 (T.olt_trans)

### 定理

$`x \prec y`$ かつ $`y \prec z`$ ならば $`x \prec z`$。

### 証明

$`z`$ の構造に関する帰納法を行う（$`x`$, $`y`$ は全称量化したまま動かす）。帰納法の述語は

```math
\Phi(z) :\equiv \forall x, y \in \mathrm{Three},\ (x \prec y \wedge y \prec z) \to x \prec z .
```

- **基底段** $`z = \mathsf{Z}`$：仮定 $`y \prec \mathsf{Z}`$ は [T.not_olt_Z](#t-not_olt_Z) に反する。
  よって前件が偽であり $`\Phi(\mathsf{Z})`$ が成り立つ。

- **帰納段** $`z = \mathsf{P}(c_1,c_2,c_3)`$：$`\Phi(c_2)`$ と $`\Phi(c_3)`$ を仮定する。
  $`x, y`$ を取り $`x \prec y`$、$`y \prec \mathsf{P}(c_1,c_2,c_3)`$ とする。

  $`x = \mathsf{Z}`$ のときは [T.olt_Z_P](#t-olt_Z_P) より結論が成り立つ。
  以下 $`x = \mathsf{P}(a_1,a_2,a_3)`$ とする。$`y = \mathsf{Z}`$ とすると $`x \prec \mathsf{Z}`$ が
  [T.not_olt_Z](#t-not_olt_Z) に反するから、$`y = \mathsf{P}(e_1,e_2,e_3)`$ と書ける。

  [T.olt_P_P](#t-olt_P_P) により $`x \prec y`$ は次のいずれかである。

  - (1) $`a_1 \lt e_1`$
  - (2) $`a_1 = e_1 \wedge a_2 \prec e_2`$
  - (3) $`a_1 = e_1 \wedge a_2 = e_2 \wedge a_3 \prec e_3`$

  同じく $`y \prec z`$ は次のいずれかである。

  - (I) $`e_1 \lt c_1`$
  - (II) $`e_1 = c_1 \wedge e_2 \prec c_2`$
  - (III) $`e_1 = c_1 \wedge e_2 = c_2 \wedge e_3 \prec c_3`$

  9 通りすべてについて、[T.olt_P_P](#t-olt_P_P) の右辺のどの選言が成り立つかを示す。

  | | (I) | (II) | (III) |
  |---|---|---|---|
  | **(1)** | $`a_1 \lt c_1`$ | $`a_1 \lt c_1`$ | $`a_1 \lt c_1`$ |
  | **(2)** | $`a_1 \lt c_1`$ | $`a_1 = c_1 \wedge a_2 \prec c_2`$ | $`a_1 = c_1 \wedge a_2 \prec c_2`$ |
  | **(3)** | $`a_1 \lt c_1`$ | $`a_1 = c_1 \wedge a_2 \prec c_2`$ | $`a_1 = c_1 \wedge a_2 = c_2 \wedge a_3 \prec c_3`$ |

  各欄の根拠は次の通りである。

  - **(1)(I)**：$`a_1 \lt e_1`$ と $`e_1 \lt c_1`$ から $`\mathbb{N}`$ の $`\lt`$ の推移律で $`a_1 \lt c_1`$。
  - **(1)(II)**, **(1)(III)**：$`e_1 = c_1`$ を $`a_1 \lt e_1`$ に代入して $`a_1 \lt c_1`$。
  - **(2)(I)**, **(3)(I)**：$`a_1 = e_1`$ を $`e_1 \lt c_1`$ に代入して $`a_1 \lt c_1`$。
  - **(2)(II)**：$`a_1 = e_1 = c_1`$ であり、$`a_2 \prec e_2`$ と $`e_2 \prec c_2`$ に
    帰納法の仮定 $`\Phi(c_2)`$ を適用して $`a_2 \prec c_2`$。
  - **(2)(III)**：$`a_1 = e_1 = c_1`$、$`e_2 = c_2`$ であるから、$`a_2 \prec e_2 = c_2`$。
  - **(3)(II)**：$`a_1 = e_1 = c_1`$、$`a_2 = e_2`$ であるから、$`a_2 = e_2 \prec c_2`$。
  - **(3)(III)**：$`a_1 = e_1 = c_1`$、$`a_2 = e_2 = c_2`$ であり、$`a_3 \prec e_3`$ と
    $`e_3 \prec c_3`$ に帰納法の仮定 $`\Phi(c_3)`$ を適用して $`a_3 \prec c_3`$。

  いずれの場合も $`x \prec z`$ が得られたので $`\Phi(\mathsf{P}(c_1,c_2,c_3))`$。∎

<a id="t-olt_ole_trans"></a>
## 定理: 狭義と広義の合成 (T.olt_ole_trans)

### 定理

$`x \prec y`$ かつ $`y \preceq z`$ ならば $`x \prec z`$。

### 証明

$`\preceq`$ の定義（D.ole）より $`y \preceq z`$ は $`y \prec z`$ か $`y = z`$ である。
前者のときは [T.olt_trans](#t-olt_trans) を $`x \prec y`$ と $`y \prec z`$ に適用する。
後者のときは $`z`$ を $`y`$ に書き換えれば仮定 $`x \prec y`$ そのものである。∎

<a id="t-olt_P_b"></a>
## 定理: 引数についての狭義単調性 (T.olt_P_b)

### 定理

$`b_1 \prec b_2`$ ならば、任意の $`a \in \mathbb{N}`$, $`c_1, c_2 \in \mathrm{Three}`$ に対し
$`\mathsf{P}(a,b_1,c_1) \prec \mathsf{P}(a,b_2,c_2)`$。

### 証明

[T.olt_P_P](#t-olt_P_P) の右辺の第 2 選言 $`a = a \wedge b_1 \prec b_2`$ が、
$`=`$ の反射性と仮定により成り立つ。∎

<a id="t-olt_P_c"></a>
## 定理: 後続和についての狭義単調性 (T.olt_P_c)

### 定理

$`c_1 \prec c_2`$ ならば、任意の $`a \in \mathbb{N}`$, $`b \in \mathrm{Three}`$ に対し
$`\mathsf{P}(a,b,c_1) \prec \mathsf{P}(a,b,c_2)`$。

### 証明

[T.olt_P_P](#t-olt_P_P) の右辺の第 3 選言 $`a = a \wedge b = b \wedge c_1 \prec c_2`$ が、
$`=`$ の反射性と仮定により成り立つ。∎

<a id="d-translate"></a>
## 定義: 翻訳 (D.translate)

以下、型 $`\alpha`$ の要素上の述語 $`p`$ と $`\alpha`$ の有限列 $`L`$ に対し

```math
\mathrm{tw}_p L := \text{（}L\text{ の先頭から、}p\text{ をみたす要素が続く極大な前部分列）},
```
```math
\mathrm{dw}_p L := \text{（}L\text{ から } \mathrm{tw}_p L \text{ を取り除いた残りの列）}
```

と書く。定義から $`\mathrm{tw}_p L \mathbin{+\!\!+} \mathrm{dw}_p L = L`$ であり、
$`\mathrm{dw}_p L`$ が空でなければその先頭要素 $`x`$ は $`\neg p(x)`$ をみたす。

$`a \in \mathbb{N}`$ と $`L \in \mathrm{PairSeq}`$（[D.PairSeq](Pss-ja.md#d-PairSeq)）に対しては、
述語を $`p(x) :\equiv a \lt x_1`$ と取ったものを $`\mathrm{tw}_a L`$、$`\mathrm{dw}_a L`$ と書く。
すなわち $`\mathrm{tw}_a L`$ は $`L`$ の先頭から第 1 成分が $`a`$ より大きい要素が続く極大な
前部分列であり、$`\mathrm{dw}_a L`$ が空でなければその先頭要素 $`x`$ は $`\neg(a \lt x_1)`$ を
みたす。下付きが述語なら一般の版、自然数ならこの版である。

写像 $`\mathrm{tr} : \mathrm{PairSeq} \to \mathrm{Three}`$ を、列の長さに関する再帰で定める。

```math
\mathrm{tr}\,() := \mathsf{Z}, \qquad
\mathrm{tr}\,(p :: L) := \mathsf{P}\bigl(p_2,\ \mathrm{tr}(\mathrm{tw}_{p_1} L),\ \mathrm{tr}(\mathrm{dw}_{p_1} L)\bigr) .
```

ここで $`p = (p_1, p_2)`$、$`p :: L`$ は先頭に $`p`$ を付けた列である。
再帰呼び出しの引数は $`\mathrm{tw}_{p_1} L`$ と $`\mathrm{dw}_{p_1} L`$ であり、
どちらも $`L`$ の部分列だから長さは $`\lvert L\rvert`$ 以下、すなわち $`\lvert p :: L\rvert`$ より
真に小さい。よってこの定義は整合的である。

読み方は次の通りである。列を行 $`0`$（第 1 成分）によって森とみなす。先頭の対 $`(x,y)`$ は
主要項 $`p_y(\cdot)`$ になり、その引数は「行 $`0`$ の値が $`x`$ より大きい対が続く極大な区間」
（$`(x,y)`$ の子孫たち）の翻訳、後続和は残りの部分（$`(x,y)`$ の兄弟たち）の翻訳である。
添字には行 $`1`$ の値 $`y`$ が入る。

この再帰に沿う帰納法、すなわち述語 $`\Psi`$ について

```math
\Psi(()) \quad\text{かつ}\quad
\forall p, L,\ \bigl(\Psi(\mathrm{tw}_{p_1} L) \wedge \Psi(\mathrm{dw}_{p_1} L)\bigr) \to \Psi(p :: L)
```

から $`\forall M,\ \Psi(M)`$ を得る形の帰納法を、以下「$`\mathrm{tr}`$ の再帰に沿う帰納法」と呼ぶ。

<a id="t-lead_translate"></a>
## 定理: 翻訳の先頭添字 (T.lead_translate)

### 定理

```math
\mathrm{lead}\,(\mathrm{tr}\,M) = \begin{cases}
0 & (M = ()) \cr
p_2 & (M = p :: L)
\end{cases}
```

### 証明

$`M`$ の構成子で場合分けする。

- $`M = ()`$：$`\mathrm{tr}`$ の定義（D.translate）より $`\mathrm{tr}\,() = \mathsf{Z}`$ であり、
  [T.lead_Z](#t-lead_Z) より $`\mathrm{lead}\,\mathsf{Z} = 0`$。

- $`M = p :: L`$：$`\mathrm{tr}`$ の定義（D.translate）より
  $`\mathrm{tr}(p :: L) = \mathsf{P}(p_2, \cdot, \cdot)`$ であり、
  [T.lead_P](#t-lead_P) よりその先頭添字は $`p_2`$。∎

<a id="t-takeWhile_append_all"></a>
## 定理: 全要素が条件をみたす前置列の take (T.takeWhile_append_all)

### 定理

$`p`$ を要素上の述語、$`xs, ys`$ を列とする。$`xs`$ のすべての要素が $`p`$ をみたすならば

```math
\mathrm{tw}_p(xs \mathbin{+\!\!+} ys) = xs \mathbin{+\!\!+} \mathrm{tw}_p\,ys .
```


### 証明

$`\mathrm{tw}_p`$ は先頭から $`p`$ をみたす限り取る操作であるから、連結列
$`xs \mathbin{+\!\!+} ys`$ に対しては、$`xs`$ のどこかで $`p`$ が破れればそこで止まり、
破れなければ $`xs`$ を全部取ってから $`ys`$ を続けて調べる。すなわち

```math
\mathrm{tw}_p(xs \mathbin{+\!\!+} ys) = \begin{cases}
xs \mathbin{+\!\!+} \mathrm{tw}_p\,ys & (\mathrm{tw}_p\,xs = xs) \cr
\mathrm{tw}_p\,xs & (\text{それ以外})
\end{cases}
```

である。仮定よりすべての要素が $`p`$ をみたすから $`\mathrm{tw}_p\,xs = xs`$ であり、
第 1 の場合になる。∎

<a id="t-dropWhile_append_all"></a>
## 定理: 全要素が条件をみたす前置列の drop (T.dropWhile_append_all)

### 定理

$`xs`$ のすべての要素が $`p`$ をみたすならば
$`\mathrm{dw}_p(xs \mathbin{+\!\!+} ys) = \mathrm{dw}_p\,ys`$。

### 証明

[T.takeWhile_append_all](#t-takeWhile_append_all) の証明と同じ場合分けにより

```math
\mathrm{dw}_p(xs \mathbin{+\!\!+} ys) = \begin{cases}
\mathrm{dw}_p\,ys & (\mathrm{dw}_p\,xs = ()) \cr
\mathrm{dw}_p\,xs \mathbin{+\!\!+} ys & (\text{それ以外})
\end{cases}
```

である。仮定よりすべての要素が $`p`$ をみたすから $`\mathrm{dw}_p\,xs = ()`$ であり、
第 1 の場合になる。∎

<a id="t-takeWhile_append_not"></a>
## 定理: 条件を破る要素を含む前置列の take (T.takeWhile_append_not)

### 定理

$`x \in xs`$ かつ $`\neg p(x)`$ ならば
$`\mathrm{tw}_p(xs \mathbin{+\!\!+} ys) = \mathrm{tw}_p\,xs`$。

### 証明

[T.takeWhile_append_all](#t-takeWhile_append_all) の証明で挙げた場合分けの第 2 の場合に
なることを示せばよい。すなわち $`\mathrm{tw}_p\,xs \ne xs`$ を示す。
$`\mathrm{tw}_p\,xs = xs`$ と仮定すると、$`\mathrm{tw}_p\,xs`$ の要素はすべて $`p`$ をみたすから
$`xs`$ の要素もすべて $`p`$ をみたし、とくに $`p(x)`$ となって仮定 $`\neg p(x)`$ に矛盾する。∎

<a id="t-dropWhile_append_not"></a>
## 定理: 条件を破る要素を含む前置列の drop (T.dropWhile_append_not)

### 定理

$`x \in xs`$ かつ $`\neg p(x)`$ ならば
$`\mathrm{dw}_p(xs \mathbin{+\!\!+} ys) = \mathrm{dw}_p\,xs \mathbin{+\!\!+} ys`$。

### 証明

[T.dropWhile_append_all](#t-dropWhile_append_all) の証明で挙げた場合分けの第 2 の場合に
なることを示せばよい。すなわち $`\mathrm{dw}_p\,xs \ne ()`$ を示す。
$`\mathrm{dw}_p\,xs = ()`$ と仮定すると、$`xs`$ の要素はすべて $`p`$ をみたすことになり、
とくに $`p(x)`$ となって仮定 $`\neg p(x)`$ に矛盾する。∎

<a id="t-drop_eq_map_getD"></a>
## 定理: 後部分列の添字表示 (T.drop_eq_map_getD)

### 定理

列 $`xs`$、$`a \in \mathbb{N}`$、既定値 $`d`$ に対し

```math
\mathrm{drop}_a\,xs = \bigl(\,xs\langle a\rangle,\ xs\langle a+1\rangle,\ \dots,\ xs\langle \lvert xs\rvert - 1\rangle\,\bigr)
```

である。ここで $`\mathrm{drop}_a\,xs`$ は先頭 $`a`$ 要素を落とした列、
$`xs\langle i\rangle`$ は $`i \lt \lvert xs\rvert`$ なら第 $`i`$ 要素、そうでなければ $`d`$ である。
右辺の長さは $`\lvert xs\rvert - a`$（切り捨て減法）である。

### 証明

両辺の長さと各成分が一致することを示す。

**長さ**：左辺の長さは $`\lvert xs\rvert - a`$ である。右辺は添字 $`a, a+1, \dots`$ を
$`\lvert xs\rvert - a`$ 個並べたものだから、長さは $`\lvert xs\rvert - a`$ である。

**成分**：$`i \lt \lvert xs\rvert - a`$ とする。左辺の第 $`i`$ 成分は $`xs`$ の第 $`a + i`$ 要素である。
右辺の第 $`i`$ 成分は $`xs\langle a + i\rangle`$ であり、$`i \lt \lvert xs\rvert - a`$ より
$`a + i \lt \lvert xs\rvert`$ であるから、これは $`xs`$ の第 $`a+i`$ 要素に等しい。∎

<a id="t-nextrel0_entry0_less"></a>
## 定理: 行 0 の親子では行 0 が真に増える (T.nextrel0_entry0_less)

### 定理

$`j_0 \to^M_0 j_1`$（[D.nextrel0](Pss-ja.md#d-nextrel0)）ならば
$`M_{0,j_0} \lt M_{0,j_1}`$（[D.entry](Pss-ja.md#d-entry)）。

### 証明

$`\to^M_0`$ の定義（D.nextrel0）の第 4 条件そのものである。∎

<a id="t-le0_entry0_mono"></a>
## 定理: 行 0 の祖先では行 0 が広義に増える (T.le0_entry0_mono)

### 定理

$`j_0 \le^M_0 j_1`$（[D.le0](Pss-ja.md#d-le0)）ならば $`M_{0,j_0} \le M_{0,j_1}`$。

### 証明

$`\le^M_0`$ の定義（D.le0）の第 3 条件により $`j_0 \mathbin{(\to^M_0)^{*}} j_1`$ である。
この反射推移閉包の構成に関する帰納法を行う。帰納法の述語は

```math
\Phi(j) :\equiv M_{0,j_0} \le M_{0,j} .
```

- **基底段**（$`j = j_0`$、鎖の長さ $`0`$）：$`M_{0,j_0} \le M_{0,j_0}`$ は $`\le`$ の反射性による。

- **帰納段**（$`j_0 \mathbin{(\to^M_0)^{*}} y`$ と $`y \to^M_0 z`$ から $`j_0 \mathbin{(\to^M_0)^{*}} z`$）：
  $`\Phi(y)`$、すなわち $`M_{0,j_0} \le M_{0,y}`$ を仮定する。
  [T.nextrel0_entry0_less](#t-nextrel0_entry0_less) より $`M_{0,y} \lt M_{0,z}`$ であるから、
  $`\le`$ の推移律により $`M_{0,j_0} \le M_{0,z}`$。よって $`\Phi(z)`$。∎

<a id="t-nextrel0_index_less"></a>
## 定理: 行 0 の親子では添字が増える (T.nextrel0_index_less)

### 定理

$`a \to^M_0 b`$ ならば $`a \lt b`$。

### 証明

$`\to^M_0`$ の定義（D.nextrel0）の第 3 条件そのものである。∎

<a id="t-nextrel0_rtrancl_index_le"></a>
## 定理: 行 0 の祖先では添字が広義に増える (T.nextrel0_rtrancl_index_le)

### 定理

$`a \mathbin{(\to^M_0)^{*}} b`$ ならば $`a \le b`$。

### 証明

反射推移閉包の構成に関する帰納法。帰納法の述語は $`\Phi(j) :\equiv a \le j`$。

- **基底段**（$`j = a`$）：$`\le`$ の反射性による。
- **帰納段**（$`a \mathbin{(\to^M_0)^{*}} y`$ と $`y \to^M_0 z`$）：帰納法の仮定 $`\Phi(y)`$ は
  $`a \le y`$ である。[T.nextrel0_index_less](#t-nextrel0_index_less) より $`y \lt z`$ であるから
  $`a \le z`$。∎

<a id="t-le0_interval_gt"></a>
## 定理: 祖先の区間はすべて行 0 が上 (T.le0_interval_gt)

### 定理

$`j_0 \mathbin{(\to^M_0)^{*}} j_1`$ とする。このとき

```math
\forall k,\ \bigl(j_0 \lt k \wedge k \le j_1\bigr) \to M_{0,j_0} \lt M_{0,k} .
```

すなわち区間 $`(j_0, j_1]`$ の**すべての**添字（鎖の点だけでなく、その間の谷も含めて）で
行 $`0`$ の値は $`M_{0,j_0}`$ より真に大きい。

### 証明

反射推移閉包の構成に関する帰納法。帰納法の述語は

```math
\Phi(j) :\equiv \forall k,\ \bigl(j_0 \lt k \wedge k \le j\bigr) \to M_{0,j_0} \lt M_{0,k} .
```

- **基底段**（$`j = j_0`$）：前件は $`j_0 \lt k \wedge k \le j_0`$ であり、これをみたす $`k`$ は
  存在しない。よって $`\Phi(j_0)`$ が成り立つ。

- **帰納段**（$`j_0 \mathbin{(\to^M_0)^{*}} y`$ と $`y \to^M_0 z`$）：$`\Phi(y)`$ を仮定する。
  次の 3 つを用意する。

  1. $`M_{0,y} \lt M_{0,z}`$。[T.nextrel0_entry0_less](#t-nextrel0_entry0_less) による。
  2. $`j_0 \le y`$。[T.nextrel0_rtrancl_index_le](#t-nextrel0_rtrancl_index_le) による。
  3. $`M_{0,j_0} \le M_{0,y}`$。2 より $`j_0 \lt y`$ か $`j_0 = y`$ である。前者のときは
     帰納法の仮定 $`\Phi(y)`$ を $`k := y`$ に適用して $`M_{0,j_0} \lt M_{0,y}`$ を得る。
     後者のときは両辺が同一である。

  さて $`k`$ を取り $`j_0 \lt k`$、$`k \le z`$ とする。$`y`$ と $`k`$ の大小で場合分けする。

  - $`k \le y`$ のとき。帰納法の仮定 $`\Phi(y)`$ を $`k`$ に適用すればよい。

  - $`y \lt k`$ のとき。さらに $`k`$ と $`z`$ で場合分けする。
    - $`k = z`$ のとき。3 と 1 から $`M_{0,j_0} \le M_{0,y} \lt M_{0,z} = M_{0,k}`$。
    - $`k \lt z`$ のとき。$`y \to^M_0 z`$ すなわち $`\to^M_0`$ の定義（D.nextrel0）の第 5 条件を
      $`j := k`$ に適用すると、$`y \lt k \wedge k \lt z`$ より $`M_{0,z} \le M_{0,k}`$ を得る。
      これと 3、1 を合わせて $`M_{0,j_0} \le M_{0,y} \lt M_{0,z} \le M_{0,k}`$。

  いずれの場合も $`M_{0,j_0} \lt M_{0,k}`$ が得られたので $`\Phi(z)`$。∎

<a id="t-translate_single_tree"></a>
## 定理: 単一の木の翻訳 (T.translate_single_tree)

### 定理

$`p \in \mathbb{N}\times\mathbb{N}`$、$`R \in \mathrm{PairSeq}`$ とする。
$`R`$ のすべての要素 $`x`$ が $`p_1 \lt x_1`$ をみたすならば

```math
\mathrm{tr}(p :: R) = \mathsf{P}\bigl(p_2,\ \mathrm{tr}\,R,\ \mathsf{Z}\bigr).
```

### 証明

仮定より $`R`$ のすべての要素が述語 $`x \mapsto p_1 \lt x_1`$ をみたすから、
$`\mathrm{tw}_{p_1} R = R`$ かつ $`\mathrm{dw}_{p_1} R = ()`$ である。
これを $`\mathrm{tr}`$ の定義（D.translate）の第 2 式に代入して

```math
\mathrm{tr}(p :: R) = \mathsf{P}\bigl(p_2,\ \mathrm{tr}\,R,\ \mathrm{tr}\,()\bigr)
```

を得る。さらに $`\mathrm{tr}`$ の定義（D.translate）の第 1 式より $`\mathrm{tr}\,() = \mathsf{Z}`$。∎

<a id="t-translate_block_append"></a>
## 定理: ブロックと後続の翻訳 (T.translate_block_append)

### 定理

$`v_0, w_0 \in \mathbb{N}`$、$`R, T \in \mathrm{PairSeq}`$ とする。
$`R`$ のすべての要素 $`x`$ が $`v_0 \lt x_1`$ をみたし、かつ
$`T = ()`$ または $`\neg\bigl(v_0 \lt (\mathrm{head}\,T)_1\bigr)`$ ならば

```math
\mathrm{tr}\bigl(((v_0,w_0) :: R) \mathbin{+\!\!+} T\bigr)
  = \mathsf{P}\bigl(w_0,\ \mathrm{tr}\,R,\ \mathrm{tr}\,T\bigr).
```

### 証明

$`((v_0,w_0) :: R) \mathbin{+\!\!+} T = (v_0,w_0) :: (R \mathbin{+\!\!+} T)`$ であるから、
$`\mathrm{tr}`$ の定義（D.translate）の第 2 式より示すべきことは

```math
\mathrm{tw}_{v_0}(R \mathbin{+\!\!+} T) = R
\qquad\text{かつ}\qquad
\mathrm{dw}_{v_0}(R \mathbin{+\!\!+} T) = T
```

である。$`T`$ について場合分けする。

- $`T = ()`$ のとき。$`R \mathbin{+\!\!+} () = R`$ であり、仮定より $`R`$ の全要素が
  $`v_0 \lt x_1`$ をみたすから $`\mathrm{tw}_{v_0} R = R`$、$`\mathrm{dw}_{v_0} R = () = T`$。

**$`T = t :: ts`$ のとき。**仮定の第 2 選言より $`\neg(v_0 \lt t_1)`$ である。
$`R`$ の全要素が条件をみたすので [T.takeWhile_append_all](#t-takeWhile_append_all) が使えて

```math
\mathrm{tw}_{v_0}(R \mathbin{+\!\!+} T) = R \mathbin{+\!\!+} \mathrm{tw}_{v_0} T .
```

$`T`$ の先頭 $`t`$ が条件を破るから $`\mathrm{tw}_{v_0} T = ()`$ であり、右辺は $`R`$ である。
同様に [T.dropWhile_append_all](#t-dropWhile_append_all) より
$`\mathrm{dw}_{v_0}(R \mathbin{+\!\!+} T) = \mathrm{dw}_{v_0} T`$ であり、$`t`$ が条件を破るから
$`\mathrm{dw}_{v_0} T = T`$ である。∎

<a id="t-translate_shift"></a>
## 定理: 行 0 の一様な平行移動は翻訳を変えない (T.translate_shift)

### 定理

$`d \in \mathbb{N}`$、$`M \in \mathrm{PairSeq}`$ とする。$`M`$ の各対の第 1 成分に
一様に $`d`$ を足した列を $`M^{+d}`$ と書くと

```math
\mathrm{tr}\,(M^{+d}) = \mathrm{tr}\,M .
```

### 証明

$`\mathrm{tr}`$ の再帰に沿う帰納法。帰納法の述語は

```math
\Psi(M) :\equiv \mathrm{tr}\,(M^{+d}) = \mathrm{tr}\,M .
```

- **基底段** $`M = ()`$：$`()^{+d} = ()`$ であり、両辺とも $`\mathsf{Z}`$ である。

**帰納段** $`M = p :: L`$：$`\Psi(\mathrm{tw}_{p_1} L)`$ と
$`\Psi(\mathrm{dw}_{p_1} L)`$ を仮定する。

まず述語が平行移動で不変であることを見る。任意の対 $`r`$ について

```math
p_1 + d \lt r_1 + d \iff p_1 \lt r_1
```

である（$`\mathbb{N}`$ の加法の狭義単調性）。したがって $`L^{+d}`$ の要素
$`r^{+d}`$ を述語 $`x \mapsto (p_1 + d) \lt x_1`$ で判定することは、$`L`$ の要素 $`r`$ を
述語 $`x \mapsto p_1 \lt x_1`$ で判定することと同値である。$`\mathrm{tw}`$, $`\mathrm{dw}`$ は
先頭から順に述語を判定するだけであるから

```math
\mathrm{tw}_{p_1 + d}(L^{+d}) = (\mathrm{tw}_{p_1} L)^{+d},
\qquad
\mathrm{dw}_{p_1 + d}(L^{+d}) = (\mathrm{dw}_{p_1} L)^{+d} .
```

$`(p :: L)^{+d} = (p_1 + d, p_2) :: L^{+d}`$ であるから、$`\mathrm{tr}`$ の定義（D.translate）より

```math
\mathrm{tr}\bigl((p :: L)^{+d}\bigr)
  = \mathsf{P}\bigl(p_2,\ \mathrm{tr}((\mathrm{tw}_{p_1} L)^{+d}),\ \mathrm{tr}((\mathrm{dw}_{p_1} L)^{+d})\bigr).
```

ここに 2 つの帰納法の仮定を適用すると右辺は
$`\mathsf{P}(p_2, \mathrm{tr}(\mathrm{tw}_{p_1} L), \mathrm{tr}(\mathrm{dw}_{p_1} L))`$ となり、
これは $`\mathrm{tr}`$ の定義（D.translate）より $`\mathrm{tr}(p :: L)`$ に等しい。
第 2 成分 $`p_2`$ は平行移動で変わらないことに注意する。よって $`\Psi(p :: L)`$。∎

<a id="t-translate_ctx_cong"></a>
## 定理: 文脈による合同 (T.translate_ctx_cong)

### 定理

$`z_1, z_2 \in \mathbb{N}\times\mathbb{N}`$、$`T_1, T_2, G \in \mathrm{PairSeq}`$ とし、
次の 4 つを仮定する。

```math
\begin{aligned}
&\text{(base)}\quad \mathrm{tr}(z_1 :: T_1) \prec \mathrm{tr}(z_2 :: T_2), \cr
&\text{(root)}\quad (z_1)_1 = (z_2)_1, \cr
&\text{(r1)}\quad \forall x \in T_1,\ (z_1)_1 \le x_1, \cr
&\text{(r2)}\quad \forall x \in T_2,\ (z_2)_1 \le x_1 .
\end{aligned}
```

このとき

```math
\mathrm{tr}(G \mathbin{+\!\!+} z_1 :: T_1) \prec \mathrm{tr}(G \mathbin{+\!\!+} z_2 :: T_2).
```

### 証明

$`\lvert G\rvert`$ に関する強帰納法。帰納法の述語は

```math
\Phi(G) :\equiv \mathrm{tr}(G \mathbin{+\!\!+} z_1 :: T_1) \prec \mathrm{tr}(G \mathbin{+\!\!+} z_2 :: T_2)
```

である。

「$`\lvert G'\rvert \lt \lvert G\rvert`$ なるすべての $`G'`$ について $`\Phi(G')`$」を仮定する。

- **$`G = ()`$ のとき**：両辺は仮定 (base) そのものである。

**$`G = g :: G'`$ のとき。** $`G'`$ の全要素が $`g_1 \lt x_1`$ をみたすかどうかで場合分けする。

**(a) $`G'`$ のある要素 $`x`$ が $`\neg(g_1 \lt x_1)`$ をみたすとき。**
[T.takeWhile_append_not](#t-takeWhile_append_not) と
[T.dropWhile_append_not](#t-dropWhile_append_not) を $`xs := G'`$、$`ys := z_i :: T_i`$ に
適用すると、$`i = 1, 2`$ のいずれでも

```math
\mathrm{tw}_{g_1}(G' \mathbin{+\!\!+} z_i :: T_i) = \mathrm{tw}_{g_1} G',
\qquad
\mathrm{dw}_{g_1}(G' \mathbin{+\!\!+} z_i :: T_i) = \mathrm{dw}_{g_1} G' \mathbin{+\!\!+} z_i :: T_i
```

である。よって $`\mathrm{tr}`$ の定義（D.translate）より

```math
\mathrm{tr}\bigl(g :: (G' \mathbin{+\!\!+} z_i :: T_i)\bigr)
  = \mathsf{P}\bigl(g_2,\ \mathrm{tr}(\mathrm{tw}_{g_1} G'),\
      \mathrm{tr}(\mathrm{dw}_{g_1} G' \mathbin{+\!\!+} z_i :: T_i)\bigr)
```

であり、$`i = 1, 2`$ で添字と引数が共通である。
$`\mathrm{dw}_{g_1} G'`$ は $`G'`$ の部分列だから
$`\lvert \mathrm{dw}_{g_1} G'\rvert \le \lvert G'\rvert \lt \lvert g :: G'\rvert`$ であり、
帰納法の仮定を $`G' := \mathrm{dw}_{g_1} G'`$ に適用して

```math
\mathrm{tr}(\mathrm{dw}_{g_1} G' \mathbin{+\!\!+} z_1 :: T_1)
  \prec \mathrm{tr}(\mathrm{dw}_{g_1} G' \mathbin{+\!\!+} z_2 :: T_2)
```

を得る。これに [T.olt_P_c](#t-olt_P_c) を適用すれば結論が従う。

**(b) $`G'`$ の全要素が $`g_1 \lt x_1`$ をみたし、かつ $`g_1 \lt (z_1)_1`$ のとき。**
(root) より $`g_1 \lt (z_2)_1`$ でもある。(r1) と合わせると、$`T_1`$ の任意の要素 $`x`$ に
ついて $`g_1 \lt (z_1)_1 \le x_1`$ であるから、$`z_1 :: T_1`$ の全要素が $`g_1 \lt x_1`$ を
みたす。$`z_2 :: T_2`$ についても (r2) から同様である。したがって
$`G' \mathbin{+\!\!+} z_i :: T_i`$ の全要素が $`g_1 \lt x_1`$ をみたし、
[T.translate_single_tree](#t-translate_single_tree) より

```math
\mathrm{tr}\bigl(g :: (G' \mathbin{+\!\!+} z_i :: T_i)\bigr)
  = \mathsf{P}\bigl(g_2,\ \mathrm{tr}(G' \mathbin{+\!\!+} z_i :: T_i),\ \mathsf{Z}\bigr)
```

である。$`\lvert G'\rvert \lt \lvert g :: G'\rvert`$ であるから帰納法の仮定を $`G'`$ に適用して

```math
\mathrm{tr}(G' \mathbin{+\!\!+} z_1 :: T_1) \prec \mathrm{tr}(G' \mathbin{+\!\!+} z_2 :: T_2)
```

を得る。これに [T.olt_P_b](#t-olt_P_b) を適用すれば結論が従う。

**(c) $`G'`$ の全要素が $`g_1 \lt x_1`$ をみたし、かつ $`\neg\bigl(g_1 \lt (z_1)_1\bigr)`$ のとき。**
(root) より $`\neg\bigl(g_1 \lt (z_2)_1\bigr)`$ でもある。
[T.takeWhile_append_all](#t-takeWhile_append_all) と
[T.dropWhile_append_all](#t-dropWhile_append_all) より、$`i = 1, 2`$ のいずれでも

```math
\mathrm{tw}_{g_1}(G' \mathbin{+\!\!+} z_i :: T_i) = G' \mathbin{+\!\!+} \mathrm{tw}_{g_1}(z_i :: T_i),
\qquad
\mathrm{dw}_{g_1}(G' \mathbin{+\!\!+} z_i :: T_i) = \mathrm{dw}_{g_1}(z_i :: T_i)
```

であり、$`z_i :: T_i`$ の先頭 $`z_i`$ が述語を破るから
$`\mathrm{tw}_{g_1}(z_i :: T_i) = ()`$、$`\mathrm{dw}_{g_1}(z_i :: T_i) = z_i :: T_i`$ である。
よって

```math
\mathrm{tr}\bigl(g :: (G' \mathbin{+\!\!+} z_i :: T_i)\bigr)
  = \mathsf{P}\bigl(g_2,\ \mathrm{tr}\,G',\ \mathrm{tr}(z_i :: T_i)\bigr)
```

であり、$`i = 1, 2`$ で添字と引数が共通である。仮定 (base) に
[T.olt_P_c](#t-olt_P_c) を適用すれば結論が従う。∎

<a id="d-sndSet"></a>
## 定義: 行 1 の値の集合 (D.sndSet)

$`M \in \mathrm{PairSeq}`$ に対し

```math
\mathrm{snd}(M) := \{\, y \in \mathbb{N} \mid \exists p \in M,\ p_2 = y \,\} .
```

<a id="t-mem_sndSet"></a>
## 定理: 行 1 の値の集合の要素判定 (T.mem_sndSet)

### 定理

$`y \in \mathrm{snd}(M) \iff \exists p \in M,\ p_2 = y`$。

### 証明

$`\mathrm{snd}`$ の定義（D.sndSet）そのものである。∎

<a id="t-sndSet_nil"></a>
## 定理: 空列の行 1 の値の集合 (T.sndSet_nil)

### 定理

$`\mathrm{snd}(()) = \emptyset`$。

### 証明

$`y \in \mathrm{snd}(())`$ とすると、[T.mem_sndSet](#t-mem_sndSet) より $`p \in ()`$ なる
$`p`$ が存在することになるが、空列は要素をもたない。よって $`\mathrm{snd}(())`$ は
要素をもたず、$`\emptyset`$ に等しい。∎

<a id="t-idx1_le1"></a>
## 定理: 探索行は 1 以下 (T.idx1_le1)

### 定理

任意の $`M \in \mathrm{PairSeq}`$, $`j \in \mathbb{N}`$ に対し
$`\mathrm{idx}_1(M,j) \le 1`$（[D.idx1](Pss-ja.md#d-idx1)）。

### 証明

$`\mathrm{idx}_1`$ の定義（D.idx1）の場合分けにより $`\mathrm{idx}_1(M,j)`$ の値は $`1`$ か $`0`$ であり、
どちらも $`1`$ 以下である。∎
