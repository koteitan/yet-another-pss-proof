[← 目次](README.md)

# AscArg — 共終性の核 $\mathrm{ArgDomCore}$ と、その導出帰納による証明

[`Cofinality.md`](Cofinality.md) は PSS の Bachmann 共終性を、**2 つ**の標準形（宿主 $M$ と側 $N$）に言及する残余
$\mathrm{AscArgDom}$ にまで還元した。本章はまずこれを、**単一の標準形**についての言明 $\mathrm{ArgDomCore}$
（[(D.ArgDomCore)](#d-ArgDomCore)）に還元し、次にその $\mathrm{ArgDomCore}$ を
[(D.ST_PS)](Def.md#d-ST_PS) の**導出に関する帰納法**で証明する。
導出帰納の `oper`-`bad` 枝は、境界 $p = \lvert G\rvert + \lvert \mathit{blk}\rvert$ に対する 2 つの列位置の
場合分け（A1 / B / A2）で尽くされる。
結論は [(T.argDomCore_holds)](#t-argDomCore_holds)（核そのもの）と
[(T.pss_cofinality_of_core)](#t-pss_cofinality_of_core)（そこから得られる共終性）である。

## 記法

この章で新たに導入する Lean 名と数学記法の対応。

| Lean | 本文 | 意味 |
|---|---|---|
| `SpineOK A L w` | $\mathrm{SpineOK}(A,L,w)$ | 側条件（[(D.SpineOK)](#d-SpineOK)） |
| `ArgDomCore` | $\mathrm{ArgDomCore}$ | 宿主を含まない核（[(D.ArgDomCore)](#d-ArgDomCore)） |
| `ArgDomCoreOn N` | $\mathrm{ArgDomCoreOn}(N)$ | 核の列ごとの形（[(D.ArgDomCoreOn)](#d-ArgDomCoreOn)） |
| `shiftl0 d X` | $\mathrm{sh}^{-}_d X$ | 行 0 の値を $d$ だけ切り捨て減算（[(D.shiftl0)](#d-shiftl0)） |

既出のモジュールで定義された記号は次のように書く。初出箇所を定義へのリンクとする。

| Lean | 本文 | 意味 |
|---|---|---|
| `X.length` | $\lvert X\rvert$ | 列の長さ |
| `p.1`, `p.2` | $\pi_0 p$, $\pi_1 p$ | 対 $p$ の第 0・第 1 成分 |
| `X ++ Y` | $X \mathbin{+\!\!+} Y$ | 連結 |
| `x :: X` | $x \mathbin{::} X$ | 先頭付加 |
| `X.headI` | $\mathrm{headI}\,X$ | 先頭要素（空列なら $(0,0)$） |
| `X <+: Y` | $X \sqsubseteq Y$ | $\exists T,\ Y = X \mathbin{+\!\!+} T$（前部分列） |
| `X.take k`, `X.drop k` | $\mathrm{take}\,k\,X$, $\mathrm{drop}\,k\,X$ | 前 $k$ 個、前 $k$ 個を除いた残り |
| `M.getD j (0,0)` | $M\langle j\rangle$ | 第 $j$ 対（範囲外なら $(0,0)$、[(D.PairSeq)](Def.md#d-PairSeq)） |
| `entry M i j` | $M_{i,j}$ | 第 $j$ 対の第 $i$ 成分（[(D.entry)](Def.md#d-entry)） |
| `M⟦n⟧` | $M[n]$ | 展開（[(D.oper)](Def.md#d-oper)） |
| `ST_PS M` | $M \in \mathrm{ST\_PS}$ | 標準形（[(D.ST_PS)](Def.md#d-ST_PS)） |
| `diagSeq 0 v` | $\Delta_0^v$ | 対角列（[(D.diagSeq)](Def.md#d-diagSeq)） |
| `le0 M i j` | $i \le^M_0 j$ | 行 0 の祖先関係（[(D.le0)](Def.md#d-le0)） |
| `nextrel1 M i j` | $i \to^M_1 j$ | 行 1 の直接親子関係（[(D.nextrel1)](Def.md#d-nextrel1)） |
| `hasParent M i j` | $\mathrm{hasParent}(M,i,j)$ | 親の一意存在（[(D.hasParent)](Def.md#d-hasParent)） |
| `idx1 M j` | $\mathrm{idx}_1(M,j)$ | 親を探す行番号（[(D.idx1)](Def.md#d-idx1)） |
| `Pred M` | $\mathrm{Pred}\,M$ | 末尾 1 個を除いた列（[(D.Pred)](Def.md#d-Pred)） |
| `translate M` | $\mathrm{tr}\,M$ | 翻訳（[(D.translate)](Mechanized.md#d-translate)） |
| `x <o y`, `x ≤o y` | $x \prec y$, $x \preceq y$ | 添字優先辞書式順序（[(D.olt)](Mechanized.md#d-olt), [(D.ole)](Mechanized.md#d-ole)） |
| `pairlt p q` | $p \prec_{\mathrm{c}} q$ | 列 1 個の比較（[(D.pairlt)](Seqlex.md#d-pairlt)） |
| `seqlex X Y` | $X \prec_{\mathrm{lex}} Y$ | 列辞書式順序（[(D.seqlex)](Seqlex.md#d-seqlex)） |
| `sle X Y` | $X \preceq_{\mathrm{lex}} Y$ | $X = Y \vee X \prec_{\mathrm{lex}} Y$（[(D.sle)](Cofinality.md#d-sle)） |
| `shiftr0 d X` | $\mathrm{sh}_d X$ | 行 0 の値を $d$ だけ増やす（[(D.shiftr0)](Wf.md#d-shiftr0)） |
| `copies d blk n` | $\mathrm{cp}_d(\mathit{blk},n)$ | $n$ 個のコピー塔（[(D.copies)](Wf.md#d-copies)） |
| `AscArgDom` | $\mathrm{AscArgDom}$ | 昇順コピーの残余（[(D.AscArgDom)](Cofinality.md#d-AscArgDom)） |
| `L.takeWhile p`, `L.dropWhile p` | $\mathrm{tw}_a L$, $\mathrm{dw}_a L$ | 述語 $\lambda q.\ a < \pi_0 q$ による前部・後部 |

$\prec_{\mathrm{c}}$、$\prec_{\mathrm{lex}}$、$\preceq_{\mathrm{lex}}$、$\mathrm{sh}_d$、$\mathrm{cp}_d$ の定義を、
本章で繰り返し使うので再掲する（いずれも他ファイルの定義であり、ここでは参照の便宜のためだけに書く）。

$$p \prec_{\mathrm{c}} q \iff \pi_0 p < \pi_0 q \ \vee\ (\pi_0 p = \pi_0 q \wedge \pi_1 p < \pi_1 q)$$

$$X \prec_{\mathrm{lex}} Y \iff
\begin{cases}
Y \ne [] & (X = [])\\
\bot & (X \ne [],\ Y = [])\\
x \prec_{\mathrm{c}} y \ \vee\ (x = y \wedge X' \prec_{\mathrm{lex}} Y') & (X = x \mathbin{::} X',\ Y = y \mathbin{::} Y')
\end{cases}$$

$$\mathrm{sh}_d X := \mathrm{map}\,(\lambda p.\ (\pi_0 p + d,\ \pi_1 p))\,X,
\qquad
\mathrm{cp}_d(\mathit{blk},n) := \mathrm{sh}_{0\cdot d}\,\mathit{blk} \mathbin{+\!\!+} \mathrm{sh}_{1\cdot d}\,\mathit{blk} \mathbin{+\!\!+} \cdots \mathbin{+\!\!+} \mathrm{sh}_{(n-1)\cdot d}\,\mathit{blk}$$

本章で用いる標準ライブラリの事実を挙げる。

- `List.append_inj`：$l_1 \mathbin{+\!\!+} r_1 = l_2 \mathbin{+\!\!+} r_2$ かつ $\lvert l_1\rvert = \lvert l_2\rvert$ ならば $l_1 = l_2$ かつ $r_1 = r_2$
- `List.append_cancel_left`：$P \mathbin{+\!\!+} X = P \mathbin{+\!\!+} Y \to X = Y$
- `List.take_append_drop`：$\mathrm{take}\,k\,L \mathbin{+\!\!+} \mathrm{drop}\,k\,L = L$
- `List.map_injective_iff`：$f$ が単射ならば $\mathrm{map}\,f$ も単射
- `List.map_append`：$\mathrm{map}\,f\,(X \mathbin{+\!\!+} Y) = \mathrm{map}\,f\,X \mathbin{+\!\!+} \mathrm{map}\,f\,Y$
- `List.takeWhile_append_dropWhile`：$L.\mathrm{takeWhile}\,p \mathbin{+\!\!+} L.\mathrm{dropWhile}\,p = L$
- `List.mem_takeWhile_imp`：$x \in L.\mathrm{takeWhile}\,p \to p\,x$
- `List.head?_dropWhile_not`：$L.\mathrm{dropWhile}\,p$ が空でなければ、その先頭は $p$ をみたさない
- `List.takeWhile_prefix`：$L.\mathrm{takeWhile}\,p \sqsubseteq L$
- `List.prefix_append`：$X \sqsubseteq X \mathbin{+\!\!+} Y$
- `List.prefix_of_prefix_length_le`：$l_1 \sqsubseteq l_3$、$l_2 \sqsubseteq l_3$、$\lvert l_1\rvert \le \lvert l_2\rvert$ ならば $l_1 \sqsubseteq l_2$
- `List.IsPrefix.length_le`：$X \sqsubseteq Y \to \lvert X\rvert \le \lvert Y\rvert$
- `List.eq_nil_of_length_eq_zero`：$\lvert L\rvert = 0 \to L = []$

自然数の減法はすべて切り捨て減法である（$a < b$ のとき $a - b = 0$）。

---

## Part A — リスト代数

$\mathrm{ArgDomCore}$ の 1 つの実例をコピー塔全体へ展開するために使う、$\preceq_{\mathrm{lex}}$ と
$\prec_{\mathrm{lex}}$ についての事実を集める。

<a id="t-seqlex_of_sle_not_prefix"></a>
### 定理 前部で決着する比較 (T.seqlex_of_sle_not_prefix)

**主張** $W, X, Y \in \mathrm{PairSeq}$ とする。
$$X \preceq_{\mathrm{lex}} W \mathbin{+\!\!+} Y \quad\wedge\quad \bigl(\forall X',\ X \ne W \mathbin{+\!\!+} X'\bigr)
\ \Longrightarrow\ \forall Y',\ X \prec_{\mathrm{lex}} W \mathbin{+\!\!+} Y' .$$

すなわち、$W$ が $X$ の前部分列**でない**ならば、比較はすでに $W$ の内部で決着しており、
$W$ の後ろに何を継ぎ足しても $X$ は真に小さい。

**証明** $W$ に関するリストの構造帰納法。帰納法の述語は
$$\Phi(W) :\equiv \forall X, Y,\ \bigl(X \preceq_{\mathrm{lex}} W \mathbin{+\!\!+} Y\bigr) \to
 \bigl(\forall X',\ X \ne W \mathbin{+\!\!+} X'\bigr) \to \forall Y',\ X \prec_{\mathrm{lex}} W \mathbin{+\!\!+} Y'$$
である（$X$ と $Y$ は帰納法の中で動かす）。

- 基底段 $W = []$：第 2 の仮定を $X' := X$ に適用すると $X \ne [] \mathbin{+\!\!+} X = X$ となり矛盾する。
  よって前提が偽であり $\Phi([])$ が成り立つ。
- 帰納段 $W = w \mathbin{::} W'$：帰納法の仮定は $\Phi(W')$ である。
  $X$、$Y$、$h : X \preceq_{\mathrm{lex}} (w \mathbin{::} W') \mathbin{+\!\!+} Y$、
  $h_{np} : \forall X',\ X \ne (w \mathbin{::} W') \mathbin{+\!\!+} X'$、$Y'$ を与える。$X$ で場合分けする。
  - $X = []$：$(w \mathbin{::} W') \mathbin{+\!\!+} Y' = w \mathbin{::} (W' \mathbin{+\!\!+} Y') \ne []$ であるから、
    $\prec_{\mathrm{lex}}$ の第 1 の場合により $[] \prec_{\mathrm{lex}} (w \mathbin{::} W') \mathbin{+\!\!+} Y'$。
  - $X = x \mathbin{::} X''$：$h$ は $x \mathbin{::} X'' \preceq_{\mathrm{lex}} w \mathbin{::} (W' \mathbin{+\!\!+} Y)$ である。
    $\preceq_{\mathrm{lex}}$ の 2 つの選言で場合分けする。
    - 等号 $x \mathbin{::} X'' = w \mathbin{::} (W' \mathbin{+\!\!+} Y)$ のとき：これは
      $X = (w \mathbin{::} W') \mathbin{+\!\!+} Y$ であり、$h_{np}$ を $X' := Y$ に適用したものに矛盾する。
    - $x \mathbin{::} X'' \prec_{\mathrm{lex}} w \mathbin{::} (W' \mathbin{+\!\!+} Y)$ のとき：$\prec_{\mathrm{lex}}$ の第 3 の場合により
      $x \prec_{\mathrm{c}} w$ または（$x = w$ かつ $X'' \prec_{\mathrm{lex}} W' \mathbin{+\!\!+} Y$）である。
      - $x \prec_{\mathrm{c}} w$：目標 $x \mathbin{::} X'' \prec_{\mathrm{lex}} w \mathbin{::} (W' \mathbin{+\!\!+} Y')$ の
        第 1 選言がそのまま成り立つ。
      - $x = w$ かつ $X'' \prec_{\mathrm{lex}} W' \mathbin{+\!\!+} Y$：
        $\Phi(W')$ を $X := X''$、$Y := Y$ に適用する。第 1 の仮定は
        $X'' \preceq_{\mathrm{lex}} W' \mathbin{+\!\!+} Y$（第 2 選言）である。第 2 の仮定は次で確かめる。
        もしある $Z$ で $X'' = W' \mathbin{+\!\!+} Z$ ならば $X = w \mathbin{::} X'' = (w \mathbin{::} W') \mathbin{+\!\!+} Z$ となり
        $h_{np}$ に矛盾する。よって $X'' \prec_{\mathrm{lex}} W' \mathbin{+\!\!+} Y'$ を得る。
        目標の第 2 選言（$x = w$ かつ尾部が $\prec_{\mathrm{lex}}$）が成り立つ。∎

<a id="t-peel_aux"></a>
### 定理 自己言及的上界の剥がし (T.peel_aux)

**主張** $d, w \in \mathbb{N}$ とする。すべての $n \in \mathbb{N}$、$X, Q, A_2 \in \mathrm{PairSeq}$、$a \in \mathbb{N}$ について
$$\lvert X\rvert \le n \ \wedge\
X \preceq_{\mathrm{lex}} Q \mathbin{+\!\!+} (a,w) \mathbin{::} \mathrm{sh}_d(X \mathbin{+\!\!+} A_2)
\ \Longrightarrow\
\exists m,\ X \preceq_{\mathrm{lex}} Q \mathbin{+\!\!+} \mathrm{cp}_d\bigl((a,w) \mathbin{::} \mathrm{sh}_d Q,\ m\bigr) .$$

$\mathrm{ArgDomCore}$ の結論の上界は $X$ 自身を含む（自己言及的である）。この定理は、その上界を
$1$ 段ずつ剥がすと、比較が $Q \mathbin{+\!\!+} [(a,w)]$ の内部で決着するか、あるいは
$Q \mathbin{+\!\!+} [(a,w)]$ が $X$ から取り除かれて 1 段上で同じ形が再現するか、のいずれかであり、
後者の繰り返しがちょうどコピー塔になることを述べる。

**証明** $n$ に関する自然数の帰納法。帰納法の述語は
$$\Psi(n) :\equiv \forall X, Q, A_2, a,\ \lvert X\rvert \le n \to
X \preceq_{\mathrm{lex}} Q \mathbin{+\!\!+} (a,w) \mathbin{::} \mathrm{sh}_d(X \mathbin{+\!\!+} A_2) \to
\exists m,\ X \preceq_{\mathrm{lex}} Q \mathbin{+\!\!+} \mathrm{cp}_d((a,w) \mathbin{::} \mathrm{sh}_d Q, m)$$
である（$X, Q, A_2, a$ は帰納法の中で動かす）。

- 基底段 $n = 0$：$\lvert X\rvert \le 0$ より $X = []$。$m := 0$ とすると
  [(T.copies_zero)](Wf.md#t-copies_zero) より $\mathrm{cp}_d(\cdot,0) = []$ であるから、
  目標は $[] \preceq_{\mathrm{lex}} Q$ である。$Q = []$ なら等号が成り立ち、
  $Q = q \mathbin{::} Q'$ なら $\prec_{\mathrm{lex}}$ の第 1 の場合（右辺が空でない）により
  $[] \prec_{\mathrm{lex}} Q$。よって $\Psi(0)$。
- 帰納段 $n+1$：帰納法の仮定は $\Psi(n)$ である。
  $X, Q, A_2, a$ と $\lvert X\rvert \le n+1$、
  $h : X \preceq_{\mathrm{lex}} Q \mathbin{+\!\!+} (a,w) \mathbin{::} \mathrm{sh}_d(X \mathbin{+\!\!+} A_2)$ を与える。
  「$\exists X',\ X = Q \mathbin{+\!\!+} (a,w) \mathbin{::} X'$」の真偽で場合分けする（排中律）。

  **(i) $X = Q \mathbin{+\!\!+} (a,w) \mathbin{::} X'$ なる $X'$ が存在するとき。**
  $h$ は
  $$Q \mathbin{+\!\!+} (a,w) \mathbin{::} X' \ \preceq_{\mathrm{lex}}\
  Q \mathbin{+\!\!+} (a,w) \mathbin{::} \mathrm{sh}_d\bigl((Q \mathbin{+\!\!+} (a,w) \mathbin{::} X') \mathbin{+\!\!+} A_2\bigr)$$
  である。[(T.sle_append_cancel)](Cofinality.md#t-sle_append_cancel) で共通前部 $Q$ を、
  続いて共通前部 $[(a,w)]$ を消去すると
  $$X' \preceq_{\mathrm{lex}} \mathrm{sh}_d\bigl((Q \mathbin{+\!\!+} (a,w) \mathbin{::} X') \mathbin{+\!\!+} A_2\bigr) .$$
  右辺を書き換える。結合律と
  [(T.shiftr0_append)](Cofinality.md#t-shiftr0_append)、[(T.shiftr0_cons)](Wf.md#t-shiftr0_cons) より
  $$\mathrm{sh}_d\bigl((Q \mathbin{+\!\!+} (a,w) \mathbin{::} X') \mathbin{+\!\!+} A_2\bigr)
  = \mathrm{sh}_d Q \mathbin{+\!\!+} (a+d,\ w) \mathbin{::} \mathrm{sh}_d(X' \mathbin{+\!\!+} A_2)$$
  であるから、
  $$X' \preceq_{\mathrm{lex}} \mathrm{sh}_d Q \mathbin{+\!\!+} (a+d, w) \mathbin{::} \mathrm{sh}_d(X' \mathbin{+\!\!+} A_2) .$$
  これは $\Psi(n)$ の前提の形（$X := X'$、$Q := \mathrm{sh}_d Q$、$a := a+d$）である。長さは
  $\lvert X\rvert = \lvert Q\rvert + 1 + \lvert X'\rvert \le n+1$ より $\lvert X'\rvert \le n$。
  よって $\Psi(n)$ から $m$ が得られて
  $$X' \preceq_{\mathrm{lex}} \mathrm{sh}_d Q \mathbin{+\!\!+}
   \mathrm{cp}_d\bigl((a+d,w) \mathbin{::} \mathrm{sh}_d(\mathrm{sh}_d Q),\ m\bigr) .$$
  求める witness は $m+1$ である。実際、
  [(T.copies_succ_front)](Wf.md#t-copies_succ_front)、
  [(T.shiftr0_copies)](Cofinality.md#t-shiftr0_copies)、[(T.shiftr0_cons)](Wf.md#t-shiftr0_cons) より
  $$Q \mathbin{+\!\!+} \mathrm{cp}_d\bigl((a,w) \mathbin{::} \mathrm{sh}_d Q,\ m+1\bigr)
  = \bigl(Q \mathbin{+\!\!+} [(a,w)]\bigr) \mathbin{+\!\!+}
    \Bigl(\mathrm{sh}_d Q \mathbin{+\!\!+} \mathrm{cp}_d\bigl((a+d,w) \mathbin{::} \mathrm{sh}_d(\mathrm{sh}_d Q),\ m\bigr)\Bigr)$$
  であり（$\mathrm{cp}_d(\mathit{blk},m+1) = \mathit{blk} \mathbin{+\!\!+} \mathrm{sh}_d(\mathrm{cp}_d(\mathit{blk},m))$ に
  $\mathit{blk} = (a,w) \mathbin{::} \mathrm{sh}_d Q$ を代入し、
  $\mathrm{sh}_d(\mathrm{cp}_d(\mathit{blk},m)) = \mathrm{cp}_d(\mathrm{sh}_d\,\mathit{blk},m)$ と
  $\mathrm{sh}_d\bigl((a,w) \mathbin{::} \mathrm{sh}_d Q\bigr) = (a+d,w) \mathbin{::} \mathrm{sh}_d(\mathrm{sh}_d Q)$ を使った）、
  かつ $X = Q \mathbin{+\!\!+} (a,w) \mathbin{::} X' = \bigl(Q \mathbin{+\!\!+} [(a,w)]\bigr) \mathbin{+\!\!+} X'$ である。
  共通前部 $Q \mathbin{+\!\!+} [(a,w)]$ を [(T.sle_append_cancel)](Cofinality.md#t-sle_append_cancel) で付け直せば目標を得る。

  **(ii) そのような $X'$ が存在しないとき。**
  $m := 1$ とする。[(T.copies_one)](Wf.md#t-copies_one) より
  $\mathrm{cp}_d((a,w) \mathbin{::} \mathrm{sh}_d Q, 1) = (a,w) \mathbin{::} \mathrm{sh}_d Q$ であるから、
  目標は $X \prec_{\mathrm{lex}} Q \mathbin{+\!\!+} (a,w) \mathbin{::} \mathrm{sh}_d Q$（$\preceq_{\mathrm{lex}}$ の第 2 選言）である。
  $h$ を括り直すと
  $X \preceq_{\mathrm{lex}} \bigl(Q \mathbin{+\!\!+} [(a,w)]\bigr) \mathbin{+\!\!+} \mathrm{sh}_d(X \mathbin{+\!\!+} A_2)$ であり、
  仮定より $\forall X',\ X \ne \bigl(Q \mathbin{+\!\!+} [(a,w)]\bigr) \mathbin{+\!\!+} X'$
  （もし $X = (Q \mathbin{+\!\!+} [(a,w)]) \mathbin{+\!\!+} X'$ ならば $X = Q \mathbin{+\!\!+} (a,w) \mathbin{::} X'$ となり (i) の場合になる）。
  [(T.seqlex_of_sle_not_prefix)](#t-seqlex_of_sle_not_prefix) を
  $W := Q \mathbin{+\!\!+} [(a,w)]$、$Y := \mathrm{sh}_d(X \mathbin{+\!\!+} A_2)$、$Y' := \mathrm{sh}_d Q$ として適用すると
  $X \prec_{\mathrm{lex}} \bigl(Q \mathbin{+\!\!+} [(a,w)]\bigr) \mathbin{+\!\!+} \mathrm{sh}_d Q
   = Q \mathbin{+\!\!+} (a,w) \mathbin{::} \mathrm{sh}_d Q$ を得る。∎

**補足（再帰が停止する理由）.** (i) の各段で $X$ は $Q \mathbin{+\!\!+} [(a,w)]$ の分だけ短くなり、
とくに列 $(a,w)$ を 1 個は消費するので、長さの上界 $n$ が真に減る。これが $\Psi$ を $n$ についての
帰納法として立てられる理由であり、また [(D.AscArgDom)](Cofinality.md#d-AscArgDom) の witness
$m$ が有限で済む理由でもある。

<a id="t-sle_take_of_short"></a>
### 定理 短い側は後続を見ない (T.sle_take_of_short)

**主張** $P, X, Y \in \mathrm{PairSeq}$ とする。
$$X \preceq_{\mathrm{lex}} P \mathbin{+\!\!+} Y \quad\wedge\quad \lvert X\rvert \le \lvert P\rvert
\ \Longrightarrow\ X \preceq_{\mathrm{lex}} P .$$

**証明** $P$ に関するリストの構造帰納法。帰納法の述語は
$$\Xi(P) :\equiv \forall X, Y,\ X \preceq_{\mathrm{lex}} P \mathbin{+\!\!+} Y \to \lvert X\rvert \le \lvert P\rvert \to
X \preceq_{\mathrm{lex}} P .$$

- 基底段 $P = []$：$\lvert X\rvert \le 0$ より $X = []$、すなわち $X = P$ であり $\preceq_{\mathrm{lex}}$ の第 1 選言。
- 帰納段 $P = p \mathbin{::} P'$：帰納法の仮定は $\Xi(P')$。$X$ で場合分けする。
  - $X = []$：$p \mathbin{::} P' \ne []$ より $[] \prec_{\mathrm{lex}} p \mathbin{::} P'$。
  - $X = x \mathbin{::} X''$：仮定は $\lvert X''\rvert + 1 \le \lvert P'\rvert + 1$、すなわち $\lvert X''\rvert \le \lvert P'\rvert$ と
    $x \mathbin{::} X'' \preceq_{\mathrm{lex}} p \mathbin{::} (P' \mathbin{+\!\!+} Y)$ である。後者の 2 選言で場合分けする。
    - 等号 $x \mathbin{::} X'' = p \mathbin{::} (P' \mathbin{+\!\!+} Y)$：先頭を比べて $x = p$、尾部を比べて $X'' = P' \mathbin{+\!\!+} Y$。
      長さを取ると $\lvert X''\rvert = \lvert P'\rvert + \lvert Y\rvert$ であり、$\lvert X''\rvert \le \lvert P'\rvert$ と
      合わせて $\lvert Y\rvert = 0$、すなわち $Y = []$。よって $X'' = P'$ であり $X = p \mathbin{::} P' = P$。
    - $x \mathbin{::} X'' \prec_{\mathrm{lex}} p \mathbin{::} (P' \mathbin{+\!\!+} Y)$：$x \prec_{\mathrm{c}} p$ ならば
      $x \mathbin{::} X'' \prec_{\mathrm{lex}} p \mathbin{::} P'$。$x = p$ かつ $X'' \prec_{\mathrm{lex}} P' \mathbin{+\!\!+} Y$ ならば、
      $\Xi(P')$ を（第 2 選言と $\lvert X''\rvert \le \lvert P'\rvert$ に）適用して $X'' \preceq_{\mathrm{lex}} P'$ を得る。
      $X'' = P'$ なら $X = P$、$X'' \prec_{\mathrm{lex}} P'$ なら $x \mathbin{::} X'' \prec_{\mathrm{lex}} p \mathbin{::} P'$。∎

<a id="t-sle_trans"></a>
### 定理 $\preceq_{\mathrm{lex}}$ の推移律 (T.sle_trans)

**主張** $A \preceq_{\mathrm{lex}} B$ かつ $B \preceq_{\mathrm{lex}} C$ ならば $A \preceq_{\mathrm{lex}} C$。

**証明** $A \preceq_{\mathrm{lex}} B$ の 2 選言で場合分けする。$A = B$ のときは第 2 の仮定がそのまま結論である。
$A \prec_{\mathrm{lex}} B$ のときは [(T.seqlex_sle_trans)](Cofinality.md#t-seqlex_sle_trans) より
$A \prec_{\mathrm{lex}} C$、すなわち $\preceq_{\mathrm{lex}}$ の第 2 選言。∎

<a id="t-sle_of_append_left"></a>
### 定理 小さい側の右切り詰め (T.sle_of_append_left)

**主張** $X \mathbin{+\!\!+} Y \preceq_{\mathrm{lex}} W$ ならば $X \preceq_{\mathrm{lex}} W$。

**証明** まず $X \preceq_{\mathrm{lex}} X \mathbin{+\!\!+} Y$ を示す。$Y = []$ なら $X = X \mathbin{+\!\!+} Y$ で等号。
$Y \ne []$ なら [(T.seqlex_prefix)](Seqlex.md#t-seqlex_prefix) より $X \prec_{\mathrm{lex}} X \mathbin{+\!\!+} Y$。
これと仮定に [(T.sle_trans)](#t-sle_trans) を適用する。∎

<a id="t-seqlex_of_sle_snoc"></a>
### 定理 落とされる列の差し替え (T.seqlex_of_sle_snoc)

**主張** $X, Y \in \mathrm{PairSeq}$、$\mathit{lp}, q \in \mathbb{N}\times\mathbb{N}$ とする。
$$X \mathbin{+\!\!+} [\mathit{lp}] \preceq_{\mathrm{lex}} Y \quad\wedge\quad q \prec_{\mathrm{c}} \mathit{lp}
\quad\wedge\quad \lvert X\rvert < \lvert Y\rvert
\ \Longrightarrow\ \forall S', E,\ X \mathbin{+\!\!+} q \mathbin{::} S' \prec_{\mathrm{lex}} Y \mathbin{+\!\!+} E .$$

長さの条件 $\lvert X\rvert < \lvert Y\rvert$ は「$X$ が尽きたから小さい」という判定を排除するためのものである。

**証明** $X$ に関するリストの構造帰納法。帰納法の述語は
$$\Theta(X) :\equiv \forall Y, \mathit{lp}, q,\
X \mathbin{+\!\!+} [\mathit{lp}] \preceq_{\mathrm{lex}} Y \to q \prec_{\mathrm{c}} \mathit{lp} \to \lvert X\rvert < \lvert Y\rvert \to
\forall S', E,\ X \mathbin{+\!\!+} q \mathbin{::} S' \prec_{\mathrm{lex}} Y \mathbin{+\!\!+} E .$$

- 基底段 $X = []$：$0 < \lvert Y\rvert$ より $Y = y \mathbin{::} Y'$。目標は
  $q \mathbin{::} S' \prec_{\mathrm{lex}} y \mathbin{::} (Y' \mathbin{+\!\!+} E)$ であり、$q \prec_{\mathrm{c}} y$ を示せば十分である。
  仮定 $[\mathit{lp}] \preceq_{\mathrm{lex}} y \mathbin{::} Y'$ の 2 選言で場合分けする。
  - 等号 $[\mathit{lp}] = y \mathbin{::} Y'$：先頭を比べて $\mathit{lp} = y$ であるから、$q \prec_{\mathrm{c}} \mathit{lp}$ が $q \prec_{\mathrm{c}} y$。
  - $[\mathit{lp}] \prec_{\mathrm{lex}} y \mathbin{::} Y'$：$\mathit{lp} \prec_{\mathrm{c}} y$ ならば
    [(T.pairlt_trans)](Cofinality.md#t-pairlt_trans) より $q \prec_{\mathrm{c}} y$。
    $\mathit{lp} = y$（かつ尾部の比較）ならば直ちに $q \prec_{\mathrm{c}} y$。
- 帰納段 $X = x \mathbin{::} X'$：帰納法の仮定は $\Theta(X')$。$\lvert x \mathbin{::} X'\rvert < \lvert Y\rvert$ より $Y = y \mathbin{::} Y'$ で
  $\lvert X'\rvert < \lvert Y'\rvert$。仮定は $x \mathbin{::} (X' \mathbin{+\!\!+} [\mathit{lp}]) \preceq_{\mathrm{lex}} y \mathbin{::} Y'$、
  目標は $x \mathbin{::} (X' \mathbin{+\!\!+} q \mathbin{::} S') \prec_{\mathrm{lex}} y \mathbin{::} (Y' \mathbin{+\!\!+} E)$ である。
  - 等号のとき：$x = y$ かつ $X' \mathbin{+\!\!+} [\mathit{lp}] = Y'$。後者は
    $X' \mathbin{+\!\!+} [\mathit{lp}] \preceq_{\mathrm{lex}} Y'$（第 1 選言）を与えるから、$\Theta(X')$ より
    $X' \mathbin{+\!\!+} q \mathbin{::} S' \prec_{\mathrm{lex}} Y' \mathbin{+\!\!+} E$。目標の第 2 選言が成り立つ。
  - $\prec_{\mathrm{lex}}$ のとき：$x \prec_{\mathrm{c}} y$ ならば目標の第 1 選言。
    $x = y$ かつ $X' \mathbin{+\!\!+} [\mathit{lp}] \prec_{\mathrm{lex}} Y'$ ならば、$\Theta(X')$（第 2 選言と $\lvert X'\rvert < \lvert Y'\rvert$）より
    $X' \mathbin{+\!\!+} q \mathbin{::} S' \prec_{\mathrm{lex}} Y' \mathbin{+\!\!+} E$ であり、目標の第 2 選言が成り立つ。∎

<a id="t-shiftr0_injective"></a>
### 定理 $\mathrm{sh}_d$ は単射 (T.shiftr0_injective)

**主張** $\mathrm{sh}_d X = \mathrm{sh}_d Y$ ならば $X = Y$。

**証明** 写像 $f(p) := (\pi_0 p + d,\ \pi_1 p)$ は単射である。実際 $f(a) = f(b)$ とすると
$\pi_0 a + d = \pi_0 b + d$ と $\pi_1 a = \pi_1 b$ が成り立ち、前者から $\pi_0 a = \pi_0 b$、
よって $a = b$。`List.map_injective_iff` より $\mathrm{map}\,f$ も単射であり、
$\mathrm{sh}_d = \mathrm{map}\,f$ であるから主張を得る。∎

<a id="t-seqlex_shiftr0"></a>
### 定理 $\mathrm{sh}_d$ は $\prec_{\mathrm{lex}}$ の同型 (T.seqlex_shiftr0)

**主張** 任意の $d$ と $X, Y \in \mathrm{PairSeq}$ について
$$\mathrm{sh}_d X \prec_{\mathrm{lex}} \mathrm{sh}_d Y \iff X \prec_{\mathrm{lex}} Y .$$

**証明** $X$ に関するリストの構造帰納法。帰納法の述語は
$$\Lambda(X) :\equiv \forall Y,\ \bigl(\mathrm{sh}_d X \prec_{\mathrm{lex}} \mathrm{sh}_d Y \iff X \prec_{\mathrm{lex}} Y\bigr) .$$

- 基底段 $X = []$：$\mathrm{sh}_d [] = []$ である。$Y = []$ のとき両辺とも偽（$\prec_{\mathrm{lex}}$ の第 1 の場合で
  右辺が空）。$Y = y \mathbin{::} Y'$ のとき $\mathrm{sh}_d Y = (\pi_0 y + d, \pi_1 y) \mathbin{::} \mathrm{sh}_d Y' \ne []$ であり、
  両辺とも真。
- 帰納段 $X = x \mathbin{::} X'$：帰納法の仮定は $\Lambda(X')$。
  - $Y = []$：$\mathrm{sh}_d X \ne []$、$X \ne []$ であるから両辺とも偽。
  - $Y = y \mathbin{::} Y'$：[(T.shiftr0_cons)](Wf.md#t-shiftr0_cons) で両辺を展開すると、左辺は
    $$(\pi_0 x + d, \pi_1 x) \prec_{\mathrm{c}} (\pi_0 y + d, \pi_1 y)
    \ \vee\ \bigl((\pi_0 x + d, \pi_1 x) = (\pi_0 y + d, \pi_1 y) \wedge \mathrm{sh}_d X' \prec_{\mathrm{lex}} \mathrm{sh}_d Y'\bigr),$$
    右辺は $x \prec_{\mathrm{c}} y \vee (x = y \wedge X' \prec_{\mathrm{lex}} Y')$ である。
    $\pi_0 x + d < \pi_0 y + d \iff \pi_0 x < \pi_0 y$ および
    $\pi_0 x + d = \pi_0 y + d \iff \pi_0 x = \pi_0 y$ であるから、第 1 選言どうし・
    ペアの等号どうしが同値であり、尾部の同値は $\Lambda(X')$ による。∎

<a id="t-sle_shiftr0"></a>
### 定理 $\mathrm{sh}_d$ は $\preceq_{\mathrm{lex}}$ の同型 (T.sle_shiftr0)

**主張** $\mathrm{sh}_d X \preceq_{\mathrm{lex}} \mathrm{sh}_d Y \iff X \preceq_{\mathrm{lex}} Y$。

**証明** $\preceq_{\mathrm{lex}}$ の定義を展開すると、両辺はそれぞれ
$\mathrm{sh}_d X = \mathrm{sh}_d Y \vee \mathrm{sh}_d X \prec_{\mathrm{lex}} \mathrm{sh}_d Y$ と
$X = Y \vee X \prec_{\mathrm{lex}} Y$ である。第 2 選言どうしは
[(T.seqlex_shiftr0)](#t-seqlex_shiftr0) により同値。第 1 選言について、
$(\Rightarrow)$ は [(T.shiftr0_injective)](#t-shiftr0_injective)、
$(\Leftarrow)$ は $X = Y$ の両辺に $\mathrm{sh}_d$ を適用すればよい。∎

---

## Part B — 側条件と、宿主を含まない核

<a id="d-SpineOK"></a>
### 定義 側条件 (D.SpineOK)

$A \in \mathrm{PairSeq}$、$L, w \in \mathbb{N}$ に対し
$$\mathrm{SpineOK}(A, L, w) :\iff
\forall U, V \in \mathrm{PairSeq},\ \forall x \in \mathbb{N}\times\mathbb{N},\
\Bigl(A = U \mathbin{+\!\!+} x \mathbin{::} V \ \wedge\ \pi_0 x < L \ \wedge\
 \bigl(\forall y \in V,\ \pi_0 x < \pi_0 y\bigr)\Bigr) \to w \le \pi_1 x .$$

条件 $\forall y \in V,\ \pi_0 x < \pi_0 y$ を「$x$ は $A$ の中で**右から見える**」と呼ぶ
（$x$ より後ろに $x$ の行 0 の値以下の列が 1 つも無い、という意味であり、この語はこの式の略記としてのみ用いる）。
$\mathrm{SpineOK}(A,L,w)$ は「$A$ の右から見える列のうち行 0 の値が $L$ 未満のものはすべて行 1 の値が $w$ 以上である」
という言明である。

<a id="d-ArgDomCore"></a>
### 定義 宿主を含まない核 (D.ArgDomCore)

$$
\begin{aligned}
\mathrm{ArgDomCore} :\iff\ &\forall X, A_1, B, A_2, Z \in \mathrm{PairSeq},\ \forall u, w, e \in \mathbb{N}, \\
&\quad \Bigl(X \mathbin{+\!\!+} (u,w) \mathbin{::} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} A_2)\bigr)\Bigr) \mathbin{+\!\!+} Z \in \mathrm{ST\_PS} \\
&\quad \wedge\ 0 < e \\
&\quad \wedge\ \bigl(\forall x \in A_1,\ u < \pi_0 x\bigr) \\
&\quad \wedge\ \bigl(\forall x \in B,\ u + e < \pi_0 x\bigr) \\
&\quad \wedge\ \bigl(\forall x \in A_2,\ u < \pi_0 x\bigr) \\
&\quad \wedge\ \bigl(A_2 = [] \ \vee\ \pi_0(\mathrm{headI}\,A_2) \le u + e\bigr) \\
&\quad \wedge\ \bigl(Z = [] \ \vee\ \pi_0(\mathrm{headI}\,Z) \le u\bigr) \\
&\quad \wedge\ \mathrm{SpineOK}(A_1,\ u+e,\ w) \\
&\quad \longrightarrow\
 B \preceq_{\mathrm{lex}} \mathrm{sh}_e\bigl(A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} A_2)\bigr)
\end{aligned}
$$

読み方は次の通りである。1 つの標準形の内部で、列 $(u,w)$ の引数（子孫ブロック）が
$A := A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} A_2)$ であり、その中に**同じ行 1 の値 $w$ をもつ**より深い列
$(u+e,w)$ があって、その引数が $B$ であるとする。このとき $B$ は $A$ の $e$-シフト $\mathrm{sh}_e A$ に
$\preceq_{\mathrm{lex}}$ で支配される。

側条件 $\mathrm{SpineOK}(A_1, u+e, w)$（[(D.SpineOK)](#d-SpineOK)）は、2 つの印付き列の間にある
「右から見える」列で行 0 の値が $u+e$ 未満のものがすべて行 1 の値 $\ge w$ をもつ、という条件である。
これを外すと言明は偽になる（[Part E](#part-e) 参照）。

---

## Part C — 側条件は宿主が供給する

この節は本章で唯一、宿主 $M$ を使う場所である。
[(D.nextrel1)](Def.md#d-nextrel1) の最小性条項（第 6 条件）がここで働く。

<a id="t-spineOK_of_nextrel1"></a>
### 定理 nextrel1 条項から側条件 (T.spineOK_of_nextrel1)

**主張** $G, R \in \mathrm{PairSeq}$、$v_0, w_0, d_0 \in \mathbb{N}$ とし、
$\mathit{lp} := (v_0+d_0,\ w_0+1)$、$M := \bigl(G \mathbin{+\!\!+} ((v_0,w_0) \mathbin{::} R)\bigr) \mathbin{+\!\!+} [\mathit{lp}]$ とおく。
$$\lvert G\rvert \to^M_1 \bigl\lvert G \mathbin{+\!\!+} ((v_0,w_0) \mathbin{::} R)\bigr\rvert
\ \Longrightarrow\ \mathrm{SpineOK}(R,\ v_0+d_0,\ w_0) .$$

**証明** $j_1 := \lvert G \mathbin{+\!\!+} ((v_0,w_0) \mathbin{::} R)\rvert$ とおく。$j_1$ は $M$ の最終列 $\mathit{lp}$ の位置である。
仮定 $\lvert G\rvert \to^M_1 j_1$ を [(D.nextrel1)](Def.md#d-nextrel1) の 6 条件に分解し、
第 5 条件 $\lvert G\rvert \le^M_0 j_1$ と第 6 条件
$$\forall j,\ \bigl(\lvert G\rvert < j \ \wedge\ j \le^M_0 j_1\bigr) \to M_{1,j_1} \le M_{1,j}$$
を用いる。

$\mathrm{SpineOK}$ の定義に従い、$R = U \mathbin{+\!\!+} x \mathbin{::} V$、$\pi_0 x < v_0 + d_0$、
$\forall y \in V,\ \pi_0 x < \pi_0 y$ を仮定して $w_0 \le \pi_1 x$ を示す。
$A := G \mathbin{+\!\!+} ((v_0,w_0) \mathbin{::} U)$ とおくと、$R$ の分解から
$$M = A \mathbin{+\!\!+} \bigl(x \mathbin{::} (V \mathbin{+\!\!+} [\mathit{lp}])\bigr),\qquad
\lvert A\rvert = \lvert G\rvert + 1 + \lvert U\rvert,\qquad
j_1 = \lvert A\rvert + 1 + \lvert V\rvert$$
である（最後の等式は $\lvert R\rvert = \lvert U\rvert + 1 + \lvert V\rvert$ による）。
[(T.getD_append_right')](Cofinality.md#t-getD_append_right') より
$M\langle \lvert A\rvert\rangle = x$ である。

**$x$ より後ろの列はすべて $x$ より行 0 が真に大きい。** すなわち
$$\forall y,\ \lvert A\rvert < y \le j_1 \ \Longrightarrow\ M_{0,\lvert A\rvert} < M_{0,y} . \tag{$\ast$}$$
実際、$y = \lvert A\rvert + (t+1)$ と書くと
[(T.getD_append_right')](Cofinality.md#t-getD_append_right') より
$M\langle \lvert A\rvert + (t+1)\rangle = (V \mathbin{+\!\!+} [\mathit{lp}])\langle t\rangle$ である。
$y \le j_1 = \lvert A\rvert + 1 + \lvert V\rvert$ より $t \le \lvert V\rvert$ であるから、2 つの場合がある。
- $t < \lvert V\rvert$：$(V \mathbin{+\!\!+} [\mathit{lp}])\langle t\rangle = V\langle t\rangle \in V$ であり、
  仮定 $\forall y \in V,\ \pi_0 x < \pi_0 y$ から $\pi_0 x < \pi_0(V\langle t\rangle)$。
- $t = \lvert V\rvert$：$(V \mathbin{+\!\!+} [\mathit{lp}])\langle \lvert V\rvert\rangle = \mathit{lp}$ であり、
  仮定 $\pi_0 x < v_0 + d_0 = \pi_0 \mathit{lp}$ から結論を得る。

**$x$ は落とされる列の行 0 祖先である。** $\lvert G\rvert < \lvert A\rvert \le j_1$（前者は
$\lvert A\rvert = \lvert G\rvert + 1 + \lvert U\rvert$ から、後者は $j_1 = \lvert A\rvert + 1 + \lvert V\rvert$ から）
と $(\ast)$ に [(T.le0_through_pivot)](Nrmstep.md#t-le0_through_pivot) を適用すると、
第 5 条件 $\lvert G\rvert \le^M_0 j_1$ から $\lvert A\rvert \le^M_0 j_1$ が得られる。

**最小性条項の適用。** 第 6 条件を $j := \lvert A\rvert$ に適用する。前提 $\lvert G\rvert < \lvert A\rvert$ と
$\lvert A\rvert \le^M_0 j_1$ はいま示した。結論は $M_{1,j_1} \le M_{1,\lvert A\rvert}$ である。
ここで $M\langle j_1\rangle = \mathit{lp}$（$M$ は長さ $j_1$ の列に $[\mathit{lp}]$ を継いだものである）であるから
[(T.entry_one)](Cofinality.md#t-entry_one) より $M_{1,j_1} = \pi_1 \mathit{lp} = w_0 + 1$、
また $M_{1,\lvert A\rvert} = \pi_1 x$ である。よって $w_0 + 1 \le \pi_1 x$、とくに $w_0 \le \pi_1 x$。∎

---

## Part D — 還元

<a id="t-ascArgDom_of_core"></a>
### 定理 核から AscArgDom (T.ascArgDom_of_core)

**主張** $\mathrm{ArgDomCore}$（[(D.ArgDomCore)](#d-ArgDomCore)）が成り立つならば
$\mathrm{AscArgDom}$（[(D.AscArgDom)](Cofinality.md#d-AscArgDom)）が成り立つ。

**証明** $\mathrm{AscArgDom}$ の仮定を与える。すなわち $G, R, S \in \mathrm{PairSeq}$、$v_0, w_0, d_0 \in \mathbb{N}$ と
- $h_N$：$\bigl(G \mathbin{+\!\!+} ((v_0,w_0) \mathbin{::} R)\bigr) \mathbin{+\!\!+} (v_0+d_0,w_0) \mathbin{::} S \in \mathrm{ST\_PS}$
- $h_{Rgt}$：$\forall x \in R,\ v_0 < \pi_0 x$
- $h_d$：$0 < d_0$
- $h_{nr}$：$\lvert G\rvert \to^{M}_1 \lvert G \mathbin{+\!\!+} ((v_0,w_0)\mathbin{::}R)\rvert$。ここで
  $M := \bigl(G \mathbin{+\!\!+} ((v_0,w_0) \mathbin{::} R)\bigr) \mathbin{+\!\!+} [(v_0+d_0,\ w_0+1)]$ は宿主である

を与える（$\mathrm{AscArgDom}$ のもう一方の仮定 $M \in \mathrm{ST\_PS}$ はこの証明では使わない）。
目標は
$$\exists m,\ \mathrm{tw}_{v_0+d_0} S \preceq_{\mathrm{lex}}
\mathrm{sh}_{d_0}\Bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}\bigl(\mathrm{sh}_{d_0}((v_0,w_0) \mathbin{::} R),\ m\bigr)\Bigr)$$
である。

**$S$ の 3 分割.** $S_{hi} := \mathrm{tw}_{v_0+d_0} S$、$D := \mathrm{dw}_{v_0+d_0} S$、
$A_2 := \mathrm{tw}_{v_0} D$、$Z := \mathrm{dw}_{v_0} D$ とおく。`List.takeWhile_append_dropWhile` より
$S_{hi} \mathbin{+\!\!+} D = S$ かつ $A_2 \mathbin{+\!\!+} Z = D$。`List.mem_takeWhile_imp` より
$$\forall x \in S_{hi},\ v_0 + d_0 < \pi_0 x, \qquad \forall x \in A_2,\ v_0 < \pi_0 x .$$

**先頭の条件.** まず $D = [] \vee \pi_0(\mathrm{headI}\,D) \le v_0+d_0$：$D \ne []$ のとき、
`List.head?_dropWhile_not` より $D$ の先頭は述語 $\lambda p.\ v_0+d_0 < \pi_0 p$ をみたさない、
すなわち $\pi_0(\mathrm{headI}\,D) \le v_0+d_0$。
次に $A_2 = [] \vee \pi_0(\mathrm{headI}\,A_2) \le v_0+d_0$：$A_2 \ne []$ とすると $D \ne []$ であり、
$D = y \mathbin{::} Y$ と書くと、$v_0 < \pi_0 y$ の場合は $A_2 = y \mathbin{::} \mathrm{tw}_{v_0} Y$ で
$\mathrm{headI}\,A_2 = y = \mathrm{headI}\,D$、$v_0 \ge \pi_0 y$ の場合は $A_2 = []$ となって仮定に反する。
よって $\mathrm{headI}\,A_2 = \mathrm{headI}\,D$ であり、上の $D$ の評価が使える。
最後に $Z = [] \vee \pi_0(\mathrm{headI}\,Z) \le v_0$：$D$ の場合と同じく `List.head?_dropWhile_not` による。

**$N$ の括り直し.** $S = S_{hi} \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)$ であるから
$$\bigl(G \mathbin{+\!\!+} ((v_0,w_0) \mathbin{::} R)\bigr) \mathbin{+\!\!+} (v_0+d_0,w_0) \mathbin{::} S
= \Bigl(G \mathbin{+\!\!+} (v_0,w_0) \mathbin{::} \bigl(R \mathbin{+\!\!+} (v_0+d_0,w_0) \mathbin{::} (S_{hi} \mathbin{+\!\!+} A_2)\bigr)\Bigr) \mathbin{+\!\!+} Z .$$

**核の適用.** [(D.ArgDomCore)](#d-ArgDomCore) を
$$X := G,\quad u := v_0,\quad w := w_0,\quad A_1 := R,\quad e := d_0,\quad B := S_{hi},\quad A_2 := A_2,\quad Z := Z$$
として適用する。標準形の仮定は上の括り直しにより $h_N$ そのもの、$0 < e$ は $h_d$、
$\forall x \in A_1,\ u < \pi_0 x$ は $h_{Rgt}$、$\forall x \in B,\ u+e < \pi_0 x$ と
$\forall x \in A_2,\ u < \pi_0 x$ と 2 つの先頭条件は上で示したもの、
$\mathrm{SpineOK}(R, v_0+d_0, w_0)$ は [(T.spineOK_of_nextrel1)](#t-spineOK_of_nextrel1) を $h_{nr}$ に適用したものである。
結論は
$$S_{hi} \preceq_{\mathrm{lex}} \mathrm{sh}_{d_0}\bigl(R \mathbin{+\!\!+} (v_0+d_0,w_0) \mathbin{::} (S_{hi} \mathbin{+\!\!+} A_2)\bigr) .$$

**自己言及的上界の展開.** [(T.shiftr0_append)](Cofinality.md#t-shiftr0_append) と
[(T.shiftr0_cons)](Wf.md#t-shiftr0_cons) により右辺は
$\mathrm{sh}_{d_0} R \mathbin{+\!\!+} (v_0+d_0+d_0,\ w_0) \mathbin{::} \mathrm{sh}_{d_0}(S_{hi} \mathbin{+\!\!+} A_2)$ に等しい。
これは [(T.peel_aux)](#t-peel_aux) の前提の形（$d := d_0$、$w := w_0$、$X := S_{hi}$、
$Q := \mathrm{sh}_{d_0} R$、$a := v_0+d_0+d_0$、$n := \lvert S_{hi}\rvert$）であるから、$m$ が得られて
$$S_{hi} \preceq_{\mathrm{lex}} \mathrm{sh}_{d_0} R \mathbin{+\!\!+}
 \mathrm{cp}_{d_0}\bigl((v_0+d_0+d_0,\ w_0) \mathbin{::} \mathrm{sh}_{d_0}(\mathrm{sh}_{d_0} R),\ m\bigr) .$$
最後に、[(T.shiftr0_append)](Cofinality.md#t-shiftr0_append)、
[(T.shiftr0_copies)](Cofinality.md#t-shiftr0_copies)、[(T.shiftr0_cons)](Wf.md#t-shiftr0_cons) を 2 度使うと
$$\mathrm{sh}_{d_0}\Bigl(R \mathbin{+\!\!+} \mathrm{cp}_{d_0}\bigl(\mathrm{sh}_{d_0}((v_0,w_0)\mathbin{::}R),\ m\bigr)\Bigr)
= \mathrm{sh}_{d_0} R \mathbin{+\!\!+}
 \mathrm{cp}_{d_0}\bigl((v_0+d_0+d_0,\ w_0) \mathbin{::} \mathrm{sh}_{d_0}(\mathrm{sh}_{d_0} R),\ m\bigr)$$
であり、これは上の右辺そのものである。よって同じ $m$ が目標の witness を与える。∎

<a id="t-pss_cofinality_of_core"></a>
### 定理 核から PSS Bachmann 共終性 (T.pss_cofinality_of_core)

**主張** $\mathrm{ArgDomCore}$ が成り立つとする。$M, N \in \mathrm{ST\_PS}$ かつ
$\mathrm{tr}\,N \prec \mathrm{tr}\,M$ ならば
$$\exists n,\ 1 \le n \ \wedge\ \mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n]) .$$

**証明** [(T.ascArgDom_of_core)](#t-ascArgDom_of_core) より $\mathrm{AscArgDom}$ が成り立つ。
これを [(T.pss_cofinality_of_argdom)](Cofinality.md#t-pss_cofinality_of_argdom) に与えればよい。∎

---

<a id="part-e"></a>

## Part E — 核は到達可能性を本質的に要する

$\mathrm{ArgDomCore}$ は、本証明が使う**局所不変量**（[(D.blockok)](Seqlex.md#d-blockok)、
[(D.z0ok)](Nrmstep.md#d-z0ok)、[(D.r1ok)](Nrmstep.md#d-r1ok)、[(D.cnf)](Wf.md#d-cnf)）からは従わない。
反例は
$$L := (0,0)\,(1,1)\,(2,1)\,(3,2)\,(2,1)\,(3,2)$$
である。この節に Lean の宣言は無い（Lean 側ではソース中の注記として記録されている）。
以下、**本文で直接検証できる部分**と、**モデル検査の記録にとどまる部分**を明示して述べる。

**(1) 結論の反証（直接検証）.** $u := 1$、$w := 1$、$e := 1$ とし、
$$X := [(0,0)],\quad A_1 := [],\quad B := [(3,2)],\quad A_2 := [(2,1),(3,2)],\quad Z := []$$
と取る。このとき
$$\bigl(X \mathbin{+\!\!+} (u,w) \mathbin{::} (A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} A_2))\bigr) \mathbin{+\!\!+} Z
= (0,0)\,(1,1)\,(2,1)\,(3,2)\,(2,1)\,(3,2) = L$$
であり、[(D.ArgDomCore)](#d-ArgDomCore) の側条件はすべて成り立つ。実際
$0 < e$；$A_1 = []$ なので $\forall x \in A_1,\ u < \pi_0 x$ は空虚に真、
かつ $\mathrm{SpineOK}([], 2, 1)$ も $[] = U \mathbin{+\!\!+} x \mathbin{::} V$ となる分解が存在しないので空虚に真；
$B$ の唯一の列は $(3,2)$ で $u+e = 2 < 3$；$A_2$ の列は $(2,1),(3,2)$ でともに $u = 1 < \pi_0$；
$\pi_0(\mathrm{headI}\,A_2) = 2 \le 2 = u+e$；$Z = []$。
一方、結論は
$$[(3,2)] \preceq_{\mathrm{lex}} \mathrm{sh}_1\bigl((2,1)\,(3,2)\,(2,1)\,(3,2)\bigr) = (3,1)\,(4,2)\,(3,1)\,(4,2)$$
であるが、先頭を比べると $(3,2) \prec_{\mathrm{c}} (3,1)$ は
$3 < 3$ も $(3 = 3 \wedge 2 < 1)$ も成り立たないので偽、また $(3,2) \ne (3,1)$ であるから
$\prec_{\mathrm{lex}}$ の第 3 の場合の 2 選言がともに偽であり、$[(3,2)] \prec_{\mathrm{lex}} (3,1)(4,2)(3,1)(4,2)$ は偽。
等号も長さが違うので偽。よって結論は成り立たない。

**(2) 局所不変量（直接検証）.**
- $\mathrm{blockok}\,0\,L$：定義は「$L \ne [] \to \pi_0(\mathrm{headI}\,L) = 0$」「$\forall p \in L,\ 0 \le \pi_0 p$」
  「$\mathrm{steps1}\,L$」（[(D.steps1)](Seqlex.md#d-steps1)）の連言である。$\mathrm{headI}\,L = (0,0)$ より $\pi_0(\mathrm{headI}\,L) = 0$ で第 1 条件が成り立ち、
  第 2 条件は任意の自然数 $t$ について $0 \le t$ であることによる。
  $\mathrm{steps1}$ は隣接する列について $\pi_0(\text{次}) \le \pi_0(\text{前}) + 1$ を要求する。
  行 0 の値の列は $0,1,2,3,2,3$ であり、$1 \le 0+1$、$2 \le 1+1$、$3 \le 2+1$、$2 \le 3+1$、$3 \le 2+1$
  がすべて成り立つ。
- $\mathrm{z0ok}\,L$：行 0 の値が $0$ の列は第 $0$ 列 $(0,0)$ のみで、その行 1 の値は $0$ である。
- $\mathrm{r1ok}\,L$：行 0 の値が正の各 $j$ について、
  $\pi_0(L\langle k\rangle) + 1 = \pi_0(L\langle j\rangle)$、
  $\forall l\ (k < l < j \to \pi_0(L\langle j\rangle) \le \pi_0(L\langle l\rangle))$、
  $\pi_1(L\langle j\rangle) \le \pi_1(L\langle k\rangle) + 1$ をみたす $k < j$ を挙げる。
  $j=1$ に $k=0$（$0+1=1$、間に列なし、$1 \le 0+1$）、
  $j=2$ に $k=1$（$1+1=2$、間に列なし、$1 \le 1+1$）、
  $j=3$ に $k=2$（$2+1=3$、間に列なし、$2 \le 1+1$）、
  $j=4$ に $k=1$（$1+1=2$、$l=2,3$ の行 0 は $2,3 \ge 2$、$1 \le 1+1$）、
  $j=5$ に $k=4$（$2+1=3$、間に列なし、$2 \le 1+1$）。

**(3) モデル検査の記録（本文では検証しない）.** $\mathrm{cnf}(\mathrm{tr}\,L)$ が成り立つこと、および
$L \notin \mathrm{ST\_PS}$ であることは、Lean ソースのコメントに 3 つの閉包
（`tools/probe_k1c4.py` による）でのモデル検査結果として記録されているのみであり、
Lean で証明された命題ではない。

<!-- TODO: (3) の 2 つの主張（cnf (translate L) と L ∉ ST_PS）は Lean 側に宣言が無く、
     ソースのコメントに記録されたモデル検査の結果である。本文でも証明を与えていない。 -->

(1) と (2) から、局所不変量 $\mathrm{blockok}\,0$、$\mathrm{z0ok}$、$\mathrm{r1ok}$ だけを仮定して
$\mathrm{ArgDomCore}$ の結論を導くことはできない。したがって証明は
[(D.ST_PS)](Def.md#d-ST_PS) の**導出そのもの**に降りる必要がある。次の Part F がそれである。

---

## Part F — $\mathrm{ArgDomCore}$ の ST_PS 導出帰納

[(D.ST_PS)](Def.md#d-ST_PS) の帰納法原理を使うため、核を「列 $N$ ごとの述語」に書き直す。

<a id="d-ArgDomCoreOn"></a>
### 定義 核の列ごとの形 (D.ArgDomCoreOn)

$N \in \mathrm{PairSeq}$ に対し、$\mathrm{ArgDomCoreOn}(N)$ を次で定める。

$$
\begin{aligned}
\mathrm{ArgDomCoreOn}(N) :\iff\ &\forall X, A_1, B, A_2, Z \in \mathrm{PairSeq},\ \forall u, w, e \in \mathbb{N}, \\
&\quad N = \Bigl(X \mathbin{+\!\!+} (u,w) \mathbin{::} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} A_2)\bigr)\Bigr) \mathbin{+\!\!+} Z \\
&\quad \wedge\ 0 < e
 \ \wedge\ \bigl(\forall x \in A_1,\ u < \pi_0 x\bigr)
 \ \wedge\ \bigl(\forall x \in B,\ u + e < \pi_0 x\bigr)
 \ \wedge\ \bigl(\forall x \in A_2,\ u < \pi_0 x\bigr) \\
&\quad \wedge\ \bigl(A_2 = [] \vee \pi_0(\mathrm{headI}\,A_2) \le u + e\bigr)
 \ \wedge\ \bigl(Z = [] \vee \pi_0(\mathrm{headI}\,Z) \le u\bigr)
 \ \wedge\ \mathrm{SpineOK}(A_1, u+e, w) \\
&\quad \longrightarrow\
 B \preceq_{\mathrm{lex}} \mathrm{sh}_e\bigl(A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} A_2)\bigr)
\end{aligned}
$$

[(D.ArgDomCore)](#d-ArgDomCore) との違いは、標準形の仮定が「$N$ が上の形に分解される」という等式に置き換わり、
$N$ 自身が外側の変数になったことだけである。以下、$N$ の分解が与えられたとき
$$i := \lvert X\rvert, \qquad j := \lvert X\rvert + (\lvert A_1\rvert + 1)$$
を、それぞれ**浅い方の印付き列** $(u,w)$ と**深い方の印付き列** $(u+e,w)$ の位置と呼ぶ
（[(T.argdom_pos)](#t-argdom_pos) がこの命名を正当化する）。

<a id="t-argDomCore_of_on"></a>
### 定理 列ごとの形から核 (T.argDomCore_of_on)

**主張** $\forall N,\ N \in \mathrm{ST\_PS} \to \mathrm{ArgDomCoreOn}(N)$ ならば $\mathrm{ArgDomCore}$。

**証明** $\mathrm{ArgDomCore}$ のデータ $X, A_1, B, A_2, Z, u, w, e$ と 8 つの仮定
（標準形性と 7 つの側条件）を与える。第 1 の仮定は
$N := \bigl(X \mathbin{+\!\!+} (u,w) \mathbin{::} (A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} A_2))\bigr) \mathbin{+\!\!+} Z$ が標準形であること
であるから、仮定を $N$ に適用して $\mathrm{ArgDomCoreOn}(N)$ を得る。これを分解の等式（$N = N$、すなわち反射性）と
残り 7 つの側条件に適用すれば、目標がそのまま結論である。∎

<a id="t-argdom_pos"></a>
### 定理 印付き列の位置 (T.argdom_pos)

**主張** $N = \bigl(X \mathbin{+\!\!+} (u,w) \mathbin{::} (A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} A_2))\bigr) \mathbin{+\!\!+} Z$ ならば
$$N\langle \lvert X\rvert\rangle = (u,w), \qquad
N\bigl\langle \lvert X\rvert + (\lvert A_1\rvert+1)\bigr\rangle = (u+e,w), \qquad
\lvert X\rvert + (\lvert A_1\rvert+1) < \lvert N\rvert .$$

**証明** まず結合律により
$$N = X \mathbin{+\!\!+} \Bigl((u,w) \mathbin{::} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} ((B \mathbin{+\!\!+} A_2) \mathbin{+\!\!+} Z)\bigr)\Bigr) .$$
[(T.getD_append_right')](Cofinality.md#t-getD_append_right') は
$(P \mathbin{+\!\!+} Q)\langle \lvert P\rvert + t\rangle = Q\langle t\rangle$ である。

- $t = 0$ として $N\langle \lvert X\rvert\rangle = \bigl((u,w) \mathbin{::} \cdots\bigr)\langle 0\rangle = (u,w)$。
- $t = \lvert A_1\rvert + 1$ として
  $N\langle \lvert X\rvert + (\lvert A_1\rvert+1)\rangle
   = \bigl((u,w) \mathbin{::} (A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} \cdots)\bigr)\langle \lvert A_1\rvert+1\rangle
   = \bigl(A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} \cdots\bigr)\langle \lvert A_1\rvert\rangle$
  であり、再び同じ補題（$P := A_1$、$t := 0$）を使って $(u+e,w)$。
- 長さ：$\lvert N\rvert = \lvert X\rvert + 1 + \bigl(\lvert A_1\rvert + 1 + (\lvert B\rvert + \lvert A_2\rvert + \lvert Z\rvert)\bigr)$
  であるから $\lvert X\rvert + \lvert A_1\rvert + 1 < \lvert N\rvert$。∎

<a id="t-argDomCoreOn_diag"></a>
### 定理 基底段：対角列 (T.argDomCoreOn_diag)

**主張** 任意の $v \in \mathbb{N}$ について $\mathrm{ArgDomCoreOn}(\Delta_0^v)$。

**証明** $\Delta_0^v$ の分解 $X, A_1, B, A_2, Z, u, w, e$ が与えられたとして矛盾を導く
（したがって結論は空虚に成り立つ）。
[(T.argdom_pos)](#t-argdom_pos) より、$i := \lvert X\rvert$、$j := \lvert X\rvert + (\lvert A_1\rvert+1)$ とおくと
$$\Delta_0^v\langle i\rangle = (u,w), \qquad \Delta_0^v\langle j\rangle = (u+e,w), \qquad j < \lvert \Delta_0^v\rvert .$$
[(T.diagSeq0_length)](Nrmstep.md#t-diagSeq0_length) より $\lvert \Delta_0^v\rvert = v+1$ であるから $j < v+1$、
また $i < j$ より $i < v+1$。よって [(T.diagSeq0_getD)](Nrmstep.md#t-diagSeq0_getD) が両方の位置で使えて
$$\Delta_0^v\langle i\rangle = (i,i), \qquad \Delta_0^v\langle j\rangle = (j,j) .$$
第 2 成分を比べると $i = w$ かつ $j = w$、したがって $i = j$。
しかし $j = i + (\lvert A_1\rvert + 1) \ge i+1 > i$ であり矛盾する。∎

これが「対角列では行 1 の値が等しい 2 つの列は同一の列である」という基底段の内容である
（$0 < e$ すら使っていない）。

<a id="t-argDomCoreOn_snoc_zero"></a>
### 定理 末尾に $(0,\cdot)$ を付けても変わらない (T.argDomCoreOn_snoc_zero)

**主張** $p \in \mathbb{N}\times\mathbb{N}$ が $\pi_0 p = 0$ をみたし、$\mathrm{ArgDomCoreOn}(N \mathbin{+\!\!+} [p])$ ならば
$\mathrm{ArgDomCoreOn}(N)$。

**証明** $N$ の分解 $X, A_1, B, A_2, Z, u, w, e$ と 7 つの側条件を与える。
仮定 $\mathrm{ArgDomCoreOn}(N \mathbin{+\!\!+} [p])$ を、同じ $X, A_1, B, A_2, u, w, e$ と
$Z' := Z \mathbin{+\!\!+} [p]$ に適用する。

- 分解の等式：$N \mathbin{+\!\!+} [p]
  = \Bigl(\bigl(X \mathbin{+\!\!+} (u,w) \mathbin{::} (A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} A_2))\bigr) \mathbin{+\!\!+} Z\Bigr) \mathbin{+\!\!+} [p]
  = \bigl(X \mathbin{+\!\!+} \cdots\bigr) \mathbin{+\!\!+} (Z \mathbin{+\!\!+} [p])$（結合律）。
- $Z'$ の先頭条件：$Z = []$ のとき $Z' = [p]$ で $\pi_0(\mathrm{headI}\,Z') = \pi_0 p = 0 \le u$。
  $Z = z \mathbin{::} Z''$ のとき $\mathrm{headI}\,Z' = z = \mathrm{headI}\,Z$ であり、
  与えられた条件 $Z = [] \vee \pi_0(\mathrm{headI}\,Z) \le u$ の第 1 選言は $Z \ne []$ に反するので
  第 2 選言 $\pi_0 z \le u$ が成り立つ。
- 他の 6 条件は $Z$ に言及しないのでそのまま。

結論 $B \preceq_{\mathrm{lex}} \mathrm{sh}_e(A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} A_2))$ は $Z$ を含まないから、
これが求める結論である。∎

### 帰納段のための移送補題

$\mathrm{ArgDomCoreOn}$ は分解の等式を通してしか前部 $X$ に言及しない。したがって実例は
左側に何があるかに依らず、また行 0 の一様シフトと可換である。この 2 つを合わせると、
$M[n] = G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(\mathit{blk},n)$ の第 $0$ コピー $\mathit{blk}$ より右にある実例が、
$M[n-1]$ の実例に帰着する。

<a id="t-argDomCoreOn_drop_left"></a>
### 定理 左側の材料は見えない (T.argDomCoreOn_drop_left)

**主張** $\mathrm{ArgDomCoreOn}(P \mathbin{+\!\!+} S)$ ならば $\mathrm{ArgDomCoreOn}(S)$。

**証明** $S$ の分解 $X, A_1, B, A_2, Z, u, w, e$ と 7 つの側条件を与える。
仮定を $X' := P \mathbin{+\!\!+} X$ と（他は同じデータに）適用する。分解の等式は
$$P \mathbin{+\!\!+} S = P \mathbin{+\!\!+} \Bigl(\bigl(X \mathbin{+\!\!+} \cdots\bigr) \mathbin{+\!\!+} Z\Bigr)
= \Bigl((P \mathbin{+\!\!+} X) \mathbin{+\!\!+} (u,w) \mathbin{::} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} A_2)\bigr)\Bigr) \mathbin{+\!\!+} Z$$
（結合律）。他の側条件は $X$ に言及せず、結論も $X$ に言及しない。∎

<a id="d-shiftl0"></a>
### 定義 行 0 の左シフト (D.shiftl0)

$$\mathrm{sh}^{-}_d X := \mathrm{map}\,\bigl(\lambda p.\ (\pi_0 p - d,\ \pi_1 p)\bigr)\,X$$

（減法は切り捨て減法）。これは $\mathrm{sh}_d$（[(D.shiftr0)](Wf.md#d-shiftr0)）の左逆写像である
（[(T.shiftl0_shiftr0)](#t-shiftl0_shiftr0)）。

<a id="t-shiftl0_cons"></a>
### 定理 $\mathrm{sh}^{-}$ と先頭付加 (T.shiftl0_cons)

**主張** $\mathrm{sh}^{-}_d (p \mathbin{::} A) = (\pi_0 p - d,\ \pi_1 p) \mathbin{::} \mathrm{sh}^{-}_d A$。

**証明** $\mathrm{map}$ の先頭付加についての計算規則そのものであり、両辺は定義により同一である。∎

<a id="t-shiftl0_append"></a>
### 定理 $\mathrm{sh}^{-}$ と連結 (T.shiftl0_append)

**主張** $\mathrm{sh}^{-}_d (A \mathbin{+\!\!+} B) = \mathrm{sh}^{-}_d A \mathbin{+\!\!+} \mathrm{sh}^{-}_d B$。

**証明** `List.map_append` そのものである。∎

<a id="t-mem_shiftl0"></a>
### 定理 $\mathrm{sh}^{-}$ の要素 (T.mem_shiftl0)

**主張** $x \in \mathrm{sh}^{-}_d M \iff \exists p \in M,\ (\pi_0 p - d,\ \pi_1 p) = x$。

**証明** 定義を展開すると $\mathrm{map}$ の要素の特徴づけ（`List.mem_map`）そのものである。∎

<a id="t-shiftl0_shiftr0"></a>
### 定理 左逆 (T.shiftl0_shiftr0)

**主張** $\mathrm{sh}^{-}_d(\mathrm{sh}_d X) = X$。

**証明** $X$ に関するリストの構造帰納法。帰納法の述語は
$\Sigma(X) :\equiv \mathrm{sh}^{-}_d(\mathrm{sh}_d X) = X$。

- 基底段 $X = []$：両辺とも $[]$。
- 帰納段 $X = p \mathbin{::} X'$：帰納法の仮定は $\Sigma(X')$。
  [(T.shiftr0_cons)](Wf.md#t-shiftr0_cons) と [(T.shiftl0_cons)](#t-shiftl0_cons) より
  $$\mathrm{sh}^{-}_d(\mathrm{sh}_d(p \mathbin{::} X'))
  = \bigl((\pi_0 p + d) - d,\ \pi_1 p\bigr) \mathbin{::} \mathrm{sh}^{-}_d(\mathrm{sh}_d X') .$$
  $(\pi_0 p + d) - d = \pi_0 p$（切り捨て減法でも加えてから引くのは元に戻る）であり、
  尾部は $\Sigma(X')$ により $X'$ に等しい。∎

<a id="t-shiftr0_shiftl0"></a>
### 定理 右逆（下界つき） (T.shiftr0_shiftl0)

**主張** $\forall x \in L,\ d \le \pi_0 x$ ならば $\mathrm{sh}_d(\mathrm{sh}^{-}_d L) = L$。

**証明** $L$ に関するリストの構造帰納法。帰納法の述語は
$$\Upsilon(L) :\equiv \bigl(\forall x \in L,\ d \le \pi_0 x\bigr) \to \mathrm{sh}_d(\mathrm{sh}^{-}_d L) = L .$$

- 基底段 $L = []$：両辺とも $[]$。
- 帰納段 $L = p \mathbin{::} L'$：帰納法の仮定は $\Upsilon(L')$。仮定より $d \le \pi_0 p$ であり、
  また $L'$ の各要素は $L$ の要素だから $\Upsilon(L')$ の前提もみたされる。
  [(T.shiftl0_cons)](#t-shiftl0_cons)、[(T.shiftr0_cons)](Wf.md#t-shiftr0_cons) より
  $$\mathrm{sh}_d(\mathrm{sh}^{-}_d(p \mathbin{::} L'))
  = \bigl((\pi_0 p - d) + d,\ \pi_1 p\bigr) \mathbin{::} \mathrm{sh}_d(\mathrm{sh}^{-}_d L')$$
  であり、$d \le \pi_0 p$ より $(\pi_0 p - d) + d = \pi_0 p$、尾部は $\Upsilon(L')$ により $L'$。∎

<a id="t-shiftr0_comm"></a>
### 定理 シフトの可換性 (T.shiftr0_comm)

**主張** $\mathrm{sh}_e(\mathrm{sh}_d L) = \mathrm{sh}_d(\mathrm{sh}_e L)$。

**証明** $\mathrm{map}$ の合成則より、左辺は
$\mathrm{map}\,\bigl(\lambda p.\ ((\pi_0 p + d) + e,\ \pi_1 p)\bigr)\,L$、
右辺は $\mathrm{map}\,\bigl(\lambda p.\ ((\pi_0 p + e) + d,\ \pi_1 p)\bigr)\,L$ である。
$(\pi_0 p + d) + e = (\pi_0 p + e) + d$（加法の結合律と交換律）であるから 2 つの写像は等しく、
したがって像も等しい。∎

<a id="t-argDomCoreOn_shiftr0"></a>
### 定理 実例は一様シフトと可換 (T.argDomCoreOn_shiftr0)

**主張** $\mathrm{ArgDomCoreOn}(W)$ ならば $\mathrm{ArgDomCoreOn}(\mathrm{sh}_d W)$。

**証明** $\mathrm{sh}_d W$ の分解
$$\mathrm{sh}_d W = \Bigl(X \mathbin{+\!\!+} (u,w) \mathbin{::} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} A_2)\bigr)\Bigr) \mathbin{+\!\!+} Z$$
と 7 つの側条件 $h_e, h_1, \dots, h_6$ を与える。

**(1) すべての列の行 0 は $d$ 以上。** 分解の右辺の要素はすべて $\mathrm{sh}_d W$ の要素であり、
[(T.mem_shiftr0)](Wf.md#t-mem_shiftr0) より $(\pi_0 q + d, \pi_1 q)$ の形をもつから行 0 の値は $d$ 以上である。
とくに、$X$、$A_1$、$B$、$A_2$、$Z$ のいずれかに属する任意の $x$ について $d \le \pi_0 x$ であり、
また $d \le u$（列 $(u,w)$ 自身が分解の右辺の要素であることによる）。

**(2) 分解を引き戻す。** $X' := \mathrm{sh}^{-}_d X$、$A_1' := \mathrm{sh}^{-}_d A_1$、$B' := \mathrm{sh}^{-}_d B$、
$A_2' := \mathrm{sh}^{-}_d A_2$、$Z' := \mathrm{sh}^{-}_d Z$ とおく。(1) と
[(T.shiftr0_shiftl0)](#t-shiftr0_shiftl0) より $\mathrm{sh}_d X' = X$、$\mathrm{sh}_d A_1' = A_1$、
$\mathrm{sh}_d B' = B$、$\mathrm{sh}_d A_2' = A_2$、$\mathrm{sh}_d Z' = Z$。
分解の等式の両辺に $\mathrm{sh}^{-}_d$ を施すと、左辺は [(T.shiftl0_shiftr0)](#t-shiftl0_shiftr0) により $W$、
右辺は [(T.shiftl0_append)](#t-shiftl0_append) と [(T.shiftl0_cons)](#t-shiftl0_cons) により分配されて
$$W = \Bigl(X' \mathbin{+\!\!+} (u-d,\ w) \mathbin{::} \bigl(A_1' \mathbin{+\!\!+} ((u-d)+e,\ w) \mathbin{::} (B' \mathbin{+\!\!+} A_2')\bigr)\Bigr) \mathbin{+\!\!+} Z' .$$
ここで深い方の列については $u+e-d = (u-d)+e$ を使った（$d \le u$ による）。

**(3) 側条件の移送。**
- $\forall x \in A_1',\ u-d < \pi_0 x$：$x = (\pi_0 q - d, \pi_1 q)$（$q \in A_1$）と書けて、
  $h_1$ より $u < \pi_0 q$、(1) より $d \le \pi_0 q$、$d \le u$。よって $u - d < \pi_0 q - d$。
- $\forall x \in B',\ (u-d)+e < \pi_0 x$：同様に $u+e < \pi_0 q$、$d \le u$ から
  $(u-d)+e = u+e-d < \pi_0 q - d$。
- $\forall x \in A_2',\ u-d < \pi_0 x$：同様。
- $A_2' = [] \vee \pi_0(\mathrm{headI}\,A_2') \le (u-d)+e$：$A_2 = []$ なら $A_2' = []$。
  $A_2 = a \mathbin{::} A_2''$ なら $h_4$ の第 2 選言より $\pi_0 a \le u+e$、(1) より $d \le \pi_0 a$、
  $\mathrm{headI}\,A_2' = (\pi_0 a - d, \pi_1 a)$ であるから $\pi_0 a - d \le u+e-d = (u-d)+e$。
- $Z' = [] \vee \pi_0(\mathrm{headI}\,Z') \le u-d$：同様に $h_5$ から。
- $\mathrm{SpineOK}(A_1', (u-d)+e, w)$：$A_1' = U' \mathbin{+\!\!+} x' \mathbin{::} V'$、$\pi_0 x' < (u-d)+e$、
  $\forall y \in V',\ \pi_0 x' < \pi_0 y$ を仮定する。両辺に $\mathrm{sh}_d$ を施すと
  $$A_1 = \mathrm{sh}_d A_1' = \mathrm{sh}_d U' \mathbin{+\!\!+} (\pi_0 x' + d,\ \pi_1 x') \mathbin{::} \mathrm{sh}_d V'$$
  である。$h_6 = \mathrm{SpineOK}(A_1, u+e, w)$ を
  $U := \mathrm{sh}_d U'$、$V := \mathrm{sh}_d V'$、$x := (\pi_0 x' + d, \pi_1 x')$ に適用する。
  行 0 の条件は $\pi_0 x' + d < u+e$（$\pi_0 x' < (u-d)+e = u+e-d$ と $d \le u$ から）、
  右から見える条件は、$\mathrm{sh}_d V'$ の要素 $(\pi_0 q + d, \pi_1 q)$（$q \in V'$）について
  $\pi_0 x' < \pi_0 q$ から $\pi_0 x' + d < \pi_0 q + d$。
  結論は $w \le \pi_1 (\pi_0 x' + d, \pi_1 x') = \pi_1 x'$ であり、これが求めるものである。

**(4) 適用と結論の戻し。** $\mathrm{ArgDomCoreOn}(W)$ を (2) の分解と (3) の側条件に適用して
$$B' \preceq_{\mathrm{lex}} \mathrm{sh}_e\bigl(A_1' \mathbin{+\!\!+} ((u-d)+e, w) \mathbin{::} (B' \mathbin{+\!\!+} A_2')\bigr) .$$
一方、[(T.shiftr0_comm)](#t-shiftr0_comm) と (2) の等式から
$$\mathrm{sh}_e\bigl(A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} A_2)\bigr)
= \mathrm{sh}_d\Bigl(\mathrm{sh}_e\bigl(A_1' \mathbin{+\!\!+} ((u-d)+e,w) \mathbin{::} (B' \mathbin{+\!\!+} A_2')\bigr)\Bigr)$$
である（各成分に $\mathrm{sh}_d A_1' = A_1$ 等を使い、印付き列については
$((u-d)+e) + d = u+e$ を使った）。$B = \mathrm{sh}_d B'$ でもあるから、
[(T.sle_shiftr0)](#t-sle_shiftr0) の $(\Leftarrow)$ 方向を上の結論に適用すれば目標を得る。∎

### コピー塔のための位置計算

<a id="t-split_prefix_left"></a>
### 定理 短い左因子での分割 (T.split_prefix_left)

**主張** $C \mathbin{+\!\!+} D = E \mathbin{+\!\!+} F$ かつ $\lvert E\rvert \le \lvert C\rvert$ ならば
$$C = E \mathbin{+\!\!+} \mathrm{drop}\,\lvert E\rvert\,C \quad\wedge\quad
F = \mathrm{drop}\,\lvert E\rvert\,C \mathbin{+\!\!+} D .$$

**証明** $C = \mathrm{take}\,\lvert E\rvert\,C \mathbin{+\!\!+} \mathrm{drop}\,\lvert E\rvert\,C$
（`List.take_append_drop`）を仮定の左辺に代入し、結合律で括り直すと
$$\bigl(\mathrm{take}\,\lvert E\rvert\,C\bigr) \mathbin{+\!\!+} \bigl(\mathrm{drop}\,\lvert E\rvert\,C \mathbin{+\!\!+} D\bigr)
= E \mathbin{+\!\!+} F .$$
$\lvert \mathrm{take}\,\lvert E\rvert\,C\rvert = \min(\lvert E\rvert, \lvert C\rvert) = \lvert E\rvert$
（$\lvert E\rvert \le \lvert C\rvert$ による）であるから `List.append_inj` が使えて
$\mathrm{take}\,\lvert E\rvert\,C = E$ かつ $\mathrm{drop}\,\lvert E\rvert\,C \mathbin{+\!\!+} D = F$。
前者を上の分解に戻すと $C = E \mathbin{+\!\!+} \mathrm{drop}\,\lvert E\rvert\,C$。∎

<a id="t-split_prefix_right"></a>
### 定理 長い左因子での分割 (T.split_prefix_right)

**主張** $C \mathbin{+\!\!+} D = E \mathbin{+\!\!+} F$ かつ $\lvert C\rvert \le \lvert E\rvert$ ならば
$$E = C \mathbin{+\!\!+} \mathrm{drop}\,\lvert C\rvert\,E \quad\wedge\quad
D = \mathrm{drop}\,\lvert C\rvert\,E \mathbin{+\!\!+} F .$$

**証明** 仮定の等式を左右反転して $E \mathbin{+\!\!+} F = C \mathbin{+\!\!+} D$ とし、
[(T.split_prefix_left)](#t-split_prefix_left) を（$C := E$、$D := F$、$E := C$、$F := D$ として）適用する。∎

<a id="t-copies_headI"></a>
### 定理 コピー塔の先頭 (T.copies_headI)

**主張** $\mathit{blk} \ne []$ かつ $1 \le n$ ならば
$\mathrm{headI}\,\mathrm{cp}_d(\mathit{blk},n) = \mathrm{headI}\,\mathit{blk}$。

**証明** $n = m+1$ と書く。[(T.copies_succ_front)](Wf.md#t-copies_succ_front) より
$\mathrm{cp}_d(\mathit{blk},m+1) = \mathit{blk} \mathbin{+\!\!+} \mathrm{sh}_d(\mathrm{cp}_d(\mathit{blk},m))$。
$\mathit{blk} = b \mathbin{::} \mathit{blk}'$ と書けるから、この列の先頭は $b = \mathrm{headI}\,\mathit{blk}$ である。∎

<a id="t-argbound_split"></a>
### 定理 上界の分割 (T.argbound_split)

**主張**
$$\mathrm{sh}_e\bigl(A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} A_2)\bigr)
= \bigl(\mathrm{sh}_e A_1 \mathbin{+\!\!+} (u+e+e,\ w) \mathbin{::} \mathrm{sh}_e B\bigr) \mathbin{+\!\!+} \mathrm{sh}_e A_2 .$$

**証明** [(T.shiftr0_append)](Cofinality.md#t-shiftr0_append) と [(T.shiftr0_cons)](Wf.md#t-shiftr0_cons) より
左辺は $\mathrm{sh}_e A_1 \mathbin{+\!\!+} (u+e+e,w) \mathbin{::} (\mathrm{sh}_e B \mathbin{+\!\!+} \mathrm{sh}_e A_2)$ に等しく、
これを結合律で括り直したものが右辺である。∎

<a id="t-argbound_len"></a>
### 定理 上界の前半は $B$ より長い (T.argbound_len)

**主張** $\lvert B\rvert < \bigl\lvert \mathrm{sh}_e A_1 \mathbin{+\!\!+} (u+e+e,w) \mathbin{::} \mathrm{sh}_e B\bigr\rvert$。

**証明** [(T.shiftr0_length)](Cofinality.md#t-shiftr0_length) より
$\lvert \mathrm{sh}_e A_1\rvert = \lvert A_1\rvert$、$\lvert \mathrm{sh}_e B\rvert = \lvert B\rvert$ であるから、
右辺は $\lvert A_1\rvert + 1 + \lvert B\rvert$ であり、これは $\lvert B\rvert$ より真に大きい。∎

### bad 枝 — 3 つの場合への分割

以下 3 つの定理は、導出帰納の `oper` 段のうち [(D.oper)](Def.md#d-oper) の分岐 (d)（`bad` 枝）を扱う。
共通の設定は次の通りである。[(T.oper_bad_blocks_all)](Cofinality.md#t-oper_bad_blocks_all) が与える分解
$$M = G \mathbin{+\!\!+} \mathit{blk} \mathbin{+\!\!+} [\mathit{lp}], \qquad \mathit{blk} := (v_0,w_0) \mathbin{::} R$$
に対し、展開列は
$$N := G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(\mathit{blk},\ n) \qquad (= M[n],\ n \ge 1)$$
である。コピー塔の第 $0$ コピーは $\mathit{blk}$ そのものであるから、$M$ と $N$ が一致する部分は
$M$ の先頭 $\lvert M\rvert - 1$ 個であり、その右端は
$$p := \lvert G\rvert + \lvert \mathit{blk}\rvert = \lvert G\rvert + (\lvert R\rvert + 1)$$
である（$\lvert G\rvert$ ではない）。$\mathrm{ArgDomCoreOn}(N)$ の実例の 2 つの印付き列の位置は
[(T.argdom_pos)](#t-argdom_pos) により $i = \lvert X\rvert$ と $j = \lvert X\rvert + (\lvert A_1\rvert+1)$ で、
つねに $i < j$ である。場合分けは $i, j$ と $p$ の位置関係で行う。

| 名前 | 判別条件 | 位置の読み |
|---|---|---|
| **B** | $\lvert X\rvert + (\lvert A_1\rvert+1) < \lvert G\rvert + (\lvert R\rvert+1)$ | $j < p$ |
| **A2** | $\lvert X\rvert < \lvert G\rvert + (\lvert R\rvert+1)$ かつ $\lvert G\rvert + (\lvert R\rvert+1) \le \lvert X\rvert + (\lvert A_1\rvert+1)$ | $i < p \le j$ |
| **A1** | $\lvert G\rvert + (\lvert R\rvert+1) \le \lvert X\rvert$ | $p \le i$ |

**網羅性.** この 3 つは互いに排反で、すべての実例を尽くす。実際、自然数の 2 分律を 2 回使うだけでよい。
$j < p$ でなければ $p \le j$ であり、そのとき $i < p$（場合 A2）か $p \le i$（場合 A1）のいずれかである。
$i$ と $j$ の関係は一切使わないので、実例を取りこぼすことはない。この振り分けを行うのが
[(T.argDomCoreOn_bad)](#t-argDomCoreOn_bad) である。

3 つの定理はいずれも文脈を全部書き下しており、単独で読める形になっている。文脈に含まれるのは
宿主の標準形性 $h_M$ とその実例 $h_{Mon}$、分解の組
（$h_{Meq}, h_{Rgt}, h_{lp}, h_{disj}$。$h_{disj}$ が [(D.nextrel1)](Def.md#d-nextrel1) の条項を運ぶ）、
塔自身の標準形性 $h_{STn}$、コピー数についての強帰納法の仮定 $h_{IH}$、$1 \le n$、
実例のデータと 7 つの側条件、そして各場合の判別条件である。各定理はこれらの一部しか使わない。

<a id="t-argDomCoreOn_bad_A1"></a>
### 定理 場合 A1：両方の印付き列が第 0 コピーより右 (T.argDomCoreOn_bad_A1)

**主張** $M, G, R \in \mathrm{PairSeq}$、$v_0,w_0,d_0,n \in \mathbb{N}$、$\mathit{lp} \in \mathbb{N}\times\mathbb{N}$ が
- $h_M$：$M \in \mathrm{ST\_PS}$、$h_{Mon}$：$\mathrm{ArgDomCoreOn}(M)$
- $h_{Meq}$：$M = G \mathbin{+\!\!+} ((v_0,w_0) \mathbin{::} R) \mathbin{+\!\!+} [\mathit{lp}]$
- $h_{Rgt}$：$\forall x \in R,\ v_0 < \pi_0 x$、$h_{lp}$：$v_0 < \pi_0 \mathit{lp}$
- $h_{disj}$：$\bigl(d_0 = 0 \wedge \pi_1 \mathit{lp} = 0 \wedge \pi_0 \mathit{lp} = v_0+1\bigr)$ または
  $\bigl(0 < d_0 \wedge \pi_1 \mathit{lp} = w_0+1 \wedge \pi_0 \mathit{lp} = v_0+d_0 \wedge
  \lvert G\rvert \to^M_1 (\lvert M\rvert - 1)\bigr)$
- $h_{STn}$：$\forall m \ge 1,\ G \mathbin{+\!\!+} \mathrm{cp}_{d_0}((v_0,w_0) \mathbin{::} R,\ m) \in \mathrm{ST\_PS}$
- $h_{IH}$：$\forall m,\ 1 \le m < n \to \mathrm{ArgDomCoreOn}\bigl(G \mathbin{+\!\!+} \mathrm{cp}_{d_0}((v_0,w_0)\mathbin{::}R,\ m)\bigr)$
- $h_n$：$1 \le n$

をみたすとする。さらに $G \mathbin{+\!\!+} \mathrm{cp}_{d_0}((v_0,w_0)\mathbin{::}R,\ n)$ の分解
$X, A_1, B, A_2, Z, u, w, e$ と 7 つの側条件、および判別条件
$$h_{case} : \lvert G\rvert + (\lvert R\rvert+1) \le \lvert X\rvert$$
が与えられたとする。このとき
$B \preceq_{\mathrm{lex}} \mathrm{sh}_e\bigl(A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} A_2)\bigr)$。

**証明** $\mathit{blk} := (v_0,w_0) \mathbin{::} R$、$P := G \mathbin{+\!\!+} \mathit{blk}$ とおく。$\lvert P\rvert = \lvert G\rvert + (\lvert R\rvert+1) = p$ である。
$h_n$ より $n = m+1$ と書ける。

**第 0 コピーを剥がす。** [(T.copies_succ_front)](Wf.md#t-copies_succ_front) より
$$G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(\mathit{blk},\ m+1) = P \mathbin{+\!\!+} \mathrm{sh}_{d_0}\bigl(\mathrm{cp}_{d_0}(\mathit{blk},\ m)\bigr)$$
であり、分解の等式を結合律で括り直すと
$$P \mathbin{+\!\!+} \mathrm{sh}_{d_0}\bigl(\mathrm{cp}_{d_0}(\mathit{blk},m)\bigr)
= X \mathbin{+\!\!+} \Bigl(\bigl((u,w) \mathbin{::} (A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} A_2))\bigr) \mathbin{+\!\!+} Z\Bigr) .$$
$h_{case}$ は $\lvert P\rvert \le \lvert X\rvert$ であるから
[(T.split_prefix_right)](#t-split_prefix_right) が使えて、$X = P \mathbin{+\!\!+} \mathrm{drop}\,\lvert P\rvert\,X$ かつ
$$\mathrm{sh}_{d_0}\bigl(\mathrm{cp}_{d_0}(\mathit{blk},m)\bigr)
= \Bigl(\mathrm{drop}\,\lvert P\rvert\,X \mathbin{+\!\!+} (u,w) \mathbin{::} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} A_2)\bigr)\Bigr) \mathbin{+\!\!+} Z .$$
すなわち実例が**そのままの側条件のまま**、塔の尾部 $\mathrm{sh}_{d_0}(\mathrm{cp}_{d_0}(\mathit{blk},m))$ の中に再現された
（7 つの側条件は $X$ に言及しないので変わらない）。

**$m = 0$ の場合。** [(T.copies_zero)](Wf.md#t-copies_zero) と
[(T.shiftr0_nil)](Wf.md#t-shiftr0_nil) より左辺は $[]$ である。しかし右辺は列 $(u,w)$ を含むので長さが $1$ 以上であり、
長さを比べて矛盾する。これは「$n = 1$ のとき塔の長さはちょうど $p$ であるのに
$p \le i < j < \lvert N\rvert = p$ が要求される」という空虚性の内容である。

**$m \ge 1$ の場合。** $h_{IH}$ を $m$（$1 \le m < m+1 = n$）に適用して
$\mathrm{ArgDomCoreOn}\bigl(G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(\mathit{blk},m)\bigr)$ を得る。
[(T.argDomCoreOn_drop_left)](#t-argDomCoreOn_drop_left)（$P := G$）で $G$ を落とし、
[(T.argDomCoreOn_shiftr0)](#t-argDomCoreOn_shiftr0)（$d := d_0$）でシフトを付け直すと
$\mathrm{ArgDomCoreOn}\bigl(\mathrm{sh}_{d_0}(\mathrm{cp}_{d_0}(\mathit{blk},m))\bigr)$。
これを上で再現した分解と 7 つの側条件に適用すれば、結論がそのまま得られる。∎

この場合に使うのは $h_{IH}$ だけであり、$h_M, h_{Mon}, h_{Meq}, h_{Rgt}, h_{lp}, h_{disj}, h_{STn}$ は使わない。
また、2 つの印付き列が $\mathit{blk}$ の**同じ**列のコピーであることは一切使っていない
（$\mathit{blk}$ が同じ行 1 の値をもつ相異なる列を 2 つ含む場合も、この議論はそのまま通る）。

<a id="t-arg_split"></a>
### 定理 水準による分割 (T.arg_split)

**主張** $L \in \mathbb{N}$ とする。任意の $E \in \mathrm{PairSeq}$ に対し $B_p, R_p \in \mathrm{PairSeq}$ が存在して
$$E = B_p \mathbin{+\!\!+} R_p, \qquad \forall x \in B_p,\ L < \pi_0 x, \qquad
R_p = [] \ \vee\ \pi_0(\mathrm{headI}\,R_p) \le L .$$

**証明** $E$ に関するリストの構造帰納法。帰納法の述語は
$$\Pi(E) :\equiv \exists B_p, R_p,\ \bigl(E = B_p \mathbin{+\!\!+} R_p \wedge (\forall x \in B_p,\ L < \pi_0 x)
 \wedge (R_p = [] \vee \pi_0(\mathrm{headI}\,R_p) \le L)\bigr) .$$

- 基底段 $E = []$：$B_p := []$、$R_p := []$ と取る。3 条件はいずれも成り立つ
  （$\forall x \in [],\ \cdots$ は空虚に真、$R_p = []$）。
- 帰納段 $E = a \mathbin{::} E'$：帰納法の仮定は $\Pi(E')$ である。$L < \pi_0 a$ か否かで場合分けする。
  - $L < \pi_0 a$ のとき：$\Pi(E')$ の与える $B_p, R_p$ に対し $(a \mathbin{::} B_p,\ R_p)$ と取る。
    $a \mathbin{::} E' = a \mathbin{::} (B_p \mathbin{+\!\!+} R_p) = (a \mathbin{::} B_p) \mathbin{+\!\!+} R_p$ であり、
    $a \mathbin{::} B_p$ の要素は $a$ か $B_p$ の要素であって、いずれも行 0 が $L$ より大きい。
    第 3 条件は $\Pi(E')$ のものをそのまま使う。
  - $\neg(L < \pi_0 a)$ のとき：$([],\ a \mathbin{::} E')$ と取る。第 1 条件は
    $a \mathbin{::} E' = [] \mathbin{+\!\!+} (a \mathbin{::} E')$、第 2 条件は $\forall x \in [],\ \cdots$ が空虚に真であること、
    第 3 条件は $\mathrm{headI}(a \mathbin{::} E') = a$ と $\pi_0 a \le L$ による。∎

<a id="t-seqlex_of_sle_snoc'"></a>
### 定理 落とされる列の差し替え（上界相対形） (T.seqlex_of_sle_snoc')

**主張** $X, V, E \in \mathrm{PairSeq}$、$\mathit{lp}, q \in \mathbb{N}\times\mathbb{N}$ とする。
$$X \mathbin{+\!\!+} [\mathit{lp}] \preceq_{\mathrm{lex}} V \mathbin{+\!\!+} E \quad\wedge\quad q \prec_{\mathrm{c}} \mathit{lp}
\quad\wedge\quad \lvert X\rvert < \lvert V\rvert
\ \Longrightarrow\ \forall S', E',\ X \mathbin{+\!\!+} q \mathbin{::} S' \prec_{\mathrm{lex}} V \mathbin{+\!\!+} E' .$$

[(T.seqlex_of_sle_snoc)](#t-seqlex_of_sle_snoc) の強化である（$E := []$ が元の形）。
仮定は $V$ の**ある**継続についての上界でよく、結論は $V$ の**任意の**継続について成り立つ。

**証明** $X$ に関するリストの構造帰納法。帰納法の述語は
$$\Theta'(X) :\equiv \forall V, E, \mathit{lp}, q,\
X \mathbin{+\!\!+} [\mathit{lp}] \preceq_{\mathrm{lex}} V \mathbin{+\!\!+} E \to q \prec_{\mathrm{c}} \mathit{lp} \to \lvert X\rvert < \lvert V\rvert \to
\forall S', E',\ X \mathbin{+\!\!+} q \mathbin{::} S' \prec_{\mathrm{lex}} V \mathbin{+\!\!+} E' .$$

- 基底段 $X = []$：$0 < \lvert V\rvert$ より $V = v \mathbin{::} V'$。
  目標 $q \mathbin{::} S' \prec_{\mathrm{lex}} v \mathbin{::} (V' \mathbin{+\!\!+} E')$ には $q \prec_{\mathrm{c}} v$ を示せば十分。
  仮定 $[\mathit{lp}] \preceq_{\mathrm{lex}} v \mathbin{::} (V' \mathbin{+\!\!+} E)$ の 2 選言で場合分けする。
  - 等号のとき：先頭を比べて $\mathit{lp} = v$、よって $q \prec_{\mathrm{c}} v$。
  - $\prec_{\mathrm{lex}}$ のとき：$\mathit{lp} \prec_{\mathrm{c}} v$ ならば
    [(T.pairlt_trans)](Cofinality.md#t-pairlt_trans) で $q \prec_{\mathrm{c}} v$、
    $\mathit{lp} = v$ ならば直ちに $q \prec_{\mathrm{c}} v$。
- 帰納段 $X = x \mathbin{::} X'$：帰納法の仮定は $\Theta'(X')$。$\lvert X\rvert < \lvert V\rvert$ より
  $V = v \mathbin{::} V'$ で $\lvert X'\rvert < \lvert V'\rvert$。
  仮定は $x \mathbin{::} (X' \mathbin{+\!\!+} [\mathit{lp}]) \preceq_{\mathrm{lex}} v \mathbin{::} (V' \mathbin{+\!\!+} E)$、
  目標は $x \mathbin{::} (X' \mathbin{+\!\!+} q \mathbin{::} S') \prec_{\mathrm{lex}} v \mathbin{::} (V' \mathbin{+\!\!+} E')$。
  - 等号のとき：$x = v$ かつ $X' \mathbin{+\!\!+} [\mathit{lp}] = V' \mathbin{+\!\!+} E$。後者は $\preceq_{\mathrm{lex}}$ の
    第 1 選言を与えるから $\Theta'(X')$ が使えて $X' \mathbin{+\!\!+} q \mathbin{::} S' \prec_{\mathrm{lex}} V' \mathbin{+\!\!+} E'$、
    目標の第 2 選言。
  - $\prec_{\mathrm{lex}}$ のとき：$x \prec_{\mathrm{c}} v$ ならば目標の第 1 選言。
    $x = v$ かつ $X' \mathbin{+\!\!+} [\mathit{lp}] \prec_{\mathrm{lex}} V' \mathbin{+\!\!+} E$ ならば $\Theta'(X')$ を適用して目標の第 2 選言。∎

<a id="t-argDomCoreOn_bad_B"></a>
### 定理 場合 B：両方の印付き列が $G \mathbin{+\!\!+} \mathit{blk}$ の内部 (T.argDomCoreOn_bad_B)

**主張** [(T.argDomCoreOn_bad_A1)](#t-argDomCoreOn_bad_A1) と同じ文脈
（$h_M, h_{Mon}, h_{Meq}, h_{Rgt}, h_{lp}, h_{disj}, h_{STn}, h_{IH}, h_n$ と実例のデータ・7 側条件）のもとで、
判別条件が
$$h_{case} : \lvert X\rvert + (\lvert A_1\rvert+1) < \lvert G\rvert + (\lvert R\rvert+1)$$
であるとする。このとき
$B \preceq_{\mathrm{lex}} \mathrm{sh}_e\bigl(A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} A_2)\bigr)$。

**証明** $\mathit{blk} := (v_0,w_0) \mathbin{::} R$、$P := G \mathbin{+\!\!+} \mathit{blk}$ とおき、$h_n$ より $n = m+1$ と書く。

**共有部分の切り出し。** [(T.copies_succ_front)](Wf.md#t-copies_succ_front) より
$G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(\mathit{blk},m+1) = P \mathbin{+\!\!+} \mathrm{sh}_{d_0}(\mathrm{cp}_{d_0}(\mathit{blk},m))$ である。
$$C_p := X \mathbin{+\!\!+} (u,w) \mathbin{::} \bigl(A_1 \mathbin{+\!\!+} [(u+e,w)]\bigr)$$
とおくと、分解の等式は結合律により
$$P \mathbin{+\!\!+} \mathrm{sh}_{d_0}\bigl(\mathrm{cp}_{d_0}(\mathit{blk},m)\bigr) = C_p \mathbin{+\!\!+} \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr)$$
と書ける。$\lvert C_p\rvert = \lvert X\rvert + 1 + \lvert A_1\rvert + 1 = j+1 \le p = \lvert P\rvert$
（$h_{case}$ は $j < p$）であるから [(T.split_prefix_left)](#t-split_prefix_left) が使えて、$D$ が存在して
$$P = C_p \mathbin{+\!\!+} D, \qquad
B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z) = D \mathbin{+\!\!+} \mathrm{sh}_{d_0}\bigl(\mathrm{cp}_{d_0}(\mathit{blk},m)\bigr) .$$
同じ座標で宿主を書くと、$h_{Meq}$ より
$$M = P \mathbin{+\!\!+} [\mathit{lp}] = C_p \mathbin{+\!\!+} \bigl(D \mathbin{+\!\!+} [\mathit{lp}]\bigr) .$$
すなわち、2 つの印付き列と $A_1$ 全体は宿主 $M$ の中にもそのままの位置で現れる。

**宿主の判定（key）.** 次を示す。任意の $B', A_2', Z'$ について、
$$D \mathbin{+\!\!+} [\mathit{lp}] = B' \mathbin{+\!\!+} (A_2' \mathbin{+\!\!+} Z'),\quad
\forall x \in B',\ u+e < \pi_0 x,\quad \forall x \in A_2',\ u < \pi_0 x,$$
$$A_2' = [] \vee \pi_0(\mathrm{headI}\,A_2') \le u+e, \quad Z' = [] \vee \pi_0(\mathrm{headI}\,Z') \le u$$
が成り立つならば
$$B' \preceq_{\mathrm{lex}} \mathrm{sh}_e A_1 \mathbin{+\!\!+} (u+e+e,\ w) \mathbin{::} \mathrm{sh}_e B' . \tag{key}$$
実際、上の分解と $M = C_p \mathbin{+\!\!+} (D \mathbin{+\!\!+} [\mathit{lp}])$ から
$$M = \Bigl(X \mathbin{+\!\!+} (u,w) \mathbin{::} \bigl(A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B' \mathbin{+\!\!+} A_2')\bigr)\Bigr) \mathbin{+\!\!+} Z'$$
であり、$h_{Mon} = \mathrm{ArgDomCoreOn}(M)$ をこれに適用できる。側条件のうち $0 < e$、
$\forall x \in A_1,\ u < \pi_0 x$、$\mathrm{SpineOK}(A_1,u+e,w)$ は実例のもの（$A_1, u, w, e$ は共通）をそのまま使い、
残りは仮定である。結論
$B' \preceq_{\mathrm{lex}} \mathrm{sh}_e\bigl(A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B' \mathbin{+\!\!+} A_2')\bigr)$ を
[(T.argbound_split)](#t-argbound_split) で
$\bigl(\mathrm{sh}_e A_1 \mathbin{+\!\!+} (u+e+e,w) \mathbin{::} \mathrm{sh}_e B'\bigr) \mathbin{+\!\!+} \mathrm{sh}_e A_2'$ と書き直し、
[(T.argbound_len)](#t-argbound_len) の与える長さの評価
$\lvert B'\rvert \le \lvert \mathrm{sh}_e A_1 \mathbin{+\!\!+} (u+e+e,w) \mathbin{::} \mathrm{sh}_e B'\rvert$ のもとで
[(T.sle_take_of_short)](#t-sle_take_of_short) を適用すれば (key) を得る。

**目標の同じ形への書き換え（goal_of）.** 逆に
$B \preceq_{\mathrm{lex}} \mathrm{sh}_e A_1 \mathbin{+\!\!+} (u+e+e,w) \mathbin{::} \mathrm{sh}_e B$ が示せれば、
[(T.argbound_split)](#t-argbound_split) で目標の右辺を
$\bigl(\mathrm{sh}_e A_1 \mathbin{+\!\!+} (u+e+e,w) \mathbin{::} \mathrm{sh}_e B\bigr) \mathbin{+\!\!+} \mathrm{sh}_e A_2$ と書き、
[(T.sle_append_mono)](Cofinality.md#t-sle_append_mono) を適用して目標が得られる。
以下、この形の主張を示す。$\lvert B\rvert$ と $\lvert D\rvert$ の 2 分律で場合分けする。

**(a) $\lvert B\rvert < \lvert D\rvert$ のとき。** [(T.split_prefix_right)](#t-split_prefix_right) を
$B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z) = D \mathbin{+\!\!+} \mathrm{sh}_{d_0}(\mathrm{cp}_{d_0}(\mathit{blk},m))$ に適用して $D_r$ を得る：
$$D = B \mathbin{+\!\!+} D_r, \qquad A_2 \mathbin{+\!\!+} Z = D_r \mathbin{+\!\!+} \mathrm{sh}_{d_0}\bigl(\mathrm{cp}_{d_0}(\mathit{blk},m)\bigr) .$$
$D_r = []$ とすると $D = B$ となり $\lvert B\rvert < \lvert D\rvert$ に反するから $D_r \ne []$、
したがって $A_2 \mathbin{+\!\!+} Z \ne []$ であり
[(T.headI_append_left)](Seqlex.md#t-headI_append_left) より
$\mathrm{headI}(A_2 \mathbin{+\!\!+} Z) = \mathrm{headI}\,D_r$。
ここで $\pi_0(\mathrm{headI}\,D_r) \le u+e$ である。実際、$A_2 = []$ ならば $Z \ne []$ かつ
$\mathrm{headI}(A_2 \mathbin{+\!\!+} Z) = \mathrm{headI}\,Z$ であり、側条件より $\pi_0(\mathrm{headI}\,Z) \le u \le u+e$。
$A_2 \ne []$ ならば $\mathrm{headI}(A_2 \mathbin{+\!\!+} Z) = \mathrm{headI}\,A_2$ であり、側条件より
$\pi_0(\mathrm{headI}\,A_2) \le u+e$。

[(T.arg_split)](#t-arg_split) を $L := u$、$E := D_r \mathbin{+\!\!+} [\mathit{lp}]$ に適用して $A_2', Z'$ を得る：
$D_r \mathbin{+\!\!+} [\mathit{lp}] = A_2' \mathbin{+\!\!+} Z'$、$\forall x \in A_2',\ u < \pi_0 x$、
$Z' = [] \vee \pi_0(\mathrm{headI}\,Z') \le u$。さらに
$A_2' = [] \vee \pi_0(\mathrm{headI}\,A_2') \le u+e$ も成り立つ：$A_2' \ne []$ ならば
$\mathrm{headI}\,A_2' = \mathrm{headI}(D_r \mathbin{+\!\!+} [\mathit{lp}]) = \mathrm{headI}\,D_r$ であり、上の評価が使える。
最後に $D \mathbin{+\!\!+} [\mathit{lp}] = (B \mathbin{+\!\!+} D_r) \mathbin{+\!\!+} [\mathit{lp}] = B \mathbin{+\!\!+} (A_2' \mathbin{+\!\!+} Z')$ であるから、
(key) を $B' := B$（側条件は実例の $\forall x \in B,\ u+e < \pi_0 x$）に適用でき、goal_of で終わる。

**(b) $\lvert D\rvert \le \lvert B\rvert$ のとき。** [(T.split_prefix_left)](#t-split_prefix_left) より $B_2$ が存在して
$$B = D \mathbin{+\!\!+} B_2, \qquad \mathrm{sh}_{d_0}\bigl(\mathrm{cp}_{d_0}(\mathit{blk},m)\bigr) = B_2 \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z) .$$
$D \subseteq B$ であるから $\forall x \in D,\ u+e < \pi_0 x$。

*次のコピーの根.* $B_2 = q \mathbin{::} B_2'$ と書けるならば $q = (v_0+d_0,\ w_0)$ である。実際、$m = 0$ なら
$\mathrm{sh}_{d_0}(\mathrm{cp}_{d_0}(\mathit{blk},0)) = []$ となって $B_2 \ne []$ に反するから $m = m'+1$ であり、
[(T.copies_succ_front)](Wf.md#t-copies_succ_front) と [(T.shiftr0_cons)](Wf.md#t-shiftr0_cons) より
$\mathrm{sh}_{d_0}(\mathrm{cp}_{d_0}(\mathit{blk},m'+1))$ の先頭は $(v_0+d_0, w_0)$ である。
一方それは $q$ でもあるから $q = (v_0+d_0,w_0)$。
このとき $h_{disj}$ の 2 つの選言のいずれでも
$$\pi_0 q \le \pi_0 \mathit{lp} \qquad\text{かつ}\qquad q \prec_{\mathrm{c}} \mathit{lp}$$
が成り立つ。実際、第 1 選言（$d_0 = 0$、$\pi_1\mathit{lp} = 0$、$\pi_0\mathit{lp} = v_0+1$）では
$q = (v_0, w_0)$ で $v_0 < v_0+1$ だから $\pi_0 q < \pi_0 \mathit{lp}$（$\prec_{\mathrm{c}}$ の第 1 選言）。
第 2 選言（$0 < d_0$、$\pi_1\mathit{lp} = w_0+1$、$\pi_0\mathit{lp} = v_0+d_0$）では
$\pi_0 q = v_0+d_0 = \pi_0\mathit{lp}$ かつ $\pi_1 q = w_0 < w_0+1 = \pi_1\mathit{lp}$（$\prec_{\mathrm{c}}$ の第 2 選言）。

さらに $u+e < \pi_0\mathit{lp}$ か否かで場合分けする。

**(b-1) $u+e < \pi_0 \mathit{lp}$ のとき。** $\forall x \in D \mathbin{+\!\!+} [\mathit{lp}],\ u+e < \pi_0 x$ が成り立つ
（$D$ の要素は上で、$\mathit{lp}$ はいまの仮定で）。(key) を
$B' := D \mathbin{+\!\!+} [\mathit{lp}]$、$A_2' := []$、$Z' := []$ に適用すると
$$D \mathbin{+\!\!+} [\mathit{lp}] \preceq_{\mathrm{lex}} \mathrm{sh}_e A_1 \mathbin{+\!\!+} (u+e+e,w) \mathbin{::} \mathrm{sh}_e(D \mathbin{+\!\!+} [\mathit{lp}])$$
であり、[(T.shiftr0_append)](Cofinality.md#t-shiftr0_append) と結合律で右辺を
$V_b \mathbin{+\!\!+} \mathrm{sh}_e[\mathit{lp}]$、$V_b := \mathrm{sh}_e A_1 \mathbin{+\!\!+} (u+e+e,w) \mathbin{::} \mathrm{sh}_e D$ と書き直す。
- $B_2 = []$ のとき：$B = D$ であり、目標は $D \preceq_{\mathrm{lex}} V_b$ である。
  [(T.sle_of_append_left)](#t-sle_of_append_left) で小さい側の $[\mathit{lp}]$ を落として
  $D \preceq_{\mathrm{lex}} V_b \mathbin{+\!\!+} \mathrm{sh}_e[\mathit{lp}]$、
  $\lvert D\rvert \le \lvert V_b\rvert = \lvert A_1\rvert + 1 + \lvert D\rvert$ のもとで
  [(T.sle_take_of_short)](#t-sle_take_of_short) を適用すればよい。
- $B_2 = q \mathbin{::} B_2'$ のとき：$B = D \mathbin{+\!\!+} q \mathbin{::} B_2'$ であり、
  [(T.shiftr0_append)](Cofinality.md#t-shiftr0_append) と [(T.shiftr0_cons)](Wf.md#t-shiftr0_cons) より
  $$\mathrm{sh}_e A_1 \mathbin{+\!\!+} (u+e+e,w) \mathbin{::} \mathrm{sh}_e B
  = V_b \mathbin{+\!\!+} (\pi_0 q + e,\ \pi_1 q) \mathbin{::} \mathrm{sh}_e B_2' .$$
  [(T.seqlex_of_sle_snoc')](#t-seqlex_of_sle_snoc') を
  $X := D$、$V := V_b$、$E := \mathrm{sh}_e[\mathit{lp}]$、$q := q$、$S' := B_2'$、
  $E' := (\pi_0 q + e, \pi_1 q) \mathbin{::} \mathrm{sh}_e B_2'$ として適用する。前提は上の $\preceq_{\mathrm{lex}}$、
  $q \prec_{\mathrm{c}} \mathit{lp}$、$\lvert D\rvert < \lvert V_b\rvert$ である。結論がそのまま目標
  （$\prec_{\mathrm{lex}}$ なので $\preceq_{\mathrm{lex}}$ の第 2 選言）である。

**(b-2) $\pi_0 \mathit{lp} \le u+e$ のとき。** このとき $B_2 = []$ である。実際 $B_2 = q \mathbin{::} B_2'$ ならば
$q \in B$ より $u+e < \pi_0 q$、他方 $\pi_0 q \le \pi_0\mathit{lp} \le u+e$ となって矛盾する。
よって $B = D$。$u < \pi_0\mathit{lp}$ か否かでさらに分ける。
- $u < \pi_0 \mathit{lp}$：(key) を $B' := B$、$A_2' := [\mathit{lp}]$、$Z' := []$ に適用する。
  $D \mathbin{+\!\!+} [\mathit{lp}] = B \mathbin{+\!\!+} ([\mathit{lp}] \mathbin{+\!\!+} [])$、
  $\forall x \in [\mathit{lp}],\ u < \pi_0 x$（いまの仮定）、
  $\pi_0(\mathrm{headI}[\mathit{lp}]) = \pi_0\mathit{lp} \le u+e$（(b-2) の仮定）である。
- $\pi_0 \mathit{lp} \le u$：(key) を $B' := B$、$A_2' := []$、$Z' := [\mathit{lp}]$ に適用する。
  $\pi_0(\mathrm{headI}[\mathit{lp}]) = \pi_0\mathit{lp} \le u$ である。

いずれの場合も goal_of で目標を得る。∎

この場合に使うのは $h_{Mon}$ と $h_{disj}$ だけであり、$h_M, h_{Rgt}, h_{lp}, h_{STn}, h_{IH}$ は使わない。
(b-1) の第 2 の枝が、塔の引数 $B$ が共有部分を越えて次のコピーへ入り込む場合であり、
そこでは $B$ は宿主 $M$ の部分列ではない。落とされる列 $\mathit{lp}$ を次のコピーの根 $q$ で差し替える
[(T.seqlex_of_sle_snoc')](#t-seqlex_of_sle_snoc') が、この食い違いを吸収している。

### 場合 A2 のための道具

交差の場合は**1 周期の降下**で処理する。深い方の印付き列が浅い方より 1 ブロック分以上上にある実例は、
1 つ小さい塔 $G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(\mathit{blk},n-1)$ の実例をちょうど $d_0$ だけシフトしたものであり、
それは強帰納法の仮定 $h_{IH}$ が処理する。以下はその降下に必要なリスト代数である。

<a id="t-shiftr0_add"></a>
### 定理 シフトの合成 (T.shiftr0_add)

**主張** $\mathrm{sh}_{a+b} X = \mathrm{sh}_a(\mathrm{sh}_b X)$。

**証明** $\mathrm{map}$ の合成則より右辺は
$\mathrm{map}\,\bigl(\lambda p.\ ((\pi_0 p + b) + a,\ \pi_1 p)\bigr)\,X$ であり、
$(\pi_0 p + b) + a = \pi_0 p + (a+b)$ であるから左辺の写像と一致する。∎

<a id="t-sle_of_prefix"></a>
### 定理 前部分列は $\preceq_{\mathrm{lex}}$ で下 (T.sle_of_prefix)

**主張** $X \sqsubseteq Y$ ならば $X \preceq_{\mathrm{lex}} Y$。

**証明** $Y = X \mathbin{+\!\!+} T$ と書く。$T = []$ なら $X = Y$（第 1 選言）。
$T \ne []$ なら [(T.seqlex_prefix)](Seqlex.md#t-seqlex_prefix) より $X \prec_{\mathrm{lex}} X \mathbin{+\!\!+} T = Y$。∎

<a id="t-shiftr0_prefix"></a>
### 定理 シフトは前部分列を保つ (T.shiftr0_prefix)

**主張** $X \sqsubseteq Y$ ならば $\mathrm{sh}_d X \sqsubseteq \mathrm{sh}_d Y$。

**証明** $Y = X \mathbin{+\!\!+} T$ と書くと [(T.shiftr0_append)](Cofinality.md#t-shiftr0_append) より
$\mathrm{sh}_d Y = \mathrm{sh}_d X \mathbin{+\!\!+} \mathrm{sh}_d T$ であり、$\mathrm{sh}_d T$ が求める継続である。∎

<a id="t-prefix_append_left"></a>
### 定理 共通左因子と前部分列 (T.prefix_append_left)

**主張** $X \sqsubseteq Y$ ならば $P \mathbin{+\!\!+} X \sqsubseteq P \mathbin{+\!\!+} Y$。

**証明** $Y = X \mathbin{+\!\!+} T$ と書くと、結合律より
$P \mathbin{+\!\!+} Y = (P \mathbin{+\!\!+} X) \mathbin{+\!\!+} T$。∎

<a id="t-copies_length"></a>
### 定理 コピー塔の長さ (T.copies_length)

**主張** $\lvert \mathrm{cp}_d(\mathit{blk},n)\rvert = n \cdot \lvert \mathit{blk}\rvert$。

**証明** $n$ に関する自然数の帰納法。帰納法の述語は
$\mathrm{K}(n) :\equiv \lvert \mathrm{cp}_d(\mathit{blk},n)\rvert = n \cdot \lvert \mathit{blk}\rvert$。

- 基底段 $n = 0$：[(T.copies_zero)](Wf.md#t-copies_zero) より左辺は $\lvert []\rvert = 0$、右辺も $0$。
- 帰納段 $n = k+1$：帰納法の仮定は $\mathrm{K}(k)$。
  [(T.copies_succ_back)](Cofinality.md#t-copies_succ_back) より
  $\mathrm{cp}_d(\mathit{blk},k+1) = \mathrm{cp}_d(\mathit{blk},k) \mathbin{+\!\!+} \mathrm{sh}_{k \cdot d}\,\mathit{blk}$ であるから、
  長さは $\mathrm{K}(k)$ と [(T.shiftr0_length)](Cofinality.md#t-shiftr0_length) より
  $k \cdot \lvert \mathit{blk}\rvert + \lvert \mathit{blk}\rvert = (k+1)\cdot\lvert \mathit{blk}\rvert$。∎

<a id="t-split_append_left"></a>
### 定理 分割の存在形 (T.split_append_left)

**主張** $C \mathbin{+\!\!+} D = E \mathbin{+\!\!+} F$ かつ $\lvert E\rvert \le \lvert C\rvert$ ならば、ある $K$ が存在して
$C = E \mathbin{+\!\!+} K$ かつ $F = K \mathbin{+\!\!+} D$。

**証明** $K := \mathrm{drop}\,\lvert E\rvert\,C$ と取り、[(T.split_prefix_left)](#t-split_prefix_left) を適用する。∎

<a id="t-prefix_cons_append"></a>
### 定理 共通左因子と共通列の後の前部分列 (T.prefix_cons_append)

**主張** $P \sqsubseteq Q$ ならば $A \mathbin{+\!\!+} c \mathbin{::} P \sqsubseteq A \mathbin{+\!\!+} c \mathbin{::} Q$。

**証明** $Q = P \mathbin{+\!\!+} T$ と書くと、結合律より
$A \mathbin{+\!\!+} c \mathbin{::} Q = (A \mathbin{+\!\!+} c \mathbin{::} P) \mathbin{+\!\!+} T$。∎

<a id="t-spineOK_of_nextrel1_strict"></a>
### 定理 nextrel1 条項から側条件（強形） (T.spineOK_of_nextrel1_strict)

**主張** $G, R \in \mathrm{PairSeq}$、$v_0,w_0,d_0 \in \mathbb{N}$ とし、
$\mathit{lp} := (v_0+d_0,\ w_0+1)$、$M := \bigl(G \mathbin{+\!\!+} ((v_0,w_0) \mathbin{::} R)\bigr) \mathbin{+\!\!+} [\mathit{lp}]$ とおく。
$$\lvert G\rvert \to^M_1 \bigl\lvert G \mathbin{+\!\!+} ((v_0,w_0) \mathbin{::} R)\bigr\rvert
\ \Longrightarrow\ \mathrm{SpineOK}(R,\ v_0+d_0,\ w_0+1) .$$

[(T.spineOK_of_nextrel1)](#t-spineOK_of_nextrel1) が $w_0 \le \pi_1 x$ を与えるのに対し、こちらは
$w_0 + 1 \le \pi_1 x$（すなわち $w_0 < \pi_1 x$）を与える。場合 A2 の第 3 の場合を反証するのに必要である。

**証明** $j_1 := \lvert G \mathbin{+\!\!+} ((v_0,w_0) \mathbin{::} R)\rvert$ とおき、仮定を
[(D.nextrel1)](Def.md#d-nextrel1) の 6 条件に分解して、第 5 条件 $\lvert G\rvert \le^M_0 j_1$ と
第 6 条件（最小性）を使う。
$R = U \mathbin{+\!\!+} x \mathbin{::} V$、$\pi_0 x < v_0+d_0$、$\forall y \in V,\ \pi_0 x < \pi_0 y$ を仮定して
$w_0 + 1 \le \pi_1 x$ を示す。$A := G \mathbin{+\!\!+} ((v_0,w_0) \mathbin{::} U)$ とおくと
$$M = A \mathbin{+\!\!+} \bigl(x \mathbin{::} (V \mathbin{+\!\!+} [\mathit{lp}])\bigr),\quad
\lvert A\rvert = \lvert G\rvert + 1 + \lvert U\rvert,\quad j_1 = \lvert A\rvert + 1 + \lvert V\rvert$$
であり、[(T.getD_append_right')](Cofinality.md#t-getD_append_right') より
$M\langle \lvert A\rvert\rangle = x$ である。
また、$\lvert A\rvert < y \le j_1$ なる $y$ を $y = \lvert A\rvert + (t+1)$ と書くと
$M\langle y\rangle = (V \mathbin{+\!\!+} [\mathit{lp}])\langle t\rangle$ であり、$t < \lvert V\rvert$ のときはこれは $V$ の要素で
$\pi_0 x$ より行 0 が真に大きく、$t = \lvert V\rvert$ のときはこれは $\mathit{lp}$ で
$\pi_0 x < v_0+d_0 = \pi_0\mathit{lp}$ である。よって
$$\forall y,\ \lvert A\rvert < y \le j_1 \Rightarrow M_{0,\lvert A\rvert} < M_{0,y} .$$
$\lvert G\rvert < \lvert A\rvert \le j_1$ とこれに
[(T.le0_through_pivot)](Nrmstep.md#t-le0_through_pivot) を適用して $\lvert A\rvert \le^M_0 j_1$。
最小性条項を $j := \lvert A\rvert$ に適用すると $M_{1,j_1} \le M_{1,\lvert A\rvert}$ であり、
$M\langle j_1\rangle = \mathit{lp}$ より [(T.entry_one)](Cofinality.md#t-entry_one) を用いて
$M_{1,j_1} = w_0+1$、$M_{1,\lvert A\rvert} = \pi_1 x$。よって $w_0+1 \le \pi_1 x$。∎

<a id="t-argDomCoreOn_bad_A2"></a>
### 定理 場合 A2：交差の場合 (T.argDomCoreOn_bad_A2)

**主張** [(T.argDomCoreOn_bad_A1)](#t-argDomCoreOn_bad_A1) と同じ文脈のもとで、判別条件が
$$h_{caseL} : \lvert X\rvert < \lvert G\rvert + (\lvert R\rvert+1), \qquad
h_{caseR} : \lvert G\rvert + (\lvert R\rvert+1) \le \lvert X\rvert + (\lvert A_1\rvert+1)$$
であるとする。このとき
$B \preceq_{\mathrm{lex}} \mathrm{sh}_e\bigl(A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} A_2)\bigr)$。

**証明** $\mathit{blk} := (v_0,w_0) \mathbin{::} R$、$L := \lvert \mathit{blk}\rvert = \lvert R\rvert+1$、$p := \lvert G\rvert + L$ とおく。
$i = \lvert X\rvert$、$j = \lvert X\rvert + (\lvert A_1\rvert+1)$ である。

**Step 0（$n \ge 2$）.** [(T.argdom_pos)](#t-argdom_pos) より $j < \lvert N\rvert$ であり、
[(T.copies_length)](#t-copies_length) より $\lvert N\rvert = \lvert G\rvert + n \cdot L$ である。
もし $n = 1$ ならば $\lvert N\rvert = \lvert G\rvert + L = p$ となり、$h_{caseR}$ の $p \le j$ と合わせて
$p \le j < p$ となって矛盾する。よって $2 \le n$ であり、$n = m+1$、$1 \le m$ と書ける。

**Step 1（境界 $p$ で切る）.** [(T.copies_succ_front)](Wf.md#t-copies_succ_front) より
$N = (G \mathbin{+\!\!+} \mathit{blk}) \mathbin{+\!\!+} \mathrm{sh}_{d_0}(\mathrm{cp}_{d_0}(\mathit{blk},m))$ である。
分解の等式を括り直すと
$$(G \mathbin{+\!\!+} \mathit{blk}) \mathbin{+\!\!+} \mathrm{sh}_{d_0}\bigl(\mathrm{cp}_{d_0}(\mathit{blk},m)\bigr)
= \bigl(X \mathbin{+\!\!+} [(u,w)]\bigr) \mathbin{+\!\!+} \Bigl(A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr)\Bigr)$$
である。$h_{caseL}$ より $\lvert X \mathbin{+\!\!+} [(u,w)]\rvert = i+1 \le p = \lvert G \mathbin{+\!\!+} \mathit{blk}\rvert$ であるから
[(T.split_append_left)](#t-split_append_left) が使えて $C$ が得られる：
$$G \mathbin{+\!\!+} \mathit{blk} = \bigl(X \mathbin{+\!\!+} [(u,w)]\bigr) \mathbin{+\!\!+} C, \qquad
A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr)
= C \mathbin{+\!\!+} \mathrm{sh}_{d_0}\bigl(\mathrm{cp}_{d_0}(\mathit{blk},m)\bigr)$$
で $\lvert C\rvert = p - (i+1)$。$h_{caseR}$（$p \le j = i + \lvert A_1\rvert + 1$）より
$\lvert C\rvert \le \lvert A_1\rvert$ であるから、第 2 の等式にもう一度
[(T.split_append_left)](#t-split_append_left) を適用して $D$ が得られる：
$$A_1 = C \mathbin{+\!\!+} D, \qquad
\mathrm{sh}_{d_0}\bigl(\mathrm{cp}_{d_0}(\mathit{blk},m)\bigr) = D \mathbin{+\!\!+} (u+e,w) \mathbin{::} \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr) .$$
とくに $\lvert A_1\rvert = \lvert C\rvert + \lvert D\rvert$ であり、
$j = i + \lvert A_1\rvert + 1 = (i + 1 + \lvert C\rvert) + \lvert D\rvert = p + \lvert D\rvert$、すなわち
$$j - L = \lvert G\rvert + \lvert D\rvert .$$
また [(T.mem_shiftr0)](Wf.md#t-mem_shiftr0) より
$\mathrm{sh}_{d_0}(\mathrm{cp}_{d_0}(\mathit{blk},m))$ の要素はすべて行 0 が $d_0$ 以上であり、
とくに $(u+e,w)$ もその要素だから $d_0 \le u+e$。

**Step 2（シフトを外す）.** 上の第 2 の等式の両辺に $\mathrm{sh}^{-}_{d_0}$ を施し、
[(T.shiftl0_shiftr0)](#t-shiftl0_shiftr0)、[(T.shiftl0_append)](#t-shiftl0_append)、
[(T.shiftl0_cons)](#t-shiftl0_cons) を使うと
$$\mathrm{cp}_{d_0}(\mathit{blk},m)
= \mathrm{sh}^{-}_{d_0} D \mathbin{+\!\!+} (u+e-d_0,\ w) \mathbin{::}
 \Bigl(\mathrm{sh}^{-}_{d_0} B \mathbin{+\!\!+} \bigl(\mathrm{sh}^{-}_{d_0} A_2 \mathbin{+\!\!+} \mathrm{sh}^{-}_{d_0} Z\bigr)\Bigr) . \tag{S}$$

**Step 3（$i$ と $j-L$ の三分律）.** $\lvert X\rvert$ と $\lvert G\rvert + \lvert D\rvert$ を比較する。

---

**(a) $\lvert X\rvert < \lvert G\rvert + \lvert D\rvert$（$i < j-L$）：1 周期の降下.**

$m \ge 1$ より $m = m''+1$ と書ける。
[(T.copies_succ_front)](Wf.md#t-copies_succ_front) より $\mathit{blk} \sqsubseteq \mathrm{cp}_{d_0}(\mathit{blk},m)$、
また (S) より $\mathrm{sh}^{-}_{d_0} D \sqsubseteq \mathrm{cp}_{d_0}(\mathit{blk},m)$ であり、
$\lvert \mathrm{sh}^{-}_{d_0} D\rvert = \lvert D\rvert$ である。
Step 1 の第 1 の等式は $X \mathbin{+\!\!+} [(u,w)] \sqsubseteq G \mathbin{+\!\!+} \mathit{blk}$ を与えるから、
[(T.prefix_append_left)](#t-prefix_append_left) と推移律により
$X \mathbin{+\!\!+} [(u,w)] \sqsubseteq G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(\mathit{blk},m)$、同様に
$G \mathbin{+\!\!+} \mathrm{sh}^{-}_{d_0} D \sqsubseteq G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(\mathit{blk},m)$。
長さは (a) の仮定より $\lvert X \mathbin{+\!\!+} [(u,w)]\rvert = i+1 \le \lvert G\rvert + \lvert D\rvert
= \lvert G \mathbin{+\!\!+} \mathrm{sh}^{-}_{d_0} D\rvert$ であるから、`List.prefix_of_prefix_length_le` により
$$X \mathbin{+\!\!+} [(u,w)] \sqsubseteq G \mathbin{+\!\!+} \mathrm{sh}^{-}_{d_0} D,$$
すなわち $A_1'$ が存在して $G \mathbin{+\!\!+} \mathrm{sh}^{-}_{d_0} D = (X \mathbin{+\!\!+} [(u,w)]) \mathbin{+\!\!+} A_1'$、
$\lvert A_1'\rvert = \lvert G\rvert + \lvert D\rvert - (i+1)$。これと (S) から、1 つ小さい塔は
$$G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(\mathit{blk},m)
= \bigl((X \mathbin{+\!\!+} [(u,w)]) \mathbin{+\!\!+} A_1'\bigr) \mathbin{+\!\!+} (u+e-d_0,\ w) \mathbin{::}
 \Bigl(\mathrm{sh}^{-}_{d_0} B \mathbin{+\!\!+} (\mathrm{sh}^{-}_{d_0} A_2 \mathbin{+\!\!+} \mathrm{sh}^{-}_{d_0} Z)\Bigr) \tag{N$'$}$$
と書ける。

*窓 $W_{tl}$ の取り出し.* [(T.copies_succ_back)](Cofinality.md#t-copies_succ_back) より
$G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(\mathit{blk},m+1)
= \bigl(G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(\mathit{blk},m)\bigr) \mathbin{+\!\!+} \mathrm{sh}_{m \cdot d_0}\,\mathit{blk}$ である。
これと (N$'$)、および Step 1 の括り直しを合わせると、共通左因子 $X \mathbin{+\!\!+} [(u,w)]$ を消去して
$$A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr)
= A_1' \mathbin{+\!\!+} (u+e-d_0,w) \mathbin{::}
 \Bigl(\bigl(\mathrm{sh}^{-}_{d_0} B \mathbin{+\!\!+} (\mathrm{sh}^{-}_{d_0} A_2 \mathbin{+\!\!+} \mathrm{sh}^{-}_{d_0} Z)\bigr)
  \mathbin{+\!\!+} \mathrm{sh}_{m \cdot d_0}\,\mathit{blk}\Bigr)$$
を得る。$\lvert A_1'\rvert \le \lvert A_1\rvert$（$\lvert A_1'\rvert = \lvert G\rvert+\lvert D\rvert-i-1$、
$\lvert A_1\rvert = \lvert C\rvert + \lvert D\rvert = p - i - 1 + \lvert D\rvert$ と $\lvert G\rvert \le p$ による）だから
[(T.split_append_left)](#t-split_append_left) が使えて $W_{nd}$ が得られ、
$A_1 = A_1' \mathbin{+\!\!+} W_{nd}$ かつ
$$(u+e-d_0,w) \mathbin{::} \Bigl(\cdots\Bigr) = W_{nd} \mathbin{+\!\!+} (u+e,w) \mathbin{::} \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr) .$$
$W_{nd} = []$ とすると $\lvert A_1\rvert = \lvert A_1'\rvert$ となるが、
$\lvert A_1\rvert - \lvert A_1'\rvert = (p - \lvert G\rvert) = L \ge 1$ であるから矛盾する。
よって $W_{nd} = w_{nd} \mathbin{::} W_{tl}$ と書け、両辺の先頭を比べて $w_{nd} = (u+e-d_0,w)$、尾部を比べて
$$\bigl(\mathrm{sh}^{-}_{d_0} B \mathbin{+\!\!+} (\mathrm{sh}^{-}_{d_0} A_2 \mathbin{+\!\!+} \mathrm{sh}^{-}_{d_0} Z)\bigr) \mathbin{+\!\!+} \mathrm{sh}_{m \cdot d_0}\,\mathit{blk}
= W_{tl} \mathbin{+\!\!+} (u+e,w) \mathbin{::} \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr) \tag{W}$$
であり、$A_1 = A_1' \mathbin{+\!\!+} (u+e-d_0,w) \mathbin{::} W_{tl}$。
この列 $(u+e-d_0,w)$ は $A_1$ の要素だから側条件より $u < u+e-d_0$、すなわち $d_0 < e$ であり、
とくに $u+e-d_0 = u + (e-d_0)$。

*小さい実例の末尾.* $A_2' := \mathrm{tw}_u(\mathrm{sh}^{-}_{d_0} A_2)$、
$Z_2 := \mathrm{dw}_u(\mathrm{sh}^{-}_{d_0} A_2) \mathbin{+\!\!+} \mathrm{sh}^{-}_{d_0} Z$ とおくと
$$A_2' \mathbin{+\!\!+} Z_2 = \mathrm{sh}^{-}_{d_0} A_2 \mathbin{+\!\!+} \mathrm{sh}^{-}_{d_0} Z, \qquad
A_2' \sqsubseteq \mathrm{sh}^{-}_{d_0} A_2, \qquad \forall x \in A_2',\ u < \pi_0 x$$
が成り立つ（第 1 は `List.takeWhile_append_dropWhile` と結合律、第 2 は `List.takeWhile_prefix`、
第 3 は `List.mem_takeWhile_imp`）。さらに
- $A_2' = [] \vee \pi_0(\mathrm{headI}\,A_2') \le u+(e-d_0)$：$A_2 = []$ なら $A_2' = []$。
  $A_2 = a \mathbin{::} A_2''$ なら $\mathrm{sh}^{-}_{d_0} A_2$ の先頭は $(\pi_0 a - d_0,\ \pi_1 a)$ であり、
  $u < \pi_0 a - d_0$ ならば $A_2'$ の先頭がそれで、側条件 $\pi_0 a \le u+e$ より
  $\pi_0 a - d_0 \le u+e-d_0 = u+(e-d_0)$。$u \ge \pi_0 a - d_0$ ならば $A_2' = []$。
- $Z_2 = [] \vee \pi_0(\mathrm{headI}\,Z_2) \le u$：$\mathrm{dw}_u(\mathrm{sh}^{-}_{d_0} A_2)$ が空でなければ、
  その先頭は述語 $\lambda q.\ u < \pi_0 q$ をみたさない（`List.head?_dropWhile_not`）から行 0 は $u$ 以下。
  空のときは $Z_2 = \mathrm{sh}^{-}_{d_0} Z$ であり、$Z = []$ なら $Z_2 = []$、
  $Z = z \mathbin{::} Z''$ なら側条件 $\pi_0 z \le u$ より $\pi_0 z - d_0 \le u$。

*小さい塔の実例.* (N$'$) と上の分解から
$$G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(\mathit{blk},m)
= \Bigl(X \mathbin{+\!\!+} (u,w) \mathbin{::} \bigl(A_1' \mathbin{+\!\!+} (u+(e-d_0),\ w) \mathbin{::} (\mathrm{sh}^{-}_{d_0} B \mathbin{+\!\!+} A_2')\bigr)\Bigr) \mathbin{+\!\!+} Z_2$$
であり、これは $\mathrm{ArgDomCoreOn}\bigl(G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(\mathit{blk},m)\bigr)$ の分解の形である。
$h_{IH}$（$1 \le m < m+1 = n$）を適用するために側条件を確かめる。
- $0 < e-d_0$：上で示した $d_0 < e$。
- $\forall x \in A_1',\ u < \pi_0 x$：$A_1' \subseteq A_1$（$A_1 = A_1' \mathbin{+\!\!+} \cdots$）と実例の側条件。
- $\forall x \in \mathrm{sh}^{-}_{d_0} B,\ u+(e-d_0) < \pi_0 x$：
  $x = (\pi_0 y - d_0,\ \pi_1 y)$（$y \in B$）と書けて、実例の側条件 $u+e < \pi_0 y$ と $d_0 < e$ から
  $u + (e-d_0) = u+e-d_0 < \pi_0 y - d_0$。
- 残り 3 つは上で構成したもの。
- $\mathrm{SpineOK}(A_1',\ u+(e-d_0),\ w)$：これが実質的な点であり、次に示す。

*降下した側条件.* $A_1' = U \mathbin{+\!\!+} x \mathbin{::} V$、$\pi_0 x < u+(e-d_0)$、
$\forall y \in V,\ \pi_0 x < \pi_0 y$ を仮定して $w \le \pi_1 x$ を示す。
$G \mathbin{+\!\!+} \mathrm{sh}^{-}_{d_0} D = (X \mathbin{+\!\!+} [(u,w)]) \mathbin{+\!\!+} A_1'$ であったから
$$\bigl((X \mathbin{+\!\!+} [(u,w)]) \mathbin{+\!\!+} U\bigr) \mathbin{+\!\!+} x \mathbin{::} V = G \mathbin{+\!\!+} \mathrm{sh}^{-}_{d_0} D .$$
$\lvert (X \mathbin{+\!\!+} [(u,w)]) \mathbin{+\!\!+} U\rvert$ と $\lvert G\rvert$ の 2 分律で場合分けする。

- **(i) $x$ が $G$ の内部にあるとき**（$\lvert (X \mathbin{+\!\!+} [(u,w)]) \mathbin{+\!\!+} U\rvert < \lvert G\rvert$）。
  [(T.split_append_left)](#t-split_append_left) より $V_3$ が存在して
  $$G = \Bigl(\bigl((X \mathbin{+\!\!+} [(u,w)]) \mathbin{+\!\!+} U\bigr) \mathbin{+\!\!+} [x]\Bigr) \mathbin{+\!\!+} V_3,
  \qquad V = V_3 \mathbin{+\!\!+} \mathrm{sh}^{-}_{d_0} D .$$
  これを Step 1 の第 1 の等式に代入し、共通左因子 $X \mathbin{+\!\!+} [(u,w)]$ を消去すると
  $$C = (U \mathbin{+\!\!+} [x]) \mathbin{+\!\!+} (V_3 \mathbin{+\!\!+} \mathit{blk}) .$$
  ここで $\pi_0 x < v_0$ を示す。[(T.copies_headI)](#t-copies_headI)（$\mathit{blk} \ne []$、$1 \le m$）より
  $\mathrm{headI}\,\mathrm{cp}_{d_0}(\mathit{blk},m) = (v_0,w_0)$ である。(S) の右辺の先頭を見ると、
  - $\mathrm{sh}^{-}_{d_0} D = []$ のとき：先頭は $(u+e-d_0,\ w)$ であるから $v_0 = u+e-d_0 = u+(e-d_0)$ であり、
    仮定 $\pi_0 x < u+(e-d_0)$ から $\pi_0 x < v_0$。
  - $\mathrm{sh}^{-}_{d_0} D = s \mathbin{::} S'$ のとき：先頭は $s$ であるから $s = (v_0,w_0)$ であり、
    $s \in V$（$V = V_3 \mathbin{+\!\!+} \mathrm{sh}^{-}_{d_0} D$）だから仮定より $\pi_0 x < \pi_0 s = v_0$。

  そこで実例の側条件 $h_6 = \mathrm{SpineOK}(A_1, u+e, w)$ を
  $U := U$、$V := (V_3 \mathbin{+\!\!+} \mathit{blk}) \mathbin{+\!\!+} D$、$x := x$ に適用する。
  - 分解：$A_1 = C \mathbin{+\!\!+} D = U \mathbin{+\!\!+} x \mathbin{::} \bigl((V_3 \mathbin{+\!\!+} \mathit{blk}) \mathbin{+\!\!+} D\bigr)$。
  - 水準：$\pi_0 x < u+(e-d_0) \le u+e$。
  - 右から見える条件：$y \in V_3$ なら $V_3 \subseteq V$ より $\pi_0 x < \pi_0 y$。
    $y \in \mathit{blk}$ なら $y = (v_0,w_0)$ か $y \in R$ であり、前者は $\pi_0 x < v_0$、
    後者は $h_{Rgt}$ より $v_0 < \pi_0 y$ と合わせて $\pi_0 x < \pi_0 y$。
    $y \in D$ なら $y \in \mathrm{sh}_{d_0}(\mathrm{cp}_{d_0}(\mathit{blk},m))$（Step 1 の第 2 の等式）であるから
    $y = (\pi_0 z + d_0,\ \pi_1 z)$（$z \in \mathrm{cp}_{d_0}(\mathit{blk},m)$）と書け、
    $h_{Rgt}$ から $\forall x \in R,\ v_0 \le \pi_0 x$ であるので
    [(T.copies_v0_le)](Wf.md#t-copies_v0_le) より $v_0 \le \pi_0 z$、よって $\pi_0 x < v_0 \le \pi_0 y$。

  結論は $w \le \pi_1 x$ である。
- **(ii) $x$ がシフト前の窓の内部にあるとき**（$\lvert G\rvert \le \lvert (X \mathbin{+\!\!+} [(u,w)]) \mathbin{+\!\!+} U\rvert$）。
  [(T.split_append_left)](#t-split_append_left) より $U_2$ が存在して
  $(X \mathbin{+\!\!+} [(u,w)]) \mathbin{+\!\!+} U = G \mathbin{+\!\!+} U_2$ かつ
  $\mathrm{sh}^{-}_{d_0} D = U_2 \mathbin{+\!\!+} x \mathbin{::} V$。
  $D$ の要素はすべて行 0 が $d_0$ 以上だから [(T.shiftr0_shiftl0)](#t-shiftr0_shiftl0) が使えて
  $$D = \mathrm{sh}_{d_0}(\mathrm{sh}^{-}_{d_0} D)
  = \mathrm{sh}_{d_0} U_2 \mathbin{+\!\!+} (\pi_0 x + d_0,\ \pi_1 x) \mathbin{::} \mathrm{sh}_{d_0} V .$$
  $h_6$ を $U := C \mathbin{+\!\!+} \mathrm{sh}_{d_0} U_2$、$V := \mathrm{sh}_{d_0} V$、
  $x := (\pi_0 x + d_0,\ \pi_1 x)$ に適用する。
  - 分解：$A_1 = C \mathbin{+\!\!+} D$ に上の $D$ を代入したもの。
  - 水準：$\pi_0 x < u+(e-d_0) = u+e-d_0$ と $d_0 < e$ より $\pi_0 x + d_0 < u+e$。
  - 右から見える条件：$\mathrm{sh}_{d_0} V$ の要素は $(\pi_0 z + d_0,\ \pi_1 z)$（$z \in V$）であり、
    $\pi_0 x < \pi_0 z$ から $\pi_0 x + d_0 < \pi_0 z + d_0$。

  結論は $w \le \pi_1(\pi_0 x + d_0,\ \pi_1 x) = \pi_1 x$ である。

以上で $h_{IH}$ の適用条件がすべて揃い、
$$\mathrm{sh}^{-}_{d_0} B \preceq_{\mathrm{lex}}
\mathrm{sh}_{e-d_0}\bigl(A_1' \mathbin{+\!\!+} (u+(e-d_0),w) \mathbin{::} (\mathrm{sh}^{-}_{d_0} B \mathbin{+\!\!+} A_2')\bigr) \tag{IH}$$
を得る。

*結論の持ち上げ.* まず
$$\mathrm{sh}^{-}_{d_0} B \mathbin{+\!\!+} A_2' \ \sqsubseteq\ W_{tl} \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} A_2)$$
を示す。$W_{tl} \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z))$ を共通の第 3 の列として
`List.prefix_of_prefix_length_le` を使う。左は (W) の左辺の前部分列であり
（$(\mathrm{sh}^{-}_{d_0} B \mathbin{+\!\!+} A_2') \mathbin{+\!\!+} \bigl(Z_2 \mathbin{+\!\!+} \mathrm{sh}_{m \cdot d_0}\mathit{blk}\bigr)$ が (W) の左辺）、
右は $Z$ を継ぎ足したものである。長さは
$\lvert A_2'\rvert \le \lvert \mathrm{sh}^{-}_{d_0} A_2\rvert = \lvert A_2\rvert$（`List.IsPrefix.length_le`）より
$\lvert \mathrm{sh}^{-}_{d_0} B\rvert + \lvert A_2'\rvert \le \lvert W_{tl}\rvert + 1 + \lvert B\rvert + \lvert A_2\rvert$。
次に $A_1 = A_1' \mathbin{+\!\!+} (u+(e-d_0),w) \mathbin{::} W_{tl}$ と
[(T.prefix_cons_append)](#t-prefix_cons_append) から
$$A_1' \mathbin{+\!\!+} (u+(e-d_0),w) \mathbin{::} \bigl(\mathrm{sh}^{-}_{d_0} B \mathbin{+\!\!+} A_2'\bigr)
\ \sqsubseteq\ A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} A_2) .$$
[(T.shiftr0_prefix)](#t-shiftr0_prefix)（$d := e-d_0$）を施し、(IH) と
[(T.sle_append_mono)](Cofinality.md#t-sle_append_mono) を合わせると
$$\mathrm{sh}^{-}_{d_0} B \preceq_{\mathrm{lex}} \mathrm{sh}_{e-d_0}\bigl(A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} A_2)\bigr) .$$
最後に [(T.sle_shiftr0)](#t-sle_shiftr0) の $(\Leftarrow)$ 方向（$d := d_0$）を適用する。
$B$ の要素 $x$ は実例の側条件より $u+e < \pi_0 x$ をみたし、Step 1 の $d_0 \le u+e$ と合わせて
$d_0 \le \pi_0 x$ であるから、
[(T.shiftr0_shiftl0)](#t-shiftr0_shiftl0) より $\mathrm{sh}_{d_0}(\mathrm{sh}^{-}_{d_0} B) = B$、
また [(T.shiftr0_add)](#t-shiftr0_add) と $d_0 + (e-d_0) = e$（$d_0 \le e$）より
$\mathrm{sh}_{d_0}\bigl(\mathrm{sh}_{e-d_0} Y\bigr) = \mathrm{sh}_e Y$。よって目標を得る。

---

**(b) $\lvert X\rvert = \lvert G\rvert + \lvert D\rvert$（$i = j-L$）：深い列は浅い列のちょうど $d_0$ シフト.**

(S) より
$$G \mathbin{+\!\!+} \mathrm{cp}_{d_0}(\mathit{blk},m)
= \bigl(G \mathbin{+\!\!+} \mathrm{sh}^{-}_{d_0} D\bigr) \mathbin{+\!\!+} (u+e-d_0,\ w) \mathbin{::}
 \Bigl(\mathrm{sh}^{-}_{d_0} B \mathbin{+\!\!+} (\mathrm{sh}^{-}_{d_0} A_2 \mathbin{+\!\!+} \mathrm{sh}^{-}_{d_0} Z)\Bigr)$$
であり、[(T.copies_succ_back)](Cofinality.md#t-copies_succ_back) と Step 1 の括り直しから
$$\bigl(X \mathbin{+\!\!+} [(u,w)]\bigr) \mathbin{+\!\!+} \Bigl(A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z))\Bigr)
= \bigl(G \mathbin{+\!\!+} \mathrm{sh}^{-}_{d_0} D\bigr) \mathbin{+\!\!+}
 \Bigl((u+e-d_0,w) \mathbin{::} \bigl(\cdots \mathbin{+\!\!+} \mathrm{sh}_{m \cdot d_0}\mathit{blk}\bigr)\Bigr) .$$
$\lvert G \mathbin{+\!\!+} \mathrm{sh}^{-}_{d_0} D\rvert = \lvert G\rvert + \lvert D\rvert = \lvert X\rvert \le \lvert X\rvert+1$
であるから [(T.split_append_left)](#t-split_append_left) が使えて $K$ が得られ、
$X \mathbin{+\!\!+} [(u,w)] = (G \mathbin{+\!\!+} \mathrm{sh}^{-}_{d_0} D) \mathbin{+\!\!+} K$ かつ
$$(u+e-d_0,w) \mathbin{::} \bigl(\cdots \mathbin{+\!\!+} \mathrm{sh}_{m \cdot d_0}\mathit{blk}\bigr)
= K \mathbin{+\!\!+} \Bigl(A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z))\Bigr) .$$
長さを比べると $\lvert K\rvert = (\lvert X\rvert+1) - (\lvert G\rvert+\lvert D\rvert) = 1$ であるから $K = [k]$。
第 1 の等式で長さ $\lvert G \mathbin{+\!\!+} \mathrm{sh}^{-}_{d_0} D\rvert = \lvert X\rvert$ に注意して `List.append_inj` を使うと
$X = G \mathbin{+\!\!+} \mathrm{sh}^{-}_{d_0} D$ かつ $[(u,w)] = [k]$、すなわち $k = (u,w)$。
第 2 の等式の先頭を比べると $k = (u+e-d_0,\ w)$。よって $u = u+e-d_0$ であり、
$d_0 \le u+e$（Step 1）と合わせて $e = d_0$。
また第 2 の等式の尾部から
$$\Bigl(\mathrm{sh}^{-}_{d_0} B \mathbin{+\!\!+} (\mathrm{sh}^{-}_{d_0} A_2 \mathbin{+\!\!+} \mathrm{sh}^{-}_{d_0} Z)\Bigr) \mathbin{+\!\!+} \mathrm{sh}_{m \cdot d_0}\mathit{blk}
= A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr)$$
であり、とくに
$\mathrm{sh}^{-}_{d_0} B \sqsubseteq A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z))$。
一方 $A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} A_2) \sqsubseteq
A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z))$ であり、
$\lvert \mathrm{sh}^{-}_{d_0} B\rvert = \lvert B\rvert \le \lvert A_1\rvert + 1 + \lvert B\rvert + \lvert A_2\rvert$
であるから `List.prefix_of_prefix_length_le` により
$$\mathrm{sh}^{-}_{d_0} B \sqsubseteq A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} A_2) .$$
[(T.shiftr0_prefix)](#t-shiftr0_prefix)（$d := e$）を施すと、$e = d_0$ と
$\forall x \in B,\ d_0 \le \pi_0 x$（実例の側条件 $u+e < \pi_0 x$ と Step 1 の $d_0 \le u+e$ による）から
[(T.shiftr0_shiftl0)](#t-shiftr0_shiftl0) により
$\mathrm{sh}_e(\mathrm{sh}^{-}_{d_0} B) = B$ であるから
$$B \sqsubseteq \mathrm{sh}_e\bigl(A_1 \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} A_2)\bigr) .$$
[(T.sle_of_prefix)](#t-sle_of_prefix) で目標を得る。この場合は $h_{IH}$ を使わない。

---

**(c) $\lvert G\rvert + \lvert D\rvert < \lvert X\rvert$（$i > j-L$）：起こりえない.**

矛盾を導く。Step 0 の $1 \le m$ より $m = m'+1$ と書ける。

**(c-1) $(u,w)$ はブロック $R$ の内部にある.** Step 1 の第 1 の等式
$G \mathbin{+\!\!+} \mathit{blk} = (X \mathbin{+\!\!+} [(u,w)]) \mathbin{+\!\!+} C$ に
[(T.split_append_left)](#t-split_append_left) を適用する（$\lvert G\rvert \le \lvert X\rvert + 1$ は
$\lvert G\rvert \le \lvert G\rvert + \lvert D\rvert < \lvert X\rvert$ から）。$K$ が得られて
$X \mathbin{+\!\!+} [(u,w)] = G \mathbin{+\!\!+} K$ かつ $\mathit{blk} = K \mathbin{+\!\!+} C$。
$K = []$ とすると $\lvert X\rvert + 1 = \lvert G\rvert$ となるが $\lvert G\rvert < \lvert X\rvert$ に反するから
$K = k_0 \mathbin{::} K_1$ であり、$\mathit{blk} = (v_0,w_0) \mathbin{::} R$ の尾部を比べて $R = K_1 \mathbin{+\!\!+} C$。
さらに $X \mathbin{+\!\!+} [(u,w)] = (G \mathbin{+\!\!+} [k_0]) \mathbin{+\!\!+} K_1$ に
[(T.split_append_left)](#t-split_append_left) を適用して（$\lvert G\rvert + 1 \le \lvert X\rvert$）$T$ を得る：
$X = (G \mathbin{+\!\!+} [k_0]) \mathbin{+\!\!+} T$ かつ $K_1 = T \mathbin{+\!\!+} [(u,w)]$。したがって
$$R = T \mathbin{+\!\!+} (u,w) \mathbin{::} C .$$
とくに $(u,w) \in R$ であるから $h_{Rgt}$ より $v_0 < u$。

**(c-2) 第 1 コピーの根が $u < v_0+d_0$ と $w \le w_0$ を与える.**
[(T.copies_succ_cons)](Wf.md#t-copies_succ_cons) と [(T.shiftr0_cons)](Wf.md#t-shiftr0_cons) より
$$\mathrm{sh}_{d_0}\bigl(\mathrm{cp}_{d_0}(\mathit{blk},\ m'+1)\bigr)
= (v_0+d_0,\ w_0) \mathbin{::} \mathrm{sh}_{d_0}\Bigl(R \mathbin{+\!\!+} \mathrm{sh}_{d_0}\bigl(\mathrm{cp}_{d_0}(\mathit{blk},m')\bigr)\Bigr) .$$
これを Step 1 の第 2 の等式
$\mathrm{sh}_{d_0}(\mathrm{cp}_{d_0}(\mathit{blk},m)) = D \mathbin{+\!\!+} (u+e,w) \mathbin{::} (B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z))$
と比べる。
- $D = []$ のとき：先頭を比べて $(v_0+d_0,w_0) = (u+e,w)$、すなわち $v_0+d_0 = u+e$ かつ $w_0 = w$。
  $0 < e$ より $u < u+e = v_0+d_0$ であり、また $w \le w_0$。
- $D = d_1 \mathbin{::} D'$ のとき：先頭を比べて $d_1 = (v_0+d_0,w_0)$、尾部を比べて
  $$\mathrm{sh}_{d_0}\Bigl(R \mathbin{+\!\!+} \mathrm{sh}_{d_0}\bigl(\mathrm{cp}_{d_0}(\mathit{blk},m')\bigr)\Bigr)
  = D' \mathbin{+\!\!+} (u+e,w) \mathbin{::} \bigl(B \mathbin{+\!\!+} (A_2 \mathbin{+\!\!+} Z)\bigr) .$$
  $A_1 = C \mathbin{+\!\!+} D = C \mathbin{+\!\!+} (v_0+d_0,w_0) \mathbin{::} D'$ であるから、実例の側条件より $u < v_0+d_0$。
  (c-1) の $v_0 < u$ と合わせて $0 < d_0$。
  [(T.copies_tl_gt)](Wf.md#t-copies_tl_gt) より
  $\forall x \in R \mathbin{+\!\!+} \mathrm{sh}_{d_0}(\mathrm{cp}_{d_0}(\mathit{blk},m')),\ v_0 < \pi_0 x$、
  したがって上の $\mathrm{sh}_{d_0}(\cdots)$ の要素はすべて行 0 が $v_0+d_0$ より大きい。
  そこで実例の側条件 $h_6 = \mathrm{SpineOK}(A_1,u+e,w)$ を
  $U := C$、$V := D'$、$x := (v_0+d_0,w_0)$ に適用する。
  分解は上の $A_1$ の形、水準の条件 $v_0+d_0 < u+e$ は $(u+e,w)$ がその $\mathrm{sh}_{d_0}(\cdots)$ の要素であることから、
  右から見える条件は $D'$ の要素も同じ列の要素であることから従う。結論は $w \le w_0$。

**(c-3) 強形の最小性条項.** (c-1)(c-2) より $v_0 < u < v_0 + d_0$、とくに $0 < d_0$ である。
$h_{disj}$ の第 1 選言は $d_0 = 0$ を含むので成り立たない。よって第 2 選言が成り立ち、
$\mathit{lp} = (v_0+d_0,\ w_0+1)$ かつ $\lvert G\rvert \to^M_1 (\lvert M\rvert - 1)$ である。
$h_{Meq}$ により $M = (G \mathbin{+\!\!+} \mathit{blk}) \mathbin{+\!\!+} [(v_0+d_0,w_0+1)]$、
$\lvert M\rvert - 1 = \lvert G \mathbin{+\!\!+} \mathit{blk}\rvert$ であるから、これは
[(T.spineOK_of_nextrel1_strict)](#t-spineOK_of_nextrel1_strict) の仮定である。
その結論 $\mathrm{SpineOK}(R,\ v_0+d_0,\ w_0+1)$ を
$U := T$、$V := C$、$x := (u,w)$ に適用する。分解は (c-1) の $R = T \mathbin{+\!\!+} (u,w) \mathbin{::} C$、
水準の条件は (c-2) の $u < v_0+d_0$、右から見える条件は $C \subseteq A_1$（$A_1 = C \mathbin{+\!\!+} D$）と
実例の側条件 $\forall y \in A_1,\ u < \pi_0 y$ から従う。結論は $w_0 + 1 \le w$ である。
これは (c-2) の $w \le w_0$ と矛盾する。∎

$h_{Mon}$ と $h_{STn}$ はこの場合では使わない。交差の場合は、塔自身の周期性と
コピー数についての帰納法の仮定だけで決着する。

<a id="t-argDomCoreOn_bad"></a>
### 定理 導出帰納の bad 枝 (T.argDomCoreOn_bad)

**主張** [(T.argDomCoreOn_bad_A1)](#t-argDomCoreOn_bad_A1) の文脈のうち
$h_M, h_{Mon}, h_{Meq}, h_{Rgt}, h_{lp}, h_{disj}, h_{STn}$ と $1 \le n$ を仮定すると
$$\mathrm{ArgDomCoreOn}\bigl(G \mathbin{+\!\!+} \mathrm{cp}_{d_0}((v_0,w_0) \mathbin{::} R,\ n)\bigr) .$$

**証明** $n$ に関する**強帰納法**。帰納法の述語は
$$\Omega(n) :\equiv 1 \le n \to \mathrm{ArgDomCoreOn}\bigl(G \mathbin{+\!\!+} \mathrm{cp}_{d_0}((v_0,w_0)\mathbin{::}R,\ n)\bigr)$$
であり、強帰納法の仮定は $\forall k < n,\ \Omega(k)$ である。これは
$$h_{IH} : \forall m,\ 1 \le m \to m < n \to
 \mathrm{ArgDomCoreOn}\bigl(G \mathbin{+\!\!+} \mathrm{cp}_{d_0}((v_0,w_0)\mathbin{::}R,\ m)\bigr)$$
と同じものである（$\Omega(m)$ に $1 \le m$ を与える）。この $h_{IH}$ が使えることが、
$\mathrm{ArgDomCoreOn}(M)$ から $\forall n \ge 1,\ \mathrm{ArgDomCoreOn}(M[n])$ を示すという形の
（外側の導出帰納とは別の）内側の帰納法を立てる理由である。

$\Omega(n)$ を示す。$1 \le n$ と塔の分解 $X, A_1, B, A_2, Z, u, w, e$ と 7 つの側条件を与える。
自然数の 2 分律を 2 回使って場合分けする。

- $\lvert X\rvert + (\lvert A_1\rvert+1) < \lvert G\rvert + (\lvert R\rvert+1)$ のとき：
  [(T.argDomCoreOn_bad_B)](#t-argDomCoreOn_bad_B) を適用する。
- そうでない（$\lvert G\rvert + (\lvert R\rvert+1) \le \lvert X\rvert + (\lvert A_1\rvert+1)$）とき、さらに
  - $\lvert X\rvert < \lvert G\rvert + (\lvert R\rvert+1)$ ならば
    [(T.argDomCoreOn_bad_A2)](#t-argDomCoreOn_bad_A2) を適用する。
  - $\lvert G\rvert + (\lvert R\rvert+1) \le \lvert X\rvert$ ならば
    [(T.argDomCoreOn_bad_A1)](#t-argDomCoreOn_bad_A1) を適用する。

3 つの場合は上の 2 回の 2 分律で尽くされており、いずれの場合も結論は目標そのものである。∎

<a id="t-argDomCoreOn_oper"></a>
### 定理 帰納段：oper で保たれる (T.argDomCoreOn_oper)

**主張** $M \in \mathrm{ST\_PS}$、$\mathrm{ArgDomCoreOn}(M)$、$1 \le n$ ならば $\mathrm{ArgDomCoreOn}(M[n])$。

**証明** [(D.oper)](Def.md#d-oper) の分岐で場合分けする。

**分岐 (a)（$\lvert M\rvert - 1 = 0$）.** [(T.oper_eq_self_of_short)](Mechanized.md#t-oper_eq_self_of_short) より
$M[n] = M$ であるから、仮定 $\mathrm{ArgDomCoreOn}(M)$ がそのまま結論である。

**分岐 (b)（$\lvert M\rvert-1 \ne 0$ かつ $M_{0,\lvert M\rvert-1} = 0 \wedge M_{1,\lvert M\rvert-1} = 0$）.**
[(T.oper_eq_pred_of_zero)](Mechanized.md#t-oper_eq_pred_of_zero) より $M[n] = \mathrm{Pred}\,M$ であり、
$\lvert M\rvert - 1 \ne 0$ から $\lvert M\rvert \ge 2$、すなわち $\neg(\lvert M\rvert \le 1)$ であるから
[(D.Pred)](Def.md#d-Pred) の第 2 の場合により $\mathrm{Pred}\,M = \mathrm{dropLast}\,M$。
仮定 $M_{0,\lvert M\rvert-1} = 0 \wedge M_{1,\lvert M\rvert-1} = 0$ は
[(T.entry_zero)](Cofinality.md#t-entry_zero)、[(T.entry_one)](Cofinality.md#t-entry_one) により
$M\langle \lvert M\rvert-1\rangle = (0,0)$ を意味する。$M \ne []$（$\lvert M\rvert \ge 2$）だから
[(T.dropLast_snoc_getD)](Cofinality.md#t-dropLast_snoc_getD) より
$$\mathrm{dropLast}\,M \mathbin{+\!\!+} [(0,0)] = M .$$
したがって $\mathrm{ArgDomCoreOn}(M)$ は $\mathrm{ArgDomCoreOn}(\mathrm{dropLast}\,M \mathbin{+\!\!+} [(0,0)])$ であり、
[(T.argDomCoreOn_snoc_zero)](#t-argDomCoreOn_snoc_zero) を $p := (0,0)$（$\pi_0 p = 0$）に適用して
$\mathrm{ArgDomCoreOn}(\mathrm{dropLast}\,M) = \mathrm{ArgDomCoreOn}(M[n])$ を得る。

**分岐 (c)（親が存在しない場合）.** $M \in \mathrm{ST\_PS}$ かつ $0 < \lvert M\rvert$ かつ末尾が $(0,0)$ でないとき、
[(T.hasParent_last_ST_PS)](Cofinality.md#t-hasParent_last_ST_PS) より
$\mathrm{hasParent}\bigl(M,\ \mathrm{idx}_1(M,\lvert M\rvert-1),\ \lvert M\rvert-1\bigr)$ が成り立つ。
すなわち標準形に対して分岐 (c) は起こらない。

**分岐 (d)（bad 枝）.** [(T.oper_bad_blocks_all)](Cofinality.md#t-oper_bad_blocks_all) を、
$1 < \lvert M\rvert$、$\mathrm{steps1}\,M$（[(T.blockok_ST_PS)](Seqlex.md#t-blockok_ST_PS) の第 3 成分）、
$\mathrm{r1ok}\,M$（[(T.r1ok_ST_PS)](Nrmstep.md#t-r1ok_ST_PS)）、末尾が $(0,0)$ でないこと、
上の $\mathrm{hasParent}$ に適用すると、$G, v_0, w_0, R, d_0, \mathit{lp}$ が得られて
$$M = G \mathbin{+\!\!+} ((v_0,w_0)\mathbin{::}R) \mathbin{+\!\!+} [\mathit{lp}], \qquad
\forall m \ge 1,\ M[m] = G \mathbin{+\!\!+} \mathrm{cp}_{d_0}((v_0,w_0)\mathbin{::}R,\ m)$$
と $h_{Rgt}$、$h_{lp}$、$h_{disj}$ が成り立つ。さらに、各 $m \ge 1$ について
$G \mathbin{+\!\!+} \mathrm{cp}_{d_0}((v_0,w_0)\mathbin{::}R,\ m) = M[m]$ であり、
[(D.ST_PS)](Def.md#d-ST_PS) の規則 (oper) を $M \in \mathrm{ST\_PS}$ と $1 \le m$ に適用して
$M[m] \in \mathrm{ST\_PS}$、すなわち $h_{STn}$ が成り立つ。
よって $M[n] = G \mathbin{+\!\!+} \mathrm{cp}_{d_0}((v_0,w_0)\mathbin{::}R,\ n)$ に対し
[(T.argDomCoreOn_bad)](#t-argDomCoreOn_bad) を適用すればよい。∎

<a id="t-argDomCoreOn_ST_PS"></a>
### 定理 導出に関する帰納法 (T.argDomCoreOn_ST_PS)

**主張** $N \in \mathrm{ST\_PS}$ ならば $\mathrm{ArgDomCoreOn}(N)$。

**証明** [(D.ST_PS)](Def.md#d-ST_PS) の導出に関する帰納法。帰納法の述語は
$$P(N) :\equiv \mathrm{ArgDomCoreOn}(N) .$$

- 基底段（規則 (diag)）：$N = \Delta_0^v$ の形である。
  [(T.argDomCoreOn_diag)](#t-argDomCoreOn_diag) より $P(\Delta_0^v)$。
- 帰納段（規則 (oper)）：$N = M[n]$ の形で、$M \in \mathrm{ST\_PS}$、$1 \le n$ が与えられ、
  帰納法の仮定は $P(M)$、すなわち $\mathrm{ArgDomCoreOn}(M)$ である。
  [(T.argDomCoreOn_oper)](#t-argDomCoreOn_oper) を $M \in \mathrm{ST\_PS}$、$P(M)$、$1 \le n$ に適用して
  $P(M[n])$ を得る。∎

<a id="t-argDomCore_holds"></a>
### 定理 核の成立 (T.argDomCore_holds)

**主張** $\mathrm{ArgDomCore}$。

**証明** [(T.argDomCoreOn_ST_PS)](#t-argDomCoreOn_ST_PS) は
$\forall N,\ N \in \mathrm{ST\_PS} \to \mathrm{ArgDomCoreOn}(N)$ であるから、
[(T.argDomCore_of_on)](#t-argDomCore_of_on) に与えればよい。∎

これと [(T.pss_cofinality_of_core)](#t-pss_cofinality_of_core) から、PSS Bachmann 共終性
$$M, N \in \mathrm{ST\_PS},\ \mathrm{tr}\,N \prec \mathrm{tr}\,M
\ \Longrightarrow\ \exists n \ge 1,\ \mathrm{tr}\,N \preceq \mathrm{tr}\,(M[n])$$
が仮定なしで得られる。これを [`Final.md`](Final.md) が
[(T.pss_cofinality_holds)](Final.md#t-pss_cofinality_holds) として取り出す。
