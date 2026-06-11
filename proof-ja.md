[README](README-ja.md)

# ペア数列システムの停止性（`p_a(b)+c` アプローチ）

ペア数列システム (Pair Sequence System, PSS) は Bashicu 氏が考案した。
その停止性は P進大好きbot 氏が証明した。
本論文では P 進大好きbot 氏の証明と別のアプローチにてペア数列システムの停止性の証明を試みる。

本証明はペア数列を独自の三分木記法 `p_a(b)+c` へ変換 (`translate`) し、
その記法上の整礎な順序 `≺` に関して**展開の各ステップで測度が真に減少する**こと
を示して証明する。これは原始数列システム (PrSS) の停止証明
（[`prss-proof`](https://github.com/koteitan/prss-proof)）の戦略
——数列をカントール標準形に写し、`expand` の各ステップで順序数が真に減少する——
をペア数列へ一般化したものである。これは P進大好きbot 氏の証明とは異なる別アプローチである。

減少を測る記法 `p_a(b)+c`（型 `three`）は独自の三分木として定義する（Buchholz §2 の
項記法系 $(\mathrm{OT},<)$ と同型）。その順序 `≺`（添字優先の純辞書式 `olt`）の**整礎性**は、
**順序数を一切使わず、構文的な帰納法で**証明する（後述 §7、`wf.thy`、session YAPSS）。
これが本証明の核心方針：減少補題も整礎性も独自記法上で完結させ、外部の順序数論
（Buchholz ψ や Towsner 論文の整礎性定理）を**引用せず自前で**与える。

PSS の証明論的強さは **ψ₀(ψ_ω(0))**（Buchholz ordinal, Ω_ω の崩壊）と
考えられており、記法 `p_a(b)` の添字 `a` を自然数（0,1,2,… とその上限 ω）に
取ることに対応する。

> **記法の凡例**: 本稿には Isabelle/HOL で形式化された証明本文を記す。全体が session
> YAPSS（`def.thy` / `mechanized.thy` / `proofs.thy` / `wf.thy`、**順序数ライブラリ不使用**）
> で検証され、停止性 `PSS_terminates` は**ただ一つの未証明補題** `wfE_within_level`
> （同一 maxsub レベル内の整礎性＝Buchholz 崩壊核）に帰着する。それ以外は全て緑。
> ビルド: `isbman build -d . YAPSS`。
> （旧 route A＝ZFC 順序数で ψ を構成する意味論的証明は、Buchholz ψ が PSS 標準形の対角を
> collapse するため破棄した。)

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

## 2. 三分木記法 `p_a(b)+c`（`mechanized.thy`）

**定義 2.1（項, `three`）。** 自然数1つと部分項2つをもつ節点からなる木を導入する
（この時点で順序性は未導入。構造のみから命名する）：

$$ \mathsf{three} ::= Z \ \mid\ P\ a\ b\ c\qquad (a\in\mathbb N,\ b,c\in\mathsf{three}) $$

$Z=0$、$P\,a\,b\,c = p_a(b)+c$ と読む。主要項 $p_a(b)$ は添字 $a$（自然数）と引数
$b$ をもち、$c$ は和の残り（同レベルの兄弟）。これは PrSS の
$E\,a\,b=\omega^{a}+b$ の一般化（単一指数 $\omega^a$ を $p_a(b)$ に置換）である。

**定義 2.2（添字優先順序, `olt` / $\prec$）。** 主要項を**添字優先**で辞書式比較する：

$$ Z\prec P\,a\,b\,c,\qquad
P\,a\,b\,c \prec P\,e\,f\,g \iff a<e \ \vee\ (a=e\wedge b\prec f)\ \vee\ (a=e\wedge b=f\wedge c\prec g). $$

すなわち $(a,b,c)$ の 3 次元辞書式順序（$a$ は自然数の $<$、$b,c$ は再帰的に $\prec$）。

> $\prec$ は線形順序（**`olt_irrefl`, `olt_trans`, `olt_total`** すべて Isabelle ✓）。

**順序の向きについて。** 本記法では主要項を**添字優先**で比較する。この向きの下で
展開ステップの測度減少が成り立つ（§4, `m_step_decreases`）。これは Buchholz の
「添字が大きいほど大きい」と同じ向きである。

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

## 4. 展開での減少（Isabelle ✓, `m_step_decreases`）

> **減少補題（`m_step_decreases`, Isabelle ✓）。** $\mathrm{Lng}\,M>1$,
> $n\ge1 \Rightarrow \mathrm{translate}(M[n])\prec\mathrm{translate}(M)$。

具体例で機構を見る：$M=(0,0)(1,1)$, $M[2]=(0,0)(1,0)(2,0)$ では

$$ \mathrm{translate}(M)=p_0(p_1(0)),\qquad \mathrm{translate}(M[2])=p_0(p_0(p_0(0))). $$

両者 $p_0(\cdot)$ なので引数 $p_1(0)$ vs $p_0(p_0(0))$ の比較に帰着し、添字
$1>0$ より $p_0(p_0(0))\prec p_1(0)$、よって減少（添字優先の効き方）。
以下、$M[n]$ の3ケース（$j_1{=}0$／Pred／bad）ごとに減少を示す。

**Pred 2 ケース（Isabelle ✓, `translate_oper_pred`）。** 末尾対が $(0,0)$、または
行 $i_1$ に一意の親が無いとき $M[n]=\mathrm{Pred}\,M=\mathrm{butlast}\,M$ なので、
**末尾追加で測度が真に増大**する補題

$$ \mathrm{translate}\,C \prec \mathrm{translate}\,(C\mathbin{@}[m])\qquad(\text{任意の対 }m,\ \text{`translate\_snoc\_increase`, Isabelle ✓}) $$

の対偶 `translate_butlast_decrease`（末尾削除で減少）から従う。
`translate_snoc_increase` は `translate` の再帰に沿う帰納で、`takeWhile`/`dropWhile`
の末尾追加補題を用いて証明する（PrSS `omap_snoc_increase` 相当）。

**bad ケース（Isabelle ✓, `translate_oper_bad`）。** $j_1=\mathrm{Lng}\,M-1$, 親 $j_0$, 良部
$G=\mathrm{take}\,j_0\,M$, 悪部 $B=(M_j)_{j=j_0}^{j_1-1}$, 末尾 $\mathit{last}=M_{j_1}$
とすると $M=G\oplus B\oplus(\mathit{last})$, $M[n]=G\oplus\bigoplus_{k=0}^{n-1}B_k$,
$B_k=((M_{0,j}+k\delta_0,\,M_{1,j}))_{j=j_0}^{j_1-1}$。示すべきは

$$ \mathrm{translate}\Bigl(G\oplus\bigoplus_{k} B_k\Bigr)\ \prec\ \mathrm{translate}\bigl(G\oplus B\oplus(\mathit{last})\bigr). $$

**bad ケースは $i_1$ で2つに分かれる（重要）。**

- **$i_1=0$**（末尾 $=(\text{正},0)$、$\delta_0=0$）: コピーは**正確な複製** $B^n$。
  $B$ の根 $M_{j_0}$ は同じ行0で $n$ 回現れるので**兄弟**となり、構造は PrSS と同型。
  減少は PrSS の `omap_core`（末尾が悪根の部分木に取り込まれ大きい項を作る／コピーは
  先頭指数が小さい）を添字付きへ移す。**単一木性は成り立たない。**
- **$i_1=1$**（末尾の行1 $>0$、$\delta_0>0$）: コピーは行0上昇で入れ子になり、以下の
  単一木機構が成り立つ（$n$ の帰納は不要）。

$i_1=1$ の機構：

1. **単一木性〔`translate_single_tree`, Isabelle ✓〕。** 悪部の根 $M_{j_0}$ の行0を
   $v_0$ とすると、$j_0$ は $j_1$ の行0
   先祖（$i_1{=}1$ では `nextrel1` が `le0` を要求）ゆえ $j_0<j\le j_1$ の全要素は
   行0 $>v_0$。コピーの行0上昇 $k\delta_0\ge0$ も $v_0$ を下げない。よって
   $B\oplus(\mathit{last})$ もコピー列も**先頭 $M_{j_0}$ を根とする単一の木**であり、
   $$ \mathrm{translate}(B\oplus(\mathit{last}))=P\,w_0\,A_M\,Z,\qquad
      \mathrm{translate}(\textstyle\bigoplus_k B_k)=P\,w_0\,A_n\,Z, $$
   ここで $w_0=M_{1,j_0}$（共通の先頭添字）。
2. **文脈合同（`BADCTX`）。** $G$ の長さに関する帰納で
   $$ \mathrm{translate}(Z_1)\prec\mathrm{translate}(Z_2)\ \Longrightarrow\ \mathrm{translate}(G\oplus Z_1)\prec\mathrm{translate}(G\oplus Z_2) $$
   （$Z_1,Z_2$ が同じ先頭 $M_{j_0}$ をもち、残りの行0 $>v_0$ のとき）。各 $G$-ステップで
   `takeWhile`/`dropWhile` の切れ目が $Z_1,Z_2$ で一致するため、比較が一段内側へ伝播する。
3. **コア＝添字優先支配。** $A_n=\mathrm{translate}(\mathrm{tl}\,\text{copies})$,
   $A_M=\mathrm{translate}(\mathrm{tl}(B\oplus(\mathit{last})))$。
   $\mathrm{tl\,copies}=\mathrm{tl}\,B_0\oplus(B_1\oplus\cdots)$,
   $\mathrm{tl}(B\oplus(\mathit{last}))=\mathrm{tl}\,B_0\oplus[\mathit{last}]$。共通の
   $\mathrm{tl}\,B_0$ に再び `BADCTX` を適用すると、$B_1\oplus\cdots$ の根の行0は
   $v_0{+}\delta_0=M_{0,j_1}=\mathit{last}$ の行0と一致（同根）、かつ $B_1\oplus\cdots$ の
   先頭添字は $w_0=M_{1,j_0}$、$\mathit{last}$ の添字は $w=M_{1,j_1}$ で
   `nextrel1` より $w_0<w$。よって `olt_P_of_lead_lt` で $B_1\oplus\cdots\prec[\mathit{last}]$、
   `BADCTX` で $A_n\prec A_M$。$n$・上昇量に依らず一様。

**コアは両 $i_1$ とも既存補題のみで閉じる（PrSS `omap_core` の移植は不要）。**

- $i_1=0$: $\mathrm{translate}(\text{copies})=\mathrm{translate}(B^n)
  =P\,w_0\,(\mathrm{translate}(\mathrm{tl}\,B))\,(\cdots)$,
  $\mathrm{translate}(B\oplus(\mathit{last}))=P\,w_0\,(\mathrm{translate}(\mathrm{tl}\,B\oplus[\mathit{last}]))\,Z$。
  引数 $\mathrm{tl}\,B\prec\mathrm{tl}\,B\oplus[\mathit{last}]$（`translate_snoc_increase`）より
  `olt_P_b` で $\prec$。コピー数 $n$ は末尾 $c$ に入り効かない。
- $i_1=1$: 上記 1–3（単一木＋`BADCTX`＋`olt_P_of_lead_lt`）。
- いずれも `translate_ctx_cong`（根が最小という弱条件版、$i_1{=}0$ の兄弟コピーにも適用可）で
  良部 $G=\mathrm{take}\,j_0\,M$ を通して $\mathrm{translate}(M[n])\prec\mathrm{translate}(M)$ に持ち上げる。

残りは `oper` の具体構造（`take`/`concat`/`map`/`upt`）と上記抽象補題の接続（機械的）。

---

## 5. 整礎性の還元（Isabelle ✓, `wf_Rnf_from_diag`）

整礎性の対象を $\mathrm{NF}:=\mathrm{translate}(\mathrm{ST_{PS}})$、その上の関係を
$R_{\mathrm{NF}}:=\{(v,u)\mid v\prec u\wedge u\in\mathrm{NF}\wedge v\in\mathrm{NF}\}$ とする。
標準形 $\mathrm{ST_{PS}}$（[`def.thy`](def.thy)）は「対角列 $\mathrm{diagSeq}\,0\,v$」と
「展開 $M\mapsto M[n]$」の2規則で生成される帰納的集合である。accessibility（`acc`）が
$R_{\mathrm{NF}}$ について**下方閉**であること（`acc_downward`）と、$\mathrm{ST_{PS}}$ 上の
帰納から、次が成り立つ：

- **展開規則**：減少補題 §4 より $\mathrm{translate}(M[n])\prec\mathrm{translate}(M)$、
  すなわち $(\mathrm{translate}(M[n]),\mathrm{translate}(M))\in R_{\mathrm{NF}}$。よって親
  $\mathrm{translate}(M)$ が accessible ならば下方閉性により $\mathrm{translate}(M[n])$ も
  accessible（`acc_Rnf_of_ST_PS`）。
- **対角規則**：基点はすべて $(0,0)$ 始まりの対角列 $\mathrm{diagSeq}\,0\,v$。

ゆえに整礎性は、対角タワーの accessibility ただ一つに還元される：

> **還元定理（`wf_Rnf_from_diag`, Isabelle ✓）。** すべての $v$ について
> $D(v):=\mathrm{translate}(\mathrm{diagSeq}\,0\,v)=p_0(p_1(\cdots p_v(0)))$ が
> $R_{\mathrm{NF}}$-accessible ならば、$R_{\mathrm{NF}}$ は整礎（$\mathrm{wf}\,R_{\mathrm{NF}}$）。

すなわち展開側（$\mathrm{NF}$ の大半）は減少補題により自動的に処理され、残る仮定は

$$ \textbf{(diagacc)}\qquad \forall v.\ D(v)\in\mathrm{acc}\,R_{\mathrm{NF}} $$

のみである。

---

## 6. 停止性（Isabelle ✓, 仮定 (diagacc) の下で）

減少（§4, `m_step_decreases`）と整礎性の還元（§5）から、1ステップ関係

$$ \{(T,M)\mid M\in\mathrm{ST_{PS}}\wedge \mathrm{step}\,M\,T\}\ \subseteq\ \mathrm{translate}^{-1}\!\bigl(R_{\mathrm{NF}}\bigr) $$

が成り立つ（`step` は `ST_PS` 内に閉じる `step_in_ST_PS`、各ステップで減少）。右辺は
整礎関係の逆像（`wf_inv_image`）、`wf_subset` で `step` も整礎。よって：

> **停止性（`no_infinite_expansion_from_diag`, Isabelle ✓）。** 仮定 (diagacc) の下で、
> $\mathrm{ST_{PS}}$ 上に無限展開列は存在しない。

減少は既に discharge されており、本含意の唯一の仮定は (diagacc) である
（`step_terminates_from_diag` / `no_infinite_expansion_from_diag`）。

---

## 7. 整礎性の証明（pure-lex 構文的・順序数なし、[`wf.thy`](wf.thy)）

§6 で停止性は **wfimg**（$\mathrm{NF}=\mathrm{translate}\,\text{«}\,\mathrm{ST_{PS}}$ 上の
$\prec$ 整礎性、`wf Rnf`）一点に帰着した。本証明はこれを**順序数を一切使わず構文的帰納**で
与える。鍵は「最大添字 `maxsub` による階層化」である。

**(1) maxsub 単調性（Isabelle ✓, `maxsub_mono_NF'`）。**
NF 項の左スパイン（最左引数の添字列）は不変条件 `inv2` で $0,1,\dots,\mathrm{maxsub}$ から
始まり、各添字は maxsub 以下（`nfinv`、`nfinv_ST_PS` で全標準形に成立）。`olt` はスパインの
辞書式順序を refine する（`olt_imp_slex`）ので、
$$ w\prec x \ \Longrightarrow\ \mathrm{maxsub}\,w \le \mathrm{maxsub}\,x \qquad (w,x\in\mathrm{NF}). $$

**(2) CNF（Isabelle ✓, `cnf_ST_PS`）。** 全標準形は Cantor 標準形（兄弟主要項が非増加）に
翻訳される（`cnf`、展開保存 `cnf_oper`、対角 `cnf_diag`）。`cnf_tops_le`：トップレベルの
$+$ 連鎖の添字は先頭で上から押さえられる。

**(3) レベル内還元（Isabelle ✓, `wf_Rnf_from_within_level`）。**
maxsub 単調性で $R_{\mathrm{NF}}$ を「maxsub 減少部」（`maxsub` への逆像で自明に整礎）と
「maxsub 同値部」に分割し、`wf_union_compatible` で
$$ \textbf{wfE}\quad \mathrm{wf}\{(w,x)\mid w\prec x \wedge w,x\in\mathrm{NF}\wedge \mathrm{maxsub}\,w=\mathrm{maxsub}\,x\} \ \Longrightarrow\ \mathrm{wf}\,R_{\mathrm{NF}}. $$

**(4) 和・添字の層の剥離（Isabelle ✓, [`wfsum.thy`](wfsum.thy)）。**
レベル内の比較は、CNF 和の summand 多重集合の Dershowitz–Manna 拡張に埋め込まれ
（`olt_summands_mult`）、添字層は辞書積で剥がれる（`wf_SingA`）。レベル0（全添字0）は
PrSS と同じ accessibility 構成で完全証明（`wf_olt0`）。残る唯一の sorry は
**`wf_ArgsA`（レベル m 引数クラスの整礎性＝Buchholz 崩壊核）**。

**(5) 補助柱（いずれも sorry なしで証明済）。**

- **柱2 `wf_olt_wf3`（[`ord/otembed.thy`](ord/otembed.thy), session PSI）**：
  pure-lex `≺` は Buchholz (1986) §2 の OT の順序そのものであり、OT クラス（`wf3`：
  G 条件＋非増加和）上では値写像 $o$（自前の ψ 意味論 [`ord/psi.thy`](ord/psi.thy)）が
  厳密単調になる——すなわち **Buchholz Lemma 2.2 の自前証明**。文献引用なし。
- **柱3 `olt_ST_iff_seqlex`（[`seqlex.thy`](seqlex.thy)）**：標準形上で
  `translate` は**列 lex 順序からの順序同型**。ゆえに wfE は「標準形ペア数列の
  列 lex 無限降下なし」という BMS ネイティブな主張と同値。

崩壊核は次のいずれかで閉じれば停止性が完結する：(α) `wf_ArgsA` の独自帰納、
(β1) NF→`wf3` の順序保存変換（P進 Trans 級）、(β2) ST_PS→`wf3` 翻訳＋展開減少。
詳細・経緯は [`memo.md`](memo.md)。

> **現状（2026-06-10）**: 停止性 `PSS_terminates` は **`wf_ArgsA` ただ一つ**の補題に帰着
> （live チェーンの sorry はこれ1個のみ）。柱2・柱3 は sorry なしで完成。

---

## 8. Isabelle 形式化との対応（現状）

| 対象 | Isabelle | 状態 |
|---|---|---|
| §5 定義, $M[n]$, `ST_PS`, `step` | [`def.thy`](def.thy) | ✓ |
| 記法 $\mathsf{three}$（$Z$, $P\,a\,b\,c$） | `datatype three` | ✓ |
| 添字優先順序 $\prec$ | `olt` (`<o`) | ✓ |
| 線形性 | `olt_irrefl`/`olt_trans`/`olt_total` | ✓ |
| $\mathrm{translate}$ | `translate` | ✓ |
| task の例 | 各 sanity 補題 | ✓ |
| 項の添字集合, 添字の出所 | `subs` / `subs_translate` | ✓ |
| 添字単調性（M[n]の添字 ⊆ Mの行1） | `oper_snd_subset` | ✓ |
| 末尾追加で増大 / 削除で減少 | `translate_snoc_increase` / `translate_butlast_decrease` | ✓ |
| 先頭添字支配 | `lead` / `olt_P_of_lead_lt` | ✓ |
| 文脈合同 BADCTX | `translate_ctx_cong` | ✓ |
| 単一木 / 区間補題 | `translate_single_tree` / `le0_interval_gt` | ✓ |
| bad コア i1=0 / i1=1 | `core_i0` / `core_i1` | ✓ |
| 減少（Pred / bad / 総合） | `translate_oper_pred` / `translate_oper_bad` / **`m_step_decreases`** | ✓ |
| 停止性（wfimg ⟹ 停止） | **`step_terminates`** / `no_infinite_expansion` | ✓ |
| 整礎性の還元（diagacc ⟹ wfimg） | **`wf_Rnf_from_diag`** / `acc_Rnf_of_ST_PS` / `oper_eq_self_short` | ✓ |
| 停止性（diagacc ⟹ 停止） | `step_terminates_from_diag` / `no_infinite_expansion_from_diag` | ✓ |
| **整礎性 (pure-lex, 順序数なし)** maxsub 単調 | [`wf.thy`](wf.thy) `olt_imp_slex` / `nfinv_ST_PS` / `maxsub_mono_NF'` | ✓ |
| CNF（標準形 ⟹ CNF） | `cnf` / `cnf_ST_PS` / `cnf_oper` / `cnf_tops_le` | ✓ |
| wfimg をレベル内に還元 | **`wf_Rnf_from_within_level`** / `wf_Rnf` | ✓ |
| 和の層の剥離（multiset 拡張） | [`wfsum.thy`](wfsum.thy) `olt_sum_mult` / `wfE_from_args` | ✓ |
| 一般 summand peel ＋添字 peel | `olt_summands_mult` / `wf_SingA` | ✓ |
| レベル0（全添字0）の整礎性 | `wf_olt0`（PrSS 流 accessibility） | ✓ |
| 停止性（pure-lex 経路） | **`PSS_terminates`** (= `step_terminates[OF wf_Rnf]`) | ✓（`wf_ArgsA` に依存） |
| 引数クラスの整礎性（崩壊核） | `wf_ArgsA` | 作業中・唯一の sorry [`memo.md`](memo.md) |
| 柱2: Buchholz Lemma 2.2 自前証明 | [`ord/psi.thy`](ord/psi.thy) ψ 意味論 ＋ [`ord/otembed.thy`](ord/otembed.thy) **`wf_olt_wf3`** | ✓ |
| 柱3: 標準形上の順序同型（列 lex） | [`seqlex.thy`](seqlex.thy) `blockok_ST_PS` / **`olt_ST_iff_seqlex`** | ✓ |

## 9. 新本線：値正規化 `nrm` による NF→OT 順序埋め込み（[`ord/nrm.thy`](ord/nrm.thy)）

§7 の剥離は最後に「崩壊核」`wf_ArgsA` が残った（凍結）。代わりに次の一手で
本丸を狙う：**小さな構文的正規化 `nrm` を定義し、`NF` を Buchholz の OT クラス
（`wf3`）へ順序を保って写す**。すると柱2（`wf_olt_wf3`）から直ちに `wf Rnf` が出る。

- `nrm` の中身（約40行）：主要項 `p_a(b)` で、`b` の中の「臨界部分項」
  `G_a(b)`（添字 ≥ a の主要項の引数たち）に `b` 以上のものがあれば、その最大元へ
  `b` を置き換える（ψ_a の値が変わらない名前の書き換え。例：
  `nrm(p0(p1(p2(0)))) = p0(p2(0))`、つまり ψ₀ψ₁ψ₂(0) = ψ₀ψ₂(0)）。
  和は「後ろにより大きい項があれば吸収」。これを再帰的に行う。
- 数列側の意味：`proj` は「セグメントの最大 row1 列からの接尾辞切り出し」に対応
  （実証 580/580 一致）。つまり nrm は P進の Trans（挿入修復・条件I-VI）より
  はるかに軽い「構造射影」で同じ橋を架ける。
- 実証：標準形の translate と全遺伝ブロック 2,643,843 ペアで順序保存違反 0。
  反例は非標準でのみ発生（y₂ = translate((0,0)(1,1)(2,0)(3,1)(4,1))、非標準）
  ＝標準性の行1親子規律が本質的に必要。
- 残る証明義務（sorry）：
  - `nrm_step_dec`：展開ステップでの減少 `nrm(translate(M[n])) <o nrm(translate M)`
    （これだけで **PSS_terminates** が閉じる。単一ホストの生成帰納で攻める）
  - `nrm_order_pres`：NF 上の全ペア順序保存（より強い目標。`wf Rnf` まで閉じる）。

### 9.1 E6 アーキテクチャ（`ord/nrmstep.thy`、2026-06-10〜11）

Pred ケースの攻略は **msfx 接尾辞定理（E6）** を軸に再編された。中心となる事実：

> **E6（射影＝接尾辞切出し）**: 標準ホストの支配セグメント `S` とホストレベル
> `u` について、射影が発火するとき
> `proj u (nrm (translate S)) = nrm (translate (msfx S))`。
> ここで `msfx S` は「S の最初の最大 row1 列からの接尾辞」。

証明済みの主要部品（全て緑）：
- **proj_once**：射影は1ステップで終わる（max 臨界は自分が発火しない）
- **C1層**：`blockok` から和-隣接ペアのレベル固定（`fbseg_hd_level`）→ 無吸収
  （`NT_dom`→`NT_shape`）→ 頭添字保存・和尾部厳密増大（`NT_tail_lt`）
- **GCAT（G-カタログ）**：正規化像の臨界は全て「S の連続部分片の NT 像」か `Z`
- **E6_value**：proj_once + maxo 最大性 + カタログ + 低添字支配からのコンビネータ
- **E6_hdom / E6_dom_tie / E6_mem の resolved 版**：排除・支配・所属の組立
  （補題レベルの循環は長さ層化で非循環＝最終組立は同時帰納にインライン）
- **snocok 機構の post 一般化**：内部位置 snoc 単調性 `nrm_snoc_mid` /
  接頭辞厳密増大 `NT_prefix_lt`
- **r1ok（row1 規律）**：標準列の全列は row0-親に対し `snd ≤ 親 snd + 1`
  （生成帰納で証明、コピー証人の簿記込み。残: `r1ok_climb` 1点）

### 9.2 SIB 核の解体（2026-06-11）

長らく全攻略経路が合流していた「添字タイの兄弟引数比較」（SIB 核）は、
順序論を一切含まない配列形状不変量に完全還元された：

> **sibm（兄弟ラン不変量）**: 標準列の隣接タイ兄弟対（同レベル・同 row1、
> level > 0）について、後続のラン は先行のランと**等しいか真の接頭辞**であり、
> 両ランとも**頭最大**（先頭列が最大 row1 を実現）。実証 2964 対で違反 0。

この不変量から SIB_shape（ピース版）→ NT_tie が導出済み（切詰め安定性
`sibm_take` 込み、全て緑）。無発火条件は E6_hdom から、接頭辞の厳密増大は
`NT_prefix_lt`（内部位置 snoc 単調性の連鎖）から出る。

また **r1ok（row1 規律）**：「全列の row1 ≤ row0-親の row1 + 1」（実証 0/14,558）
を生成帰納で証明（コピー証人の簿記込み、残 1 点 r1ok_climb のみ）。
これが行レベル事実群（q-cut で snd q = maxr1+1 等）の土台になる。

残る sorry は全て「first-max 優先」という単一テーマの変種（コピー簿記保存
sibm_oper_bad・fire カスケード・深部タイ・行レベル配置排除）で、実証 0 違反の
正確なステートメント＋証明地図としてスコープ済み（`memo.md` 続19〜続28）。

---

## 出典・引用 (Reference)
- W. Buchholz, "[A new system of proof-theoretic ordinal functions](https://www.sciencedirect.com/science/article/pii/0168007286900527)", Annals of Pure and Applied Logic, Volume 32, 1986, pp. 195–207.
- Bashicu, "[BASIC 言語による巨大数のまとめ](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:BashicuHyudora/BASIC%E8%A8%80%E8%AA%9E%E3%81%AB%E3%82%88%E3%82%8B%E5%B7%A8%E5%A4%A7%E6%95%B0%E3%81%AE%E3%81%BE%E3%81%A8%E3%82%81?oldid=15603&useskin=oasis)", [巨大数研究 Wiki](http://ja.googology.wikia.com/) ユーザーブログ, 2015.8.21.（ペア数列システムの考案）
- P進大好きbot. "[ペア数列の停止性](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E3%81%AE%E5%81%9C%E6%AD%A2%E6%80%A7)", [巨大数研究 Wiki](http://ja.googology.wikia.com/) ユーザーブログ, 2018.11.11.（ペア数列の停止性の証明。本リポジトリの PSS 定義もこの論文に倣う）
