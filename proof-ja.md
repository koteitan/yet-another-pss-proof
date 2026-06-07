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
をペア数列へ一般化したものである。Buchholz の ψ への変換とは異なる記法を用いる。

PSS の証明論的強さは **ψ₀(ψ_ω(0))**（Buchholz ordinal, Ω_ω の崩壊）と
考えられており、記法 `p_a(b)` の添字 `a` を自然数（0,1,2,… とその上限 ω）に
取ることに対応する。

> **記法の凡例**: 本稿には Isabelle/HOL で形式化された証明本文のみを記す（`def.thy`
> / `mechanized.thy` / `proofs.thy`、`isbman build -d . -v YAPSS` で検証済み）。
> 最終段の整礎性は、証明済みの含意により**ただ一つの仮定**（対角タワーの
> accessibility）に還元される。本稿はその含意までを扱い、当該仮定を明示する。

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
（`step_terminates_from_diag` / `no_infinite_expansion_from_diag`）。仮定 (diagacc) の
証明に向けた作業メモは [`memo.md`](memo.md) に分離する。

---

## 7. Isabelle 形式化との対応（現状）

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
| 仮定 (diagacc)：対角タワー $D(v)$ の accessibility | （含意の仮定） | [`memo.md`](memo.md) |

---

## 出典・引用 (Reference)
- W. Buchholz, "[A new system of proof-theoretic ordinal functions](https://www.sciencedirect.com/science/article/pii/0168007286900527)", Annals of Pure and Applied Logic, Volume 32, 1986, pp. 195–207.
- Bashicu, "[BASIC 言語による巨大数のまとめ](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:BashicuHyudora/BASIC%E8%A8%80%E8%AA%9E%E3%81%AB%E3%82%88%E3%82%8B%E5%B7%A8%E5%A4%A7%E6%95%B0%E3%81%AE%E3%81%BE%E3%81%A8%E3%82%81?oldid=15603&useskin=oasis)", [巨大数研究 Wiki](http://ja.googology.wikia.com/) ユーザーブログ, 2015.8.21.（ペア数列システムの考案）
- P進大好きbot. "[ペア数列の停止性](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E3%81%AE%E5%81%9C%E6%AD%A2%E6%80%A7)", [巨大数研究 Wiki](http://ja.googology.wikia.com/) ユーザーブログ, 2018.11.11.（停止性の証明。本証明とは無関係な別証明）
- koteitan, "[Purely mathematical definition of BMS](https://googology.fandom.com/wiki/User_blog:Koteitan/Purely_mathematical_definition_of_BMS)", [巨大数研究 Wiki](http://ja.googology.wikia.com/) ユーザーブログ.（定義の参照）
