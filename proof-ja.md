[README](README-ja.md)

# ペア数列システムの停止性（`p_a(b)+c` アプローチ）

**ペア数列システム (Pair Sequence System, PSS) は Bashicu 氏が考案した**。
その停止性は **P進大好きbot 氏が証明した**（Buchholz の ψ を用いる）が、
**本証明はそれとは無関係な独立のオリジナル証明である**（同氏の手法・補題には依拠しない）。

本証明はペア数列を独自のオーダー記法 `p_a(b)+c` へ変換 (`translate`) し、
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

> **減少補題（`m_step_decreases`）。** $M\in\mathrm{ST_{PS}}$, $\mathrm{Lng}\,M>1$,
> $n\ge1 \Rightarrow \mathrm{translate}(M[n])\prec\mathrm{translate}(M)$。

**Pred 2 ケース（Isabelle ✓, `translate_oper_pred`）。** 末尾対が $(0,0)$、または
行 $i_1$ に一意の親が無いとき $M[n]=\mathrm{Pred}\,M=\mathrm{butlast}\,M$ なので、
**末尾追加で測度が真に増大**する補題

$$ \mathrm{translate}\,C \prec \mathrm{translate}\,(C\mathbin{@}[m])\qquad(\text{任意の対 }m,\ \text{`translate\_snoc\_increase`, Isabelle ✓}) $$

の対偶 `translate_butlast_decrease`（末尾削除で減少）から従う。
`translate_snoc_increase` は `translate` の再帰に沿う帰納で、`takeWhile`/`dropWhile`
の末尾追加補題を用いて証明する（PrSS `omap_snoc_increase` 相当）。

**bad ケース（未了, 本丸）。** $j_1=\mathrm{Lng}\,M-1$, 親 $j_0$, 良部
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

**整礎性の還元——対角タワー accessibility（Isabelle ✓ `wf_Rnf_from_diag`）。**
accessibility（`acc`）は順序で**下方閉**である（`acc_downward`）。$\mathrm{ST_{PS}}$ は
「対角列 $\mathrm{diagSeq}\,u\,v$」と「展開 $M\mapsto M[n]$」の2規則で生成される
帰納的集合だから、$\mathrm{ST_{PS}}$ 上の帰納で次が言える：

- **対角規則**：$\mathrm{translate}(\mathrm{diagSeq}\,u\,v)$ が accessible（これが残る仮定）。
- **展開規則**：減少補題 §4 より $\mathrm{translate}(M[n])\prec\mathrm{translate}(M)$、すなわち
  $(\mathrm{translate}(M[n]),\mathrm{translate}(M))\in R_{\mathrm{NF}}$。よって親
  $\mathrm{translate}(M)$ が accessible なら下方閉性で $\mathrm{translate}(M[n])$ も
  **自動的に** accessible。

ゆえに整礎性 `wfimg` 全体は、ただ一つの残余事実に**崩壊**する：

> **残る本質的核。** すべての対角タワー
> $D(u,v)=\mathrm{translate}(\mathrm{diagSeq}\,u\,v)=p_u(p_{u+1}(\cdots p_v(0)))$
> （$u\le v$）が $R_{\mathrm{NF}}$-accessible である。

これにより**展開側（NF の大半）は減少補題で無料で片付き**、ψ崩壊レベルの本質的内容は
対角タワーのみに鋭く隔離される。

**整礎性の難所が安く回避できないことの確認（経験的）。**

- bad chain $x_n=p_0^{\,n}(p_1(0))$ は $n\le1$ のみ到達可能で **$n\ge2$ は到達不能**
  （`reach_badchain.py`, 20913 状態）。ゆえに無限降下列 $x_0\succ x_1\succ\cdots$ は
  $\mathrm{NF}$ に入らず、$\prec$ は $\mathrm{NF}$ 上で整礎な見込み。ただし
  $\mathrm{NF}$ の**構文的特徴づけは存在しない**（`bms.c` の `-s`＝`isstd` は到達可能性の
  決定手続きのみ、原論文にも標準形の閉形式なし）。
- 最大添字での階層化は**不可**：$\mathrm{NF}$ 内で「$w\prec x\Rightarrow\max\text{添字}(w)\le\max\text{添字}(x)$」
  は**偽**（`maxsub_test.py` で 576868 件違反、例 $p_2(\cdots\!4\!\cdots)\prec p_3(\cdots)$）。
  根添字 `lead` のみ非増加だが、単独では整礎測度にならない。

**現状認識。** PSS の強さ $\psi_0(\psi_\omega(0))$ ゆえ、対角タワー accessibility は
本質的に Buchholz の $\psi$（崩壊関数）の整礎性と同等の内容をもつ。`p_a(b)+c` 化と
上記還元により、**減少側は完全に証明済み**で、形式化に残るのは対角タワーの
accessibility（Buchholz $\psi$ 整礎性）のみに集約された。

---

## 6. 停止性の組み立て（Isabelle ✓, `step_terminates`）

減少（§4, `m_step_decreases`, 証明済み）と NF 上の整礎性（§5, `wfimg`, 未了）から、

$$ \{(T,M)\mid M\in\mathrm{ST_{PS}}\wedge \mathrm{step}\,M\,T\}\ \subseteq\ \mathrm{translate}^{-1}\!\bigl(\prec|_{\mathrm{NF}}\bigr) $$

（`step` は `ST_PS` 内に閉じる `step_in_ST_PS`、各ステップで減少）。右辺は整礎関係の逆像
（`wf_inv_image`）ゆえ整礎、`wf_subset` で `step` も整礎。すなわち
**`wfimg` さえ示せれば、無限展開列は存在しない（停止性）**。減少は既に discharge 済みで、
`step_terminates` / `no_infinite_expansion` は `wfimg` のみを仮定する。

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
| 項の添字集合, 添字の出所 | `subs` / `subs_translate` | ✓ |
| 添字単調性（M[n]の添字 ⊆ Mの行1） | `oper_snd_subset` | ✓ |
| 末尾追加で増大 / 削除で減少 | `translate_snoc_increase` / `translate_butlast_decrease` | ✓ |
| 先頭添字支配 | `lead` / `olt_P_of_lead_lt` | ✓ |
| 文脈合同 BADCTX | `translate_ctx_cong` | ✓ |
| 単一木 / 区間補題 | `translate_single_tree` / `le0_interval_gt` | ✓ |
| bad コア i1=0 / i1=1 | `core_i0` / `core_i1` | ✓ |
| 減少（Pred / bad / 総合） | `translate_oper_pred` / `translate_oper_bad` / **`m_step_decreases`** | ✓ |
| 停止性（wfimg ⟹ 停止） | **`step_terminates`** / `no_infinite_expansion` | ✓ |
| wfimg → 対角 accessibility 還元 | **`wf_Rnf_from_diag`** / `acc_Rnf_of_ST_PS` / `oper_eq_self_short` | ✓ |
| 停止性（対角 accessibility ⟹ 停止） | `step_terminates_from_diag` / `no_infinite_expansion_from_diag` | ✓ |
| 対角タワー accessibility（ψ崩壊） | — | **未了（残る唯一の本質的核）** |

---

クレジット：ペア数列システムの考案は Bashicu 氏。その停止性の証明は
P進大好きbot 氏「ペア数列の停止性」巨大数研究 Wiki（本証明とは無関係な別証明）。
定義の参照：Koteitan「[Purely mathematical definition of BMS](https://googology.fandom.com/wiki/User_blog:Koteitan/Purely_mathematical_definition_of_BMS)」巨大数研究 Wiki。
