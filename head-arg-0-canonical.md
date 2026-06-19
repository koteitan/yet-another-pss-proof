# 命題:畳まれた標準形像の先頭引数は 0-正準

ya-pss(ペア数列システム停止性証明)で現在追っている唯一の本質的未証明命題。

## 記号の定義（すべて木に関する再帰）

木 $t$ は2種類:$t = 0$、または $t = P\,a\,b\,c$（ここで $a\in\mathbb N$ は添字、$b,c$ は木）。

先頭添字 $\mathrm{lead}$、先頭引数 $\mathrm{harg}$:

$$\mathrm{lead}(0)=0,\qquad \mathrm{lead}(P\,a\,b\,c)=a,$$
$$\mathrm{harg}(0)=0,\qquad \mathrm{harg}(P\,a\,b\,c)=b.$$

順序 $<$（辞書式、$0$ が最小）:

$$0 < P\,a\,b\,c,\qquad P\cdots \not< 0,$$
$$P\,a_1\,b_1\,c_1 < P\,a_2\,b_2\,c_2 \iff a_1<a_2 \ \lor\ (a_1{=}a_2 \land b_1<b_2)\ \lor\ (a_1{=}a_2\land b_1{=}b_2\land c_1<c_2).$$

レベル $u$ の臨界部分木の集合 $G_u$（$u\in\mathbb N$）:

$$G_u(0)=\varnothing,$$
$$G_u(P\,a\,b\,c)=\big(u\le a\ \text{なら}\ \{b\}\cup G_u(b)\ \text{、否なら}\ \varnothing\big)\ \cup\ G_u(c).$$

$u$-違反子:$g$ が $t$ の $u$-違反子 $\overset{\text{def}}{\iff}\ g\in G_u(t)\ \land\ \lnot(g<t)$（つまり $g\ge t$ なのに臨界に居る)。

射影（畳み込み） $\mathrm{proj}_u$:

$$\mathrm{proj}_u(t)=\begin{cases}t & (t\ \text{に}\ u\text{-違反子が無い)}\\[2pt]\mathrm{proj}_u(m) & (m = t\ \text{の}\ u\text{-違反子のうち}\ <\text{-最大、を再帰})\end{cases}$$

正規化 $\mathrm{nrm}$:

$$\mathrm{nrm}(0)=0,\qquad \mathrm{nrm}(P\,a\,b\,c)=\mathrm{ins}_a\big(\mathrm{proj}_a(\mathrm{nrm}\,b),\ \mathrm{nrm}\,c\big)$$

（$\mathrm{ins}_a(x,t)$ は「ブロック $P\,a\,x$」を $t$ の整列位置に挿入）。

対象クラス $\mathcal N$:

$$\mathcal N=\{\,\mathrm{nrm}(\mathrm{translate}\,M)\ :\ M\ \text{は標準形 PSS 状態の引数帯}\,\}$$

（$\mathrm{translate}$ = 数列→木 の変換、標準形 = PSS で到達可能な状態。$M$ の引数帯 = 先頭列を除いた行0が正の前半部分。）

## いま追っている命題

$$\boxed{\ \forall X\in\mathcal N.\quad \mathrm{proj}_0(X)\neq X\ \Longrightarrow\ \mathrm{proj}_0(\mathrm{harg}\,X)=\mathrm{harg}\,X\ }$$

「$\mathcal N$ の木 $X$ が（$\mathrm{proj}_0$ で）畳まれるなら、その先頭引数 $\mathrm{harg}\,X$ はもう畳めない（0-正準）」。

## 還元の現状（2026-06-19, maxsub-spine split 統合済・PSI green）

⚠️ **訂正**:当初の「(S1) 発火像は単一主項 $X=P\,L\,b\,Z$」は **深層で偽**（closure+5・1M ST で 4/266594 反例。$M=(0,0)(1,1)(2,2)(1,1)(2,2)$ 型で $X=D_1(D_2 0)+D_1(D_2 0)$ = 反復主項の和）。bridge_probe の corpus（16303 ST）が浅く見逃した。第7・8事件型。

**健全な還元**（反復主項でも成立、深層 0/266594 で検証）— `argzone_head_maxviol` は今これで**証明済**:
- **(S2′ 集合)**:$G_0(X)=\{\mathrm{harg}\,X\}\cup G_0(\mathrm{harg}\,X)$（反復主項は同一ゆえ新 critical を増やさない）。
- **maxsub-spine**:発火 $\iff \mathrm{lead}\,X<\mathrm{maxsub}\,X$、$\mathrm{lead}(\mathrm{harg}\,X)=\mathrm{maxsub}\,X$。
- 非 tied 部（$\mathrm{lead}\,g<\mathrm{lead}(\mathrm{harg}\,X)$）は class-free 緑（G1: $g\in G_0(X)\Rightarrow\mathrm{maxsub}\,g\le\mathrm{maxsub}\,X$）。
- **残る壁 = `tied_crit_lt_hb`**（tied lead の $G_0$-critical $<\mathrm{harg}\,X$ = $\mathrm{harg}\,X$ の 0-正準性）。class-essential。

BMOCF/行列 `parent_index`(=`≤_M`)への輸送は subscript shear で壁を**移すだけ**（行列部分列の正規化は fresh context で別物、bridge_probe 3988/0）。本道は `tied_crit_lt_hb` の **木内部 pure-lex 構文帰納**。

## 備考

- **同値な形（最大違反子）**:$\ \forall g.\ g\in G_0(X)\ \land\ \lnot(g<X)\ \Longrightarrow\ \lnot(\mathrm{harg}\,X<g)$（$\mathrm{harg}\,X$ は $X$ の $0$-違反子のうち $<$-最大）。
- **クラスを外すと偽**:任意の木では $\mathrm{proj}_0(\mathrm{harg}\,X)\neq\mathrm{harg}\,X$ となる反例がある（添字0の浅い所に大きい添字の部分木が埋もれる型）。標準形クラス $\mathcal N$ の規律が本質。
- **実測**:標準形像 266545 件（発火例）で反例 0、深層閉包 1,013,172 標準形。
- **Isabelle 対応**:`ord/nrm.thy` の sorry `tied_crit_lt_hb`（および等価な `argzone_head_maxviol`）。これが閉じれば `sigma_seqlex_mono` / `oV_mono_NF` 経由で PSS 停止性が完成。
- **既証明の周辺**:非 tied 部（$\mathrm{lead}\,g<\mathrm{lead}(\mathrm{harg}\,X)$）は $G_0$ の最大添字単調性 $g\in G_0(X)\Rightarrow \mathrm{maxsub}\,g\le\mathrm{maxsub}\,X$ で緑。残る難所は同点 $\mathrm{lead}\,g=\mathrm{lead}(\mathrm{harg}\,X)$ の場合。
