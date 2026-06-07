# 作業メモ（証明本文ではない）

このファイルは証明完成のための**作業メモ**である。経験的観察・戦略・未解決の核の
分析など、まだ証明になっていない事柄を置く。完成した証明本文は
[`proof-ja.md`](proof-ja.md) に書く（こちらには未証明・経験的事項を書かない、
循環論法防止のため）。

## 残る唯一の仮定 (diagacc)

[`proof-ja.md`](proof-ja.md) §5–§6 の通り、停止性は次の含意まで形式化済み
（`wf_Rnf_from_diag` / `no_infinite_expansion_from_diag`, Isabelle ✓）：

> **(diagacc)** すべての $v$ について対角タワー
> $D(v)=\mathrm{translate}(\mathrm{diagSeq}\,0\,v)=p_0(p_1(\cdots p_v(0)))$ が
> $R_{\mathrm{NF}}$-accessible。

これを証明すれば停止性が完成する。減少補題（§4）により展開側は無料なので、残るは
この (diagacc) のみ。内容的には **ψ₀(ψ_ω(0)) の整礎性**（Buchholz の崩壊関数の
整礎性）と同等。

## NF の構造（経験的観察、u=0 対角のみ）

`work/` の Python（`yaBMS/c/bms -v4` で展開）で、真の NF
（`diagSeq 0 v` から到達可能な列の `translate` 像）を調べた結果。**いずれも経験的**
（証明ではない）。

- 全状態が $(0,0)$ 始まり（`diag` を $u=0$ に修正した根拠。`def.thy` 修正済み）。
- **兄弟和は $\prec$ 非増加（CNF）**（違反 0）。
- **maxsub 単調**：$w\prec x\Rightarrow \max\text{添字}(w)\le\max\text{添字}(x)$（違反 0、`maxsub_u0.py`）。
- **built-from-below**：各引数の先頭添字 $\le$ 親添字 $+1$（違反 0）。

注意：上の不変条件は **u>0 対角を含めると全て壊れる**（CNF 違反 6906、maxsub 単調
違反 576868 等）。`def.thy` の `diag` を $(0,0)$ 始まり（`diagSeq 0 v`）に限定したのは
この理由（ユーザー確認済み：NF は (0,0), (0,0)(1,1), … から到達可能なもの）。

## cheap な道が無いことの確認

- 純 lex（添字優先）は**全 `three` 上では整礎でない**：
  $x_n=p_0^{\,n}(p_1(0))$ は $x_0\succ x_1\succ\cdots$ の無限降下列。
- だが $x_n$ は $n\le1$ のみ到達可能、$n\ge2$ は**到達不能**（`reach_badchain.py`,
  20913 状態）。よって $x_n$ は $\mathrm{NF}$ に入らず、$\prec$ は $\mathrm{NF}$ 上で
  整礎な見込み。
- **構文的 NF 述語は無い**：標準形判定は `bms.c` の `-s`＝`isstd`（到達可能性の
  決定手続き）のみで、閉じた構文形は存在しない（原論文にも無し）。
- 構文的超集合 `good`＝「CNF＋built-from-below」だけでは整礎にならない：上の $x_n$ は
  すべて `good` だが NF 外。よって `good` への埋め込みでは不十分。maxsub 単調も
  `good` では成り立たない（例 $p_0(p_0(p_1(p_2(0))))$ は good だが NF 外で maxsub を
  上げる）。→ maxsub 単調は NF 固有の性質で、単純な局所構文条件からは出ない。

## NF のスパイン構造（経験的、(diagacc) への鍵）

最左 b-スパインを `spine(P a b c)=a # spine(b)`, `spine(Z)=[]` とする。NF 項について
（`leftspine.py` / `inv2.py`, 違反 0）：

- (INV1) `maxsub(t) = max(spine(t))`：全添字（兄弟 c 側も含む）は最左スパインの最大以下。
- (INV2) `spine(t)` は `0,1,2,…,maxsub(t)` で始まる（最初の maxsub+1 項が `[0..maxsub]`）。
- 系：`a_i ≤ i`（根 0＋bfb の +1 以下から）。

**これらから maxsub 単調性が従う**：NF の `w ≺ x` は添字優先＝スパイン優先なので、
スパイン添字が最初に食い違う深さで勝敗が決まる。両スパインは `0,1,2,…` で始まるので、
初期登りが短い（maxsub が小さい）方がその深さで小さい添字をもち ≺ 側になる。ゆえに
`w ≺ x ⟹ maxsub(w) ≤ maxsub(x)`（兄弟 c 側は maxsub に効かない＝INV1 ゆえ、スパインで決まる）。

→ これで **maxsub による階層化帰納** が成立：`R_NF` 降下で maxsub 非増加。残るは
**同一 maxsub レベル内の整礎性**（Buchholz の「レベル n はレベル n-1 から構成」の段）。

形式化の段取り：
1. `spine`/`maxsub` を定義し、INV1・INV2 を `M∈ST_PS ⟹ translate M` で証明
   （ST_PS 帰納：対角は自明、oper の copy-with-ascension がスパイン構造を保つ）。
2. INV1・INV2 から maxsub 単調性（構文的補題）。
3. maxsub の strong induction で `wf R_NF`。同一レベル内の二次測度が要（本丸の残り）。

### 形式化の進捗（wf.thy, すべてビルド緑・コミット済）
- **順序核 (Stage 2 相当)**: `olt_imp_slex`（`w≺x ⟹ slex(spine w)(spine x)`、`≺` がスパイン lex を refine）、`climb_mono`、`maxsub_mono_cond`（不変条件下で maxsub 単調）。
- **スパイン再定式化**: `spine_translate_eq`: `spine(translate M)=map snd(incpref M)`、`incpref`＝行0狭義増加の最長接頭辞。`maxsub_translate`: `maxsub(translate M)=cmax(map snd M)`。`maxsub_eq_climb_iff`。
- これで NF 不変条件は純ペア数列命題に帰着:
  - (A) `cmax(map snd M)=cmax(map snd(incpref M))`、(B) `inv2(map snd(incpref M))`。
- 対角基底ケース: `spine_diagSeq0`/`climb_diagSeq0`/`inv2_spine_diagSeq0`。incpref 基本補題: `incpref_append`/`incpref_fst_sorted`/`incpref_snoc`/`incpref_butlast`/`incpref_append_stop`/`incpref_append_full`。
- **Stage 1 完了 ✅**: `nfinv` 述語＋`nfinv_append`（閉包）＋`nfinv_butlast`＋`nfinv_diag`＋`nfinv_ST_PS`（全 ST_PS で (A)∧(B)）。鍵: **`M[n]=butlast M @ R`（R の行1⊆butlast M）**〔`oper_eq_butlast_append`/`oper_bad_eq_butlast_append`〕によりコピーの行0上昇解析が不要に。→ **`maxsub_mono_NF`**（`w≺x` on NF ⟹ `maxsub w ≤ maxsub x`）完成。
- **wf → within-level 還元も完成 ✅**: `wf_Rnf_from_within_level`（`maxsub_mono_NF'`＋`wf_union_compatible`）。wf は `wf {(w,x). w≺x ∧ w,x∈NF ∧ maxsub w=maxsub x}`（同一 maxsub レベル）ただ一つに還元。
- **残り = Stage 3 = within-level wf のみ**（＝Buchholz ψ崩壊整礎性そのもの）。必要: (a) CNF 不変条件 `cnf`(兄弟非増加)の oper 保存 `cnf_ST_PS`（`cnf_diag` 済、全 NF で cnf 成立を経験確認 952/952。oper 保存はコピー構造解析が要りそう＝減少補題 bad 規模）、(b) レベル内崩壊マルチセット整礎性論法。nfinv だけでは within-level 非wf（反例 `p_0(0)+p_0(p_0(0))`）→ cnf が鍵。
  正直な評価: (b) は ψ_ω の wf という深い proof-theory 既知定理。すぐ解ける類でなく相当量の新規形式化が要る研究レベルの核。現状「PSS停止性 = この within-level wf ただ一つ」に形式還元済み（他は全 Isabelle ✓）。

### within-level wf への multiset アプローチ（鍵となる構造、継続用）
- NF 項は**最上位の兄弟（c-鎖）が全て添字 0**（経験確認「top sibling 添字≠0: 0件」）。よって NF 項 x は
  `x = p_0(b_1)+p_0(b_2)+…+p_0(b_k)`、cnf より `b_1 ≥ b_2 ≥ … ≥ b_k`（同添字0なので b で比較）。
- このとき NF 上の `≺` は **引数 b_i の multiset 拡大順序**に一致（CNF 和の lex = multiset ext）。
  ⟹ within-level wf は「引数 b_i 全体の上で `≺` が wf」＋ `wfp_multp`（マルチセット拡大は wf 保存、prss_ordinal で使用）に帰着。
- 引数 b_i は根添字 ≤1（bfb）。b_i を剥くと根添字が上がりうる（崩壊）。ゆえに「許される根添字レベル」で添字付けした
  accessibility 族の入れ子帰納（Buchholz の構造）が要る。prss_ordinal の `hord=H(multiset)` 流（ε_0）を
  崩壊階層へ拡張する形。これが残る本丸。
- 形式化の段取り案: (1) `cnf_ST_PS`、(2) 「NF 項=添字0の CNF 和」＋「≺ = 引数の multiset ext」を補題化、
  (3) HOL-Library.Multiset の `wfp_multp`/`accp` で accessibility を引数から和へ持ち上げ、(4) 根添字レベルの入れ子帰納。

### Stage 3（同一 maxsub レベル内整礎性）が迂回不可であることの確認
- `≺` は spine の slex を refine するが、**slex は有界アルファベット上の列でも整礎でない**
  （例 `[1]≻[0,1]≻[0,0,1]≻…`＝bad chain `x_n` の spine）。
- inv2 は bad spine の一部（`[1]`,`[0,0,1]` は inv2 違反）を排除するが、レベル n 内では
  spine は `[0,1,…,n]@tail`（tail は `{0..n}` 上任意）で、**tail 上の slex はやはり非整礎**。
- ゆえに同一レベル整礎性は spine-lex では出ず、`≺` が見る**部分木構造＋NF 制約**の再帰
  （＝Buchholz 崩壊の段）に本質的に依存する。maxsub 単調＝stratification は降下の
  maxsub 非増加までしか与えず、レベル内は崩壊整礎性が要る。ここが研究レベルの最重量部。

## ★ 確定方針 (2026-06-07): Towsner distinguished-set WF の移植

決定的発見・経験確認（`work/isot_check.py`, `anchor_search.py`）:
- **NF ⊄ Buchholz OT**（1327 NF 項中 279 が Buchholz OT 不適合）。対角タワー
  `p_0(p_1(…p_v(0)))` は NF だが OT 外（anchoring `G_a(b)<b` を破る。`ψ_0(ψ_1(ψ_2(…)))`
  は OT 項でない）。順序 `<` は Buchholz と完全一致だが **wf 部分集合が別物**。
  → 「Buchholz をそのまま構文移植」は不成立。
- NF が満たす単純構文条件は **cnf + bfb（添字≤親+1, 違反 0）のみ**。だが cnf+bfb は
  wf を与えない（bad chain `x_n=p_0ⁿ(p_1(0))` が cnf+bfb だが無限降下、n≥2 非到達=NF外）。
- **私の `olt` は素朴な添字優先 lex（K 条件なし）。真の wf 順序は critical subterm 条件付き。
  両者は NF 上でのみ一致する**（NF＝素朴 lex が真の順序数順序に合致する正規形）。

参照論文（`ya-pss/` 直下 PDF）:
- `H-Towsner-Polymorphic-Ordinal-Notations-2504.02131v2.pdf` ★本命。§2 が非poly Buchholz
  記法 (OT_Ωω: 構成子 `#`(multiset和), `ω^α`, `Ω_n`, `ϑ_n α`; distinguished subset H;
  critical subterms `K_n α`; 順序 Def 2.3)。**§3.2 が distinguished-set 法の完全な WF 証明**:
  - Def 3.7: `Acc_n ⊆ M_n` 階層。`M_{-∞}`=FC=-∞ の項全体, `Acc_n`=`M_n` の wf 部分。
    `M_n`={α: FC(α)=0, ground≥-n, ∀β∈K^{<0}α. β* ∈ ⋃_{i<n} Acc_i}。
  - Lemma 3.8: `Acc` は自然和 `#` で閉じる（m≤n, α∈Acc_m, β∈Acc_n ⟹ α#β∈Acc_n）。
  - Lemma 3.9: `ω^·` で閉じる。
  - Lemma 3.10: 崩壊 `ϑ` で閉じる（α∈Acc_n ⟹ ϑ(α)∈Acc_n）。
  - Lemma 3.11: `α∈Acc_n, n>-∞ ⟹ (ϑα)* ∈ ⋃_{m<n} Acc_m`（崩壊で cardinality 降下）。
  - **Thm 3.12: 全項 α と n≥G(α*) で α*∈Acc_n**（＝WF）。構造帰納＋上記補題。
  証明は構造帰納＋ Acc=wf部分 の組合せで Isabelle 移植可能（順序数を構築しない）。
  注: §2.5-2.7/§3.3/§4(Key Lemma, 変数, Ξ) は cut-elimination 用で **WF には不要**。
  注: 有限添字（私の nat）なら **非poly §2 系（Ω_n, ϑ_n を n∈ℕ で添字, absolute）で十分**、
  §3 の de Bruijn shift 複雑性を回避できる（§3.2 の証明構造を absolute 版に翻訳）。
- `WimVeldman-...Kruskal...pdf`: 直感主義 Kruskal（distinguished set/bar induction の背景）。

移植の段取り（継続用）:
1. **WF 核**: Towsner OT_Ωω を新 datatype で（`#`=multiset, `ω^`, `Ω_n`, `ϑ_n`）。
   FC（formal cardinality/level）, `K_n`（critical subterms）, 順序 `<_T`（Def 2.3, K 条件付き）,
   `Acc_n`/`M_n`（Def 3.7）を定義 → Lemma 3.8–3.12 → **wf `<_T`**。これが最大の再利用核。
2. **埋め込み**: 私の NF（`olt`）→ この WF 順序へ順序保存写像 φ（`p_a(b)→ϑ_a(b)`, 和→`#`）。
   NF 上で `olt = <_T` を示す（素朴 lex と真順序の一致）。これで `wf Rnf`。
3. 既存の within-level 還元 (`wf_Rnf_from_within_level`) と接続 or 直接 `wf Rnf`。

別案（leaner かもしれない）: WF 核を別 datatype で作らず、`three` 上に直接 `Acc_n/M_n`
階層を maxsub を level proxy として定義し §3.2 の論法を走らせる。要 K の正しい定義。

## (diagacc) 証明の方針候補（旧、参考）

- **(A)** Buchholz ψ_ω 流の正規形述語＋整礎性をフル形式化し、`translate(NF)` を
  順序保存で埋め込む。大規模。`good`（CNF+bfb）では足りないため、正しい NF 条件
  （崩壊の anchoring）を要する。
- **(B)** ST_PS 生成構造を直接使い、(diagacc) を対角 $v$ の帰納で示す（maxsub 単調を
  NF の性質として証明し、レベル帰納）。maxsub 単調を構文超集合でなく NF 上で示す
  必要があり、ここが要。
- いずれも内容は ψ 崩壊整礎性と同等で、本質的に大きい。

## ツール

- `yaBMS/c/bms`：`-v4` 展開、`-s` 標準判定（=isstd, 経験的・未証明）、`-c bm0 bm1`
  サイズ比較。
- 検証 Python は `work/`：`nf_u0.py`（CNF）, `maxsub_u0.py`（maxsub 単調 / bfb）,
  `reach_badchain.py`（x_n 到達可能性）, `validate.py`（parse/translate/cmp）。
- 注意：自前 `\<le>o`/`<o` に対する calc の `also`（推移律解決）は巨大項で発散。
  `also` を使わず明示 `have`＋`simp` で連鎖すること。
