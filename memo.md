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
（不成立確認: `three` には Ω が無く FC が常に -∞ になり階層が潰れる。Ω scaffolding は
proof に必須。よって別 datatype `ot` で WF 核を作る本線で進める。）

### wo.thy 進捗（全ビルド緑・コミット済, 2026-06-07）
Towsner §2 非poly OT_Ωω を `ot` datatype に移植（`W`=ω^ は省略, 埋め込み像は Th/Su のみ;
`Om` は K の scaffold）。済んだもの:
- `datatype ot = Om nat | Th nat ot | Su "ot list"`（`Zero ≡ Su []`）, `isH`。
- `FCset`/`FC`（Def 2.4, formal cardinality 集合と max）, `finite_FCset`。
- `Kn`（Def 2.2 critical subterms）, `finite_Kn`, `Kn_size`(γ∈Kn n a ⟹ size γ≤size a),
  `size_lt_Su`(x∈set xs ⟹ size x<size(Su xs))。
- **順序 `olt`（infix `<\<^sub>o`, Towsner Def 2.3）を `function`+`termination`(size measure) で定義**。
  K 条件付き＝真の wf 順序（素朴 lex の `olt`@mechanized とは別物）。`ole`(`\<le>\<^sub>o`)。
- 基本: `not_olt_Zero`, `olt_Zero_iff`, `olt_ZeroI`(Zero が最小)。
### 順序メタ理論の設計（重要・継続用）
- **観察: 単純な構造帰納／単一引数帰納は効かない**。`olt` の `Th m a <\<^sub>o γ` 再帰は
  host `Th m a` を固定したまま γ を `Kn` の中へ深く潜らせ、しかも δ∈Kn p c は Kn m a に
  入らない（Kn は非推移的: p≤m で `{Th p c}` を採り c へ潜らない）。ゆえに irreflexivity
  すら単独では帰納できず、**サイズ同時帰納**か下記の WF 直接論法が要る。
- **WF の分解（線形性不要ルート, 採用）**:
  - Towsner 和順序（Def 2.3 第1項: 共通部分を除き、残りβ達の1つが残りα達全てを支配）は
    **principal 上 `<\<^sub>o` の Dershowitz–Manna multiset 拡大 `mult` の部分関係**。
    （|Y|>1 でも他のβ'を空へ置換する mult1 を挟めば mult に入る。）
  - ゆえに `wf_mult`（HOL-Library.Multiset, R wf ⟹ mult R wf）＋ `wf_subset` で
    **principal (Om/Th) 上 WF ⟹ 和 (Su) 上 WF**。線形性を経由しない。
  - 注: Su は `ot list` だが順序は `mset xs` 経由なので、和順序⊆`mult` を mset で示す。
- **残る本丸 = principal 上の WF**:
  - `Om n` 同士は `m<n`(nat) で自明 wf。
  - `Th n a`（崩壊）の accessibility が核 = Towsner Lemma 3.10/3.11。level (= FC/添字)
    の入れ子帰納。`α ∈ acc ⟹ ϑ_n α ∈ acc`、`ϑ_n α の正規化が下位 level の acc`。
  - **全 `ot` 項が wf**（Towsner Thm 3.12, 崩壊 ϑ により bad chain が阻止される）。
    ゆえに部分集合不要で `wf {(a,b). a <\<^sub>o b}` を目標にできる。埋め込み像⊆ot で transfer。
- 段取り改: (i) `princ_lt`(principal限定の<)を別出し or 直接, (ii) 和順序⊆mult を証明し
  sum-WF を principal-WF へ還元, (iii) principal-WF を Isabelle `accp`/`acc` で level 帰納
  (Towsner 3.8-3.12 を absolute 版に翻訳), (iv) `wf (olt 全体)`, (v) 埋め込み順序保存。
- 設計判断: 論文の完備な WF 証明は **poly 版(§3.2, de Bruijn shift 付)**。私の `ot` は
  absolute(Om n)。absolute 版 WF は §3.2 を翻訳（shift 不要で簡素化されるはず）。
  M_n の正確な absolute 定義の再構成に注意（要検証）。risk があれば poly 版faithful移植に切替。

### 実装済（wo.thy, 緑・コミット済 2026-06-07 続き）
- `oltR ≡ {(a,b). a <\<^sub>o b}`。
- **`olt_Su_imp_mult`**: `Su xs <\<^sub>o Su ys ⟹ (mset xs, mset ys) ∈ mult oltR`
  （`one_step_implies_mult` 使用。和順序⊆multiset 拡大）。
- `embed.thy`: `princs`/`embed`（`P a b c ↦ Su(Th a (embed b) # princs c)`）, `embed_Z`,
  `embed_P`, `princs_P`, `princs_all_Th`, `isH_princs`。

### 実装済（wo.thy, 緑・コミット 2026-06-07 さらに続き）
- **assembly 完成 ✅**: `wfo`(well-formed), `bag`(principal 和の multiset), `principalR`
  (`{(a,b). a<\<^sub>o b ∧ isH a ∧ isH b}`), `mult_single_dom`, `mult_add`, `mult_dom_set`,
  **`bag_mono`**(`wfo a⟹wfo b⟹a<\<^sub>o b⟹(bag a,bag b)∈mult principalR`),
  **`wf_olt_of_principal`**(`wf principalR ⟹ wf {(a,b). a<\<^sub>o b ∧ wfo a ∧ wfo b}`)。
  → **残る WF 義務は `wf principalR`（Om/Th 上）ただ一つに crisp 還元済み**。
  注意（ハマり）: `<\<^sub>o` 上の `auto`/巨大 `metis` は発散（kill 要）。明示 `rule`/`linarith`/
  小さい metis で書く。`{#a#}+X` vs `add_mset a X`, `Suc 0≤length` は `Suc_le_eq` 必要。

### wf principalR の足場（wo.thy/wflevel.thy, 緑・コミット 2026-06-07 続き）
- `Kn_isH`(Kn 元は principal), `FCset_Kn`(γ∈Kn n a ⟹ FCset γ⊆{k∈FCset a.k<n}),
  `FC_Kn`(FC γ≤FC(Th n a)), `FCset_Th_eq_Kn`(FCset(Th n a)=⋃_{γ∈Kn n a}FCset γ),
  `FC_nonempty`, `FC_Th_le`(∀γ∈Kn n a.FC γ≤B ⟹ FC(Th n a)≤B)。
- **`FC_mono_pr`**: principal で `a<\<^sub>o b ⟹ FC a ≤ FC b`（FC 階層化の鍵）。
- `wflevel.thy`: `wfpart`/`AAlevel`/`accUpto`(定義), `wf_on_wfpart`(accessible 部分上 wf), `accUpto_mono`。

### ★ 深掘り所見（wf principalR の本質、継続用）
- FC 階層化（`FC_mono_pr`）で `wf principalR` を **同一 FC レベル内の wf** に還元できるが、
  それは **subscript による別の崩壊**（`Th m c <\<^sub>o Th n a` の m<n 第2選言ケース）になる。
- すなわち absolute 系（ϑ_n に subscript n）では **cardinality(FC)→subscript(n)→argument(acc)
  の三重入れ子帰納**が要る。Towsner **poly 版は単一 ϑ＋Ω-levels でこの subscript 段を吸収**して
  おり、そこが poly の利点。absolute 移植はこの三重帰納が固有の重さ。
- さらに注意: 順序 `olt` が使う critical subterm は **subscript ベースの `Kn`**（Def 2.3）。
  一方 Towsner の WF 階層 M_n は **cardinality ベースの K^{<0}**。absolute では両者が別物で、
  WF 階層用に cardinality ベースの別 K を要する可能性（要検討）。
- 選択肢: (a) absolute で三重入れ子帰納を実装（重い）、(b) **poly 版(de Bruijn Ω^(J)+shift)を
  faithful 移植**し embedding も poly へ（Towsner の完備証明をほぼ直訳, m<n 段が消える）。
  → 次セッションで (a) vs (b) を判断。現状 (a) の足場（FC 階層補題群）は揃っている。

### 次セッションの段取り（最重要・本丸 = `wf principalR`）
**(B') `wf principalR`**: Om/Th 上の `<\<^sub>o` 整礎性。`Om n` は `m<n` で自明。`Th n a` の崩壊が核
  （Towsner 3.10/3.11, level=FC 入れ子帰納, `Acc_n`/`M_n` Def 3.7 を absolute 化）。
  Isabelle `acc`/`accp` で「全 principal が acc」を level 帰納で示す。M_n 定義の再構成に注意
  （Thm 3.12 全項被覆が非空虚性の検証）。
**(C) 埋め込み順序保存**（既出, 下記）。

（参考・旧）assembly の元計画:
**(A) assembly: `wf principalR ⟹ wf oltR`（well-formed 上）** — 機械的、先にやると本丸が crisp 化:
  - `wfo`(well-formed): `Su` の元は principal かつ長さ≠1、再帰。埋め込み像は `wfo`。
  - `bag`: `Su xs↦mset xs`, principal `p↦{#p#}`。
  - `principalR ≡ {(a,b). a<\<^sub>o b ∧ isH a ∧ isH b}`。
  - `bag_mono`: `wfo a ⟹ wfo b ⟹ a<\<^sub>o b ⟹ (bag a, bag b) ∈ mult principalR`
    （4 ケース: Su/Su は `olt_Su_imp_mult`＋元が principal; Su/princ, princ/Su, princ/princ は
     `one_step_implies_mult` で構成）。
  - ⟹ `wf principalR ⟹ wf {(a,b). a<\<^sub>o b ∧ wfo a ∧ wfo b}`（`wf_mult`＋`wf_inv_image` bag）。
**(B) 本丸 principal WF**（Towsner 3.7–3.12, absolute 版に翻訳, 要慎重）:
  - `Om n` 同士は `m<n` で wf。
  - `Th n a`: `Acc_n`/`M_n` 階層（Def 3.7 を absolute 化）。level=FC で入れ子帰納。
    Lemma 3.8(和閉)/3.9(ω^閉=不要, W 無し)/3.10(ϑ 閉)/3.11(崩壊で level 降下)/Thm 3.12(全項 acc)。
  - **危険**: absolute M_n 定義の再構成（poly §3.2 は de Bruijn shift 付き完備証明）。
    M_n を小さく取りすぎると Acc 空虚→補題 vacuous。**Thm 3.12（全項被覆）が非空虚性の検証**。
    risk 高ければ poly 版 faithful 移植（shift 機械化）へ切替。
**(C) 埋め込み順序保存**: NF 上で `olt_three w x ⟹ embed w <\<^sub>o embed x`（NF で素朴 lex=真順序）。
  ⟹ `wf Rnf`（embed の inv_image）。`wf_Rnf_from_within_level`/`wf_Rnf_from_diag` と接続。

旧・次の段取り: (1) 順序性質: 線形性(Lemma 2.1)/推移律/`FC α<FC β ⟹ α<β`。
(2) `Acc_n`/`M_n`(Def 3.7), Lemma 3.8(和で閉)–3.10(ϑで閉)–3.11(崩壊で cardinality 降下)
–Thm 3.12(全項 accessible=wf)。(3) 埋め込み `three`→`ot`（`P a b c ↦ Su(Th a · # tail)`),
NF 上で `olt_three = <\<^sub>o` を示し `wf Rnf`。
注: `isbman build -d /home/koteitan/ya-pss/git -v YAPSS`（cwd がリセットされうるので -d 絶対パス）。

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

## (wfpR) 2026-06-07 WF核を `wf pR` まで還元（accinfra / wflevel 改）

**到達点（すべて緑・コミット済）**:
- `accinfra.thy`: 汎用 acc 基盤。`acc_imp_acc_trancl`（acc は trancl で不変）,
  `acc_pullback`（単調写像で acc 引き戻し）, `acc_mult_of_elems`（要素が acc なら
  multiset も `mult` で acc＝`all_accessible` の要素版）。
- `wflevel.thy`: 和への還元。`oltRw≡{(a,b).a<o b∧wfo a∧wfo b}`。
  `wfo_Kn`（wfo の臨界部分項は wfo）, `bag_mono_w`（`<o` on wfo → `mult oltRw`）,
  `acc_of_bag_elems`（bag 要素が acc なら本体も acc）, `princ_acc_lift`
  （`acc pR ⟹ acc oltRw`: principal の Su 述語は principal 和因子に分解＝各々 pR 述語）,
  `wf_oltRw_of_wf_pR`: **`wf pR ⟹ wf oltRw`**。`pR≡{(a,b).a<o b∧isH a∧isH b∧wfo a∧wfo b}`。
- `embed.thy`: `wf_Rnf_via_embed` は `wf oltRw` を仮定（`wf_olt_of_principal` 廃止）。

**残る本丸＝`wf pR`**（well-formed principal 上の `<o` 整礎性）＝古典 Buchholz WF。
重要発見: Towsner §2（本記法）には WF 証明が無い。§3.2 の WF は polymorphic 系
（de Bruijn / ground 正規化）専用。絶対系（Om n は n で上方整礎なので ground 正規化不要）
では直接 Buchholz 流で書く必要。

**`wf pR` の難所（精密分析）**: master を構造帰納にすると Th n d の引数 d∈acc は
部分項として得られる（Towsner Thm 3.12）。崩壊補題 L_Th（d∈acc⟹Th n d∈acc）の中で:
- 臨界部分項支配（Om m≤δ, Th≤δ; δ∈Kn n d）: δ は d の部分項→size 小→master の
  size-IH(HS) で acc。✓（`acc_downward`+`wfo_Kn`）
- 同添字 e<o d（p=n）: `(e,d)∈oltRw`, d∈acc → `acc_downward` で e∈acc → 引数 acc 帰納。✓筋
- 述語の臨界部分項 γ∈Kn p e: size γ<size(述語) → 述語 size 帰納(HS_q)で acc。✓筋
- **異添字 p<n かつ FC=FC(Th n d)（同 level）**: e は Th n d の部分項でも d の下でもなく、
  e∈acc の供給源が無い。FC<level なら LOW で済むが FC=level の Th p e(p<n) と Om N が壁。
  → 純 size / 純 FC / (FC,size) いずれも反例（同FC述語が size 増大しうる）。
  Towsner は M_n（level集合）で臨界部分項 acc を robust に供給＋引数 acc 帰納で解決。
  絶対系移植には Acc_n/M_n（FC で層化、ground 臨界部分項条件）の構築が要。次段。
- 和因子（述語が Su）: `acc_of_bag_elems` で principal 述語に帰着済み（princ_acc_lift 内で実証）。

次: Acc_n/M_n を FC 層化で構築し L_Th を入れ子帰納で証明 → `wf pR`。並行で embed 順序保存。

## (Ifull) 2026-06-07 WF核を単一補題 Ifull に還元（buchholz.thy）

`wf pR`/`wf oltRw`/`wf Rnf` は **Ifull**（∀wfo principal a. a∈Acc(FC a)）に完全還元・コミット済。
buchholz.thy: Mlev/Awf/AccBelow 構築・PC（前者閉包）⟸Ifull・(II) Acc_n⊆acc pR・
wf_pR_of_Ifull/wf_oltRw_of_Ifull すべて緑。

**Ifull の中身（=Towsner Thm 3.12, 絶対系）**: FC で強帰納。レベル N で
- Part1: a∈Mlev N (AccBelow N) — 臨界部分項 FC<N が AccBelow に（下位帰納で可）。
- Part2: a∈acc(R|M) = **within-level（特に FC=0=ground）の崩壊 WF**。これが本丸。

**Part2 の前者分解（principal a=Th n d, N=FC a, n>N）**:
- 臨界支配 q≤δ (δ∈Kn n d): δ は d の部分項で size 小 → 構造(size)帰納で acc、acc_downward。
- m=n（Th n e, e<o d）: 引数 acc 帰納（d∈acc は d が部分項＝構造帰納で供給）。
- p<n（Th p e）: FC(Th p e)≤N。**FC<N なら LOW、FC=N（同レベル）なら subscript 帰納**。
  例: `Th1(Th5(Om9)) <o Th2(Om0)`（両 FC=0, p=1<2, 引数 Th5(Om9) は部分項でなく size 大）。
  引数 e は述語の部分項なので、述語を size 帰納すれば e∈acc は出る＝subscript→arg-acc 入れ子。
- 和: 和因子は principal 前者 → 上記＋acc_of_bag_elems。
⟹ **三重入れ子（FC→subscript→argument acc）＋構造(size)帰納で引数供給**。

**Ifull に要る基盤補題（未証明・次段）**:
- `olt_trans`（<o 推移律）: 和の連鎖・臨界支配で必須。Towsner Lemma 2.1 圏。大きい。
- `Kn_le_self`（δ∈Kn n d ⟹ δ≤o d）か、代替に size 帰納で臨界部分項 acc。
- 崩壊補題 Lcoll（LOW(n)＋d∈acc＋acc-on-d で Th n d∈acc。p<n の FC=N は subscript 帰納）。
注: ground 正規化(α*)は不要と判明（引数は述語の部分項なので構造帰納で acc 供給できる）。
de Bruijn も不要。絶対系で素直に書ける見込み。残るは推移律＋三重入れ子の配線。

## (Kn/Mlev) 2026-06-07 推移律回避＋Mlev 定義のズレ発見

**推移律不要を確認・実装（wo.thy, 緑・コミット f88fbe3）**:
- `olt_Th_of_le_Kn`（isH γ, δ∈Kn q b, γ≤o δ ⟹ γ<o Th q b：<o の臨界部分項節が witness）。
- `Kn_mono_le`（γ∈Kn n a, n≤r ⟹ ∃δ∈Kn r a. γ≤o δ）：a の構造帰納＋第一選言のみ。**一般推移律不要**。
- `KnTh`（γ∈Kn n a, n≤r ⟹ γ<o Th r a）、`Kn_le_self`（γ∈Kn n d ⟹ γ≤o d）。
⟹ 崩壊補題の臨界支配は `Kn_le_self`＋`acc_downward[d∈acc]` で出る（推移律不要）。

**Ifull Part2（within-level WF）の残課題と Mlev 定義バグ**:
- buchholz の `Mlev N prev` の条件は `∀p γ. γ∈Kn p a⟶FC γ<N⟶γ∈prev`（a の Kn）。
  しかし順序 `q <o Th s d` が使う臨界部分項は **`Kn s d`（引数 d の subscript=s での Kn）**。
  `Kn s (Th s d)={Th s d}` であって `Kn s d` ではない＝**Mlev の条件が順序の臨界部分項を捕えていない**。
  → Mlev を `ocrit a`（a=Th s d なら `Kn s d`, それ以外 ∅）ベースに直す必要。
- within-level（FC=N）の前者分解（a=Th s d, s>N）：
  - 臨界支配 r≤γ (γ∈Kn s d=ocrit a): FC γ≤N。FC<N→AccBelow（Mlev条件）。FC=N→γ<o a・size 小→size 帰納（要 γ∈Mlev N＝「臨界の臨界⊆ a の AccBelow 条件」補題）。
  - m=s（Th s e, e<o d）: **d∈acc が要る＝構造帰納（d は部分項）でしか出ない**。FC/subscript 帰納では引数 FC≥N が拾えない。
  - p<s（Th p e, FC=N）: subscript 帰納（p∈(N,s)、底 p=N+1 の p'<p 前者は FC<N→LOW）。
  → **三重帰納（FC 外 → subscript 中 → 引数 acc=構造帰納で d 供給）**＋直した Mlev。m=s の d∈acc を
    構造帰納から供給する配線が肝。次段で Mlev を ocrit ベースに直し、Mlev_acc_pR を実装する。

## (訂正) 2026-06-07 ground 正規化は「必要」と判明（前言撤回）

前に「引数は述語の部分項なので構造帰納で acc 供給でき、ground 正規化不要」と書いたが**誤り**。
反例を構成して確認：
- `a = Th s (Om m)`（m≥s, FC=0, size 2）。`Kn s (Om m)={}`（m≥s）。
- 述語 `Th 5 (Th100 (Om9))`：`Kn 5 (Th100(Om9))={}`（5≤9）, `5<s` ⟹ 第二選言で `<o a`。
  臨界支配でない（Kn s d={}）＝**真の D2 p<s 前者**。FC=0（=a と同）, 引数 `Th100(Om9)` は
  size 3 > size a=2 ＝**引数が項より大きい**。subscript も 100 > s で subscript-IH 外。
- ⟹ 構造(size)帰納でも subscript 帰納でも FC 帰納でも引数 acc を供給できない。
  これは ground レベル（FC=0）の崩壊 WF そのもので、**Buchholz/Towsner の ground 正規化
  （α*／G）または C(α) 制御集合**が本質的に必要。

**結論（確定）**: (a) 絶対系でも WF の核は ground 正規化機構の実装を要する＝(b) と同等規模。
既存の還元（wf pR⟸Ifull）・Kn 補題群・accinfra は活きる。残るは Ifull Part2＝
ground 正規化を絶対系に移植して within-level（特に FC=0）崩壊 WF を閉じること。

## (★決定的, 2026-06-08) §3.2 精読 → 絶対系は poly より「厳密に重い」と判明

Towsner §3.2 を全文精読（`/tmp/tow.txt` 抽出, Def 3.1–3.7 / Lemma 3.8–3.12）。判明:

1. **§2（＝私の絶対系 `ot`: `Om nat`/`Th nat`/`Su`）には WF 証明が一切無い。** §2 は順序の
   定義と Key Lemma（cut-elim 用）のみ。WF（整礎性）は **§3 の polymorphic 系
   `OT^poly_Ωω`（`Ω(J)` J≤0 の de Bruijn 相対レベル＋**単一 ϑ**（添字なし）＋shift）専用**。
2. **WF 証明（§3.2）は de Bruijn shift `α±n^{≤J}`（Def 3.3）と正規化 `α* = α^{≥0}_{-FC(α)}`
   （FC top を 0 に押上げ）と ground 階層 `G(α)=min FC`（Def 3.6）に本質依存。**
   M_n/Acc_n（Def 3.7）は **ground で階層化**（私の `Mlev` の FC-max 階層は別物＝不適）。
   Lemma 3.8（和, shift付）/3.10（`α∈Acc_n ⟹ ϑ(α^{≤0}_{-1})∈Acc_n`）/3.11（`ϑα` が ground 降下）
   /3.12（構造帰納）すべて shift と α* に依存。
3. **footnote 8（decisive）**: Towsner 自身が絶対系（"Ω(0) means the first cardinality
   wherever it appears"）を検討し、"This would change when shifting has to be done, but
   **would not save us from doing it**" と明記。⟹ **絶対系でも shift は不可避。**
4. **絶対系で α* 正規化を実装すると `Om n` の n を FC 分だけ下げる必要があり、ground<FC の項
   （2 つ以上の cardinal level を含む）で `n` が負になる ⟹ `Om int` が必須。** さらに絶対系は
   ϑ に添字が付く（`Th nat`）ので、poly の**単一 ϑ＋shift より組合せが増え厳密に重い。**

**∴ (a)/(b) 判断の前提が覆る**:
- 旧判断「(b)にいっても Isabelle 資産は無い／(a) と (b) は同等規模」→ **誤り**。
- **(a) 絶対系**: 論文に存在しない「絶対版 §3.2」を自作（`Om int`＋shift＋添字付 ϑ の Acc_n/M_n
  を ground 階層で再構築）＝**オリジナル研究・高リスク・poly より重い**。
- **(b) poly 系**: 論文 §3 の完全証明を**ほぼ転写**（当初ユーザーが論文を渡した狙いそのもの）。
  低リスク。コスト＝新 datatype（`Om int`/単一 ϑ/shift）＋ `embed: three→poly` 作り直し＋
  sum→multiset 還元（wflevel）を poly 順序で再具体化。ただし **accinfra（汎用 acc）と
  還元の設計パターンは流用可**、`three`/translate/decrease/wf.thy 還元は無傷。
- 結論: **(b) が (a) を複雑性で支配**（poly=単一ϑ+shift < 絶対=添字ϑ+int+shift）。

## (★ユーザー決定 2026-06-08) (a) 絶対系のまま §3 を「書き換え転写」で実行

footnote 8（絶対系でも shift 不可避）を伝えた上で、ユーザーは **(a) 絶対系を維持し §3 の
完全証明を絶対系へ書き換えながら転写**する方針を選択。これを実行する。

### L_Th（崩壊閉包）scratch 検証で p<s ギャップを正確に切り出し（`git/scratch_lth.thy`, ROOT外）
`d∈acc oltRw ⟹ Th s d∈acc oltRw` を d の acc 帰納で試行。骨格（`induction set: Wellfounded.acc`,
`1.hyps`=d∈acc, `1.IH`=IH, `pred_acc`=acc_downward）で **easy ケースが全通過**＝検証済:
- Om 前者 / Th 第一選言（臨界支配）: `dom_acc`（γ∈Kn s d は `Kn_le_self`+`acc_downward` で acc, q≤oγ で downward）。
- Th 第二選言 p=s（e<o d）: `(e,d)∈oltRw` ＋ 主 IH。
**残 `sorry` は Su 前者 と Th 第二選言 p<s の2つのみ**。

### p<s が本丸（shift 不可避を確定）
`Th p e <o Th s d`（p<s, ∀γ∈Kn p e. γ<o Th s d）の引数 e は：部分項でなく size/FC とも大きく
（反例 e=`Th100(Om9)`, FC9, vs a=`Th6(Om6)` FC0）、**size/FC/構造のいずれの測度でも e の acc を
供給不能**。Towsner Lemma 3.10 も `ϑ(α^{≤0}_{-1})` と明示 shift を使用。⟹ **絶対転写でも明示 shift 必須。**
Python 移植（`work/ot_order.py`）で確認: 可算項（FCset 空）上 `olt` は**線形整礎**（size≤4,idx≤4 で
incomparable=0, cycle=0）。最小元は最深ネスト `Th0(Th1(Th2(Om2)))`。

### 確定設計
1. **datatype を `Om int`/`Th int` 化**（shift が束縛部分項で負添字を生む例
   `Su[Om3, Th0(Om0)]` を ground=3 で下げ→`Th(-3)(Om(-3))` ⟹ int 必須）。`wo.thy` の順序補題群を
   int で再確立。FC は -∞ 対応（empty=countable を 0 と区別）。
2. **shift（Def 3.3 絶対版）/ ground G（Def 3.6）/ 正規化 α\*（Def 3.6）** を定義。
3. **M_n/Acc_n を ground 階層**（Def 3.7 絶対版, `buchholz.thy` 全面書換）。`Mlev`(FC-max) は破棄。
4. **Lemma 3.8（和閉, shift付）/3.10（ϑ 閉, p<s を shift で解消）/3.11（ϑ で ground 降下）/3.12（構造帰納）**
   を絶対系へ転写 → `wf pR`。
5. 還元（`wflevel: wf_oltRw_of_wf_pR`, `accinfra`）と `embed`（int 化）を接続。
継続用: scratch_lth.thy の easy ケース骨格はそのまま int 版 L_Th に流用可（p<s だけ shift で差替）。

### 進捗 (2026-06-08 続き, すべて緑・コミット済)
- **int 化完了**: `ot=Om int|Th int ot|Su`。`wo`/`wflevel`/`embed` 緑。旧 FC 階層補題
  （FC_Th_le/FC_Kn/FC_mono_pr）は int で破綻（FC ∅=0 と負値）するので削除。`buchholz` はスタブ。
- **shift（Towsner Def 3.3 global 版）完成**: `shift k`＝全 Om/Th 添字に +k。
  `shift_shift/0/inv/inj/isH/eq/eqTh/eqOm/FCset/Kn` ＋ **`shift_olt`（順序自己同型, sorry無し）**
  証明済（Su/Su case は `image_mset_diff_if_inj`、Th/Th は展開形 eq 補題で解決）。
  ⟹ **`acc oltRw` は shift 不変**（shift は自己同型＝降下列を降下列に写す）。

### shift だけでは p<s は閉じない（要 M_n 階層, 確認済）
`Th p e <o Th s d`(p<s) で shift(s-p)(Th p e)=Th s(shift(s-p)e) は subject の引数 d より
大きくなりうる（反例: shift1(Th100(Om9))=Th101(Om10) は Om6 より上）＝acc-IH on d で拾えない。
∴ shift 不変だけでは不足。**Towsner §3.7 の distinguished-set（M_n/Acc_n）が必須**。

### 確定設計：width 階層（絶対系 §3.7, nat 添字維持）
Towsner は top を 0 に正規化（α*=α^{≥0}_{-FC}）し ground で階層化。絶対系（shift は完全自己同型）では:
- **正規化** `norm a = shift (- FC a) a`（FCset≠∅ のとき top→0; countable は不変）。`acc` は shift 不変なので `a∈acc ⟺ norm a∈acc`。
- **width** `w(a) = FC a - G a`（FCset≠∅）/ countable は別扱い。Towsner の n＝-G(α*)＝width。**ℕ に収まる**。
- **M_n** = {正規化済（FC=0 or countable）, width ≤ n, 臨界部分項の正規化が ⋃_{i<n}Acc_i}。`Acc_n`=M_n の acc 部分。
- Thm 3.12 は**構造帰納**（Su/Th/Om を closure 補題 3.8/3.10 で閉じる）。L_Th(3.10) の p<s は
  正規化＋width-IH で引数を下位 width に落として処理。
次段: `wo.thy` に `G`(ground, Min FCset)・`norm`・width を定義 → `buchholz.thy` に M_n/Acc_n と 3.8/3.10/3.11/3.12。

### (訂正) width も `<o` 非単調 — 単調性ショートカットは存在しない
当初 width 単調（違反0）と書いたが**不完全な検証**だった（Python pool が Th 引数に Su を含まず）。
Su 込みの反例: **`Th6(Su[Om3,Om5]) <o Om6`** で width(LHS)=5-3=2 > width(Om6)=0 ＝ **width 非単調**。
⟹ **FC・width・ground いずれも `<o` 非単調**。旧 FC 階層が `FC_mono_pr` で得ていた「綺麗な PC」は
**実は使えない**（旧 FC 構成が証明不能だった根因の一つ）。

∴ **単調性による PC ショートカットは無い**。Towsner の PC（前者閉包）は単調性ではなく
**Lemma 3.10/3.11（ϑ 閉包・ground 降下）そのもの**が担う。よって本丸は
**full Buchholz 整礎性（§3.2）の忠実転写**＝ Acc_n/M_n（ground 階層, 正規化 α\*）＋
Lemma 3.8（和閉）/3.10（ϑ 閉, 主帰納 on 引数 acc, 構造帰納 on 前者, 正規化で p<s を吸収）/
3.11（ϑ で ground 降下）/3.12（構造帰納）。ショートカット無しの研究レベル核。

- 確立済の道具（すべて緑・コミット済, これが footnote 8 の言う「絶対系でも必須」の shift 機構）:
  `shift`(順序自己同型 `shift_olt`), `shift_wfo`, **`acc_shift`(acc は shift 不変)**,
  `gnd`/`wdt`/`norm`＋`FC_shift`/`gnd_shift`/`wdt_shift`/`FC_norm`/`wdt_nonneg`。
- 次段: §3.7 の Acc_n/M_n を ground 階層で定義（正規化込み）→ Lemma 3.8/3.10/3.11/3.12 を
  忠実転写。PC は 3.10/3.11 経由（単調性不使用）。設計は Towsner §3.2 を逐語的に追う。

### ★★ 致命的訂正 (2026-06-08): global `wf pR` は偽 — WF 対象は「可算項」
`Om int` 化により **`Om 0 >\<^sub>o Om(-1) >\<^sub>o Om(-2) >\<^sub>o …` の無限降下**が生じる
（Towsner §3.2 冒頭「Ω(0)>Ω(-1)>… certainly not well-founded on its face」）。
⟹ **全 int principal 上の `wf pR` は偽**。`acc_shift` で global acc に持ち上げる `master2`
（normalized principal∈acc pR）も**偽**（Om 0 すら acc pR でない）。コミット済だが要修正。

**embed 像は Om を含まない**（`embed`/`eprincs` は `Th`/`Su` のみ生成, Om 無し）⟹
FCset(embed t)={} ＝ **embed 像は全て可算項（FCset={}）**。
∴ **WF の正しい対象＝可算項（`FCset a = {}`）に制限した順序**。Om は崩壊階層の
スキャフォールド（証明内部の cardinal 上界）としてのみ要る。可算項上は Om 降下が無く WF。

**修正方針**:
- WF 主張を可算項に制限：`cbl a ≡ FCset a = {}`。目標は `wf {(a,b). a<\<^sub>o b ∧ wfo a ∧ wfo b ∧ cbl a ∧ cbl b}`
  （または embed 像 = Om-free 項上）。embed 像 ⊆ 可算 なので `wf Rnf` に十分。
- `master2`/`wf_pR`（global, 偽）を破棄し、可算版に。`wflevel` の和→principal 還元も可算で閉じる
  （可算 principal の Su は可算）。distinguished-set（Acc_n/M_n）は Om 上界を内部で使い可算項の acc を構築。
- shift（負添字）は正規化の proof-internal 道具のまま（最終主張には負添字項は出ない）。
- 注: `wf_Rnf_via_embed`（embed.thy）は `wf oltRw` 仮定 → 可算版 `wf oltRw_cbl` に差替が要る。

### ★ 到達点 (2026-06-08): 停止性 = L_ThF[p<n] ＋ op の2点に集約（他は全証明済）
end-to-end チェーン（`embed.step_terminates_via_embed`）構築・全コミット済:
`step_terminates_via_embed` ⟸ `wf_Rnf_via_embed[op]` ⟸ `wf_oltRwF` ⟸ `masterF` ⟸ `L_ThF`。
- **`masterF`（証明済）**: omfree wfo 項 → acc oltRwF。構造帰納（Om は omfree で消滅／Su は
  `bag_mono_wF`+`acc_of_bag_elemsF`／Th は `L_ThF`）。
- **`L_ThF`（domination/p=n/Su 証明済, 残 p<n のみ）**: `omfree d⟹wfo d⟹d∈acc oltRwF⟹Th n d∈acc oltRwF`。
  acc 帰納 on d。前者 r（omfree なので Om 無し）: dom（γ∈Kn n d 支配, `Kn_le_self`+downward）✓／
  p=n（e<o d, 主 IH）✓／Su（`acc_of_bag_elemsF`+summands を pacc）✓／**p<n が唯一の sorry**。
- **残 2 義務**:
  1. **`L_ThF` の `p<n` ケース** = `Th p e <o Th n d`（p<n, ∀γ∈Kn p e. γ<o Th n d, 全 omfree）で
     `Th p e∈acc oltRwF`。＝ **真の Buchholz ϑ 崩壊 WO**。引数 e は acc 供給源が無く（impredicative）、
     subscript 階層＋Ω scaffold＋制御集合（Buchholz C_n(α)/Towsner 正規化）が要る研究核。
     注: omfree 項は FCset={} で ground/width 退化 ⟹ 既存の ground 階層 Mn/Acc は**そのままでは効かない**。
     subscript（p）で階層化し Ω_p を上界とする版が要る（or Buchholz 1986 の C 集合）。
  2. **`op`**（embed 順序保存, NF 上 `w≺x⟹embed w<\<^sub>o embed x`）。NF 不変条件（CNF/bfb/maxsub）依存。
- 道具（全証明済）: shift 順序自己同型 / acc 不変 / gnd/norm/wdt / Mn/AccB/Acc（ground 階層, p<n 用に
  subscript 版へ要再設計）/ omfree_embed / bag_mono_wF。

### ★ 到達点 (2026-06-08 続き): 停止性 = 3義務に集約（実 sorry 2 ＋ op 仮定）
PSS 停止性 ⟸ **(1) `olt_trans`**（wo:384, 推移律＝Towsner Lemma 2.1 順序メタ）
＋ **(2) `L_ThF[p<n]`**（buchholz:434, Buchholz ϑ 崩壊核）＋ **(3) `op`**（embed の NF 順序保存）。
- **順序メタ理論を整備**: `olt_asym`（非対称性）/`olt_irrefl` を完全証明（`olt_trans` 依存）。
  asym は「より小さい 2-cycle 抽出＋size-IH」で 8/9 ケース＋Th/Th の subscript 排他・domination を
  直接証明、XA∧YA（双方が相手の臨界部分項に支配）のみ `olt_ole_trans` 経由で trans に帰着。
- `olt_trans` の証明計画: size 帰納＋ c の形で分岐。c=Om は IH（小さい三つ組）＋multiset で可（分析済）、
  c=Su は multiset bookkeeping、c=Th（K 条件）が最難。これが残る順序メタ唯一の sorry。
- 反例検証（`tools/ot_order.py`）: maxsub は general omfree で非単調（382件, NF でのみ単調）、
  width も非単調、p<n は ≤d/domination に非帰着（967件）＝崩壊核は近道なし確定。
- 参考: PrSS（姉妹, 完成済）は ε_0＝`hord=H multiset` の accp/multp 構成。PSS の崩壊は別物（ε_0 超）。

### olt_trans（推移律）の進捗 (2026-06-08)
size 帰納（size a+size b+size c）で c の形で分岐。**証明済**:
- 補助 `olt_Om_mono`（a<o Om p, p≤q ⟹ a<o Om q）。
- **c=Om 完全**（a=Om/Th/Su, olt_Om_mono＋IH＋multiset count 論法）。
- **c=Su の「a principal」完全**（b<o Su zs から支配 z∈zs を発見, olt_irrefl で witness 確保, IH）。
**残（olt_trans 内 sorry 2つ）**: c=Su[a=Su]（one-step multiset 推移＝要 totality）, **c=Th（最難）**。
- c=Th の困難: K 条件の連鎖が大きな中間項 b=Th p f を貫き、IH の measure
  size δ+size γ < size(Om q)+size c が保証されない（b,c 独立）。Towsner Key Lemma 本体で、
  asym/trans/total が深く相互依存（combined induction か Th-monotonicity 補助が要）。
- 学んだ tactic パターン（次段用）: `from X[unfolded eq1 eq2] obtain`（case 代入後の olt 展開）,
  multiset は count+linarith+in_diff_count を明示, IH は `using sz xy yz IH by blast` で明示適用,
  `≤o` の等式ケースは `by auto`/明示。`bc` 等を simp で代入させず `[unfolded]` を使う。

### olt_trans 続報 (2026-06-08): c=Th 全証明、残 c=Su[a=Su] のみ
- **c=Th 完全証明**（a=Om/a=Su は IH(小成分), **a=Th＝ϑ/ϑ/ϑ core は totality 不要**で
  `olt_Th_of_le_Kn`（支配→Th未満）＋IH＋subscript の arith／q=p=n のとき IH(e,f,d) で e<o d）。
  ＝Towsner Key Lemma の最難部が片付いた。
- **残 olt_trans sorry は c=Su[a=Su] ただ1つ**（Su as<o Su bs<o Su zs ⟹ Su as<o Su zs ＝
  one-step multiset 順序の推移）。各 t∈as-zs は w1 か w2 に支配されるが、単一 witness∈zs-as へ
  まとめるのに w1,w2 比較（totality）か多重度の場合分け（fiddly）が要る。`olt_Su_imp_mult` 有り。
  選択肢: (i) `olt_total` を別途証明し mult 同値経由, (ii) 直接 witness 論法。次段。
- ∴ **実 sorry は計3つ**: olt_trans[c=Su[a=Su]], L_ThF[p<n], ＋ op 仮定。
