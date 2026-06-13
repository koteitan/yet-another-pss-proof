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
注: `isbman build -d /home/koteitan/proofs/ya-pss/git -v YAPSS`（cwd がリセットされうるので -d 絶対パス）。

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
- **c=Su[a=Su] は真と実証**（`work/ot_order.py`: 735130 連鎖で clause1 非推移の反例 0）。
  要素全順序が無くても（ot は Su のリスト順序 artifact で非全順序）one-step multiset clause は推移的。
  ∴ totality 不要の直接 witness 論法が存在するはず（w1/w2 の多重度場合分けが fiddly）。
  あるいは `olt_Su_imp_mult`＋mult 推移（要素 trans は size-IH で可）＋converse。後段で詰める。

### ★ c=Su[a=Su] は order メタ理論の相互依存（combined induction 要）と判明
c=Su[a=Su] の witness 論法（∀v∈as. v<o z, z∈zs ⟹ witness z）で **z∉as** が要るが、それは
`olt_irrefl`（z<o z 排除）に帰着。`olt_irrefl`⟸`olt_asym`⟸`olt_trans`（今証明中）＝**循環**。
∴ 分離アプローチ（olt_trans を先に、olt_asym を後で）では c=Su[a=Su] が閉じない。
**正しくは asym+trans（+irrefl）を単一 size 帰納で同時証明**（Towsner Lemma 2.1 / 標準の
順序メタ理論手法）。c=Om/c=Su[a-principal]/c=Th は IH(trans) のみで irrefl 不要だったので分離で証明できた。
- 次段の選択肢: (A) `olt_trans`＋`olt_asym` を1つの combined lemma に統合し同時帰納（c=Su[a=Su] で
  IH から要素 irrefl/asym が使える）。既証明の c=Om/c=Su[a-principal]/c=Th はそのまま combined に移植可。
  (B) c=Su[a=Su] だけ別途、要素 irrefl を size-IH で局所証明して埋める。
- 現状の order メタ理論: c=Su[a=Su] 以外すべて証明済（＝Th/Th/Th 含む本質部分は完了）。

### ★ 確定 (2026-06-08): order メタ理論は単純 size 帰納では閉じない（Towsner Lemma 2.1 本体）
`olt_irrefl` も自立しない: Th-first-disjunct（`Th m a ≤o γ`, γ∈Kn m a）の γ=Th r h サブケースで
δ∈Kn r h について `Th m a≤oδ<oγ<o Th m a` の cycle が出て trans/asym が要る（Om サブケースのみ
自己比較 `Om r<o Om r=False` で自立）。∴ irrefl⟷asym⟷trans の 3-way 相互依存。
さらに **combined induction でも単純 size measure では不足**: irrefl(w=Th m a) が
`asym(γ,w)=trans(γ,w,γ)+irrefl(γ)` を要し、`trans(γ,w,γ)` の measure=2·size γ+size w が
irrefl(w) の budget（〜2 size w）を超え得る（size γ>size w/2 のとき）。
⟹ Towsner Lemma 2.1（Key Lemma 圏）は **careful な measure 設計**（部分項深さ等の別測度 or
Towsner の Dn,γ・!nγ 構成）が要る研究レベル。c=Su[a=Su] はこれに blocked。

**∴ 残3義務はいずれも substantial**: olt_trans[c=Su[a=Su]]（=order メタ理論完成, careful measure）、
L_ThF[p<n]（Buchholz ϑ 崩壊 WO, 制御集合）、op（NF↔ot 順序保存）。
それ以外（end-to-end 還元・shift 自己同型・masterF・olt_trans の主要部・omfree 等）は全証明済・緑。

### 🚨🚨 致命的発見 (2026-06-08): oltRwF / omfree / cntbl は ill-founded ＝ L_ThF は偽
**`Th(-k)(Zero)` (k=0,1,2,…) は無限降下 omfree 鎖**: `Th(-(k+1))Z <o Th(-k)Z`
（olt Th/Th 第2項 d2: Kn(-(k+1)) Zero=∅ で前件 vacuous, かつ -(k+1)<-k）。Python で確認済。
⟹ **`oltRwF={(a,b).a<o b∧omfree a∧omfree b}` は ill-founded**（無限降下鎖が omfree 内に存在）
⟹ **`wf_oltRwF` は偽**, **`masterF`（全 omfree wfo 項が acc）は偽**（`Th(-1)Z∉acc`）。
これらが「緑」なのは **`L_ThF[p<n]` の sorry を経由しているため** ＝ **L_ThF は「難しい」のではなく「偽」**。
反例: d=Zero (omfree,wfo,∈acc), n=-1 ⟹ L_ThF は Th(-1)Z∈acc を主張するが偽。
∴ headline `step_terminates_NF` は**命題は真**だが**証明が無効**（偽の sorry 補題に依存, 完成不能）。
- **`cntbl`(FCset=∅) も同様に ill-founded**: `Th(-k)(Om1)` が無限降下 cntbl 鎖。
  ⟹ 直前 commit の「cntbl が正しい WF target」という主張は**誤り**（cntbl_downclosed 補題自体は真で再利用可だが target ではない）。
- **原因**: olt の Th/Th d2 が `m<n` を**下限なし**に許す。負添字 ψ_{-k} は Buchholz/Towsner では
  **無効な記法**（Towsner は Ω_{(J)} を J≤0 に限定, Buchholz は ν≥0）。負添字項は notation system 外。
- **正しい WF target = 非負添字フラグメント**: `nneg t ≡ (全 Th 添字 ≥0 ∧ 全 Om index ≥0)`。
  embed 像は `Th (int a)` (a:nat≥0)・Om 無し ⟹ nneg(embed t) 成立（wfo_embed と同様に証明可）。
  予想: olt は {omfree ∧ nneg}（or {wfo∧nneg}）上で WF（Buchholz の標準結果, ν≥0）。
  **embed 転写には olt∩(nneg×nneg) の acc で十分**（embed 像同士のみ比較するため downward 閉不要）。
- **修正方針**: (1) `nneg` 定義＋`nneg_embed`, (2) target を `oltRwN ≡ olt∩{omfree∧nneg}²` に変更,
  (3) masterF/L_ThF/bag_mono_wF/acc_of_bag_elemsF を nneg 付きで再証明。
  L_ThF p<n は **0≤p<n** になり**真**（添字 n で帰納の base ができる）が、依然 level machinery（Towsner 3.11）必要。
  ＝負添字偽問題は除去されるが崩壊核は残る（ただし今度は真の目標）。

### 確定 (2026-06-08): nneg 修正後の残作業の正確な姿
**healthy になった**: oltRwF=非負添字フラグメント, masterF/wf_oltRwF は健全, L_ThF p<n は真の目標。
残 headline sorry は2つ（olt_trans[c=Su[a=Su]] は headline 非依存＝dead）:

**(1) L_ThF[0≤p<n]（Buchholz ϑ 崩壊 WF, 真）**:
- 構造: Th n d の acc 証明内, predecessor Th p e (0≤p<n), (∀γ∈Kn p e. γ<o Th n d) 既知, Th p e∈acc を要す。
- p=n(e<o d)は証明済（Towsner 3.10 main-IH=引数 acc 帰納に対応）。p<n は **Towsner 3.11（cardinality/level 降下）が必須**。
- 核心の循環: e は d より大きく得る（添字違い）ので dacc/IH から e∈acc が出ない。masterF 経由は循環（masterF が L_ThF 依存）。
  ⟹ **leveled M_n/Acc_n（Towsner Def 3.7）を Ω-scaffold 込みで構築するしかない**。
- **重要対応**: 私の omfree Th n（添字 n≥0）は Towsner では **自由 Ω_n を持つ項**（FC=n, 可算でない）に対応。
  ∴ omfree fragment の WF を得るにも Towsner の有限 level M_n/Acc_n（自由 Ω 込み）が要る。omfree=可算ではない。
- **要 build**: FC(=max FCset, -∞=空)・G(=min FCset)・K^{<0}(FC<0 の臨界部分項)・norm(=*)・
  M_n/Acc_n を nat level 再帰（primrec で (M_n, ⋃_{≤n}Acc) を返す）, Lemma 3.8(和閉)/3.10(ϑ閉)/3.11(level降下)/Thm3.12。
  ω^ は無いので該当ケース消去。〜数百行の研究レベル formalization。

**(2) op_NF[P/P]（embed の NF 順序保存, 経験的に真 0 反例/7381+ pairs）**:
- three 順序＝principal 列の subscript-first lex。embed＝principal 和（ot の DM/multiset 順序）。
- 一致には **cnf（principal 非増, wf.thy にあり）** が鍵（CNF では lex=自然和順序）。NF⟹cnf を要す。
- principal-level: Th(int a)(embed b) <o Th(int e)(embed f) （a<e or a=e∧embed b<o embed f）を K 条件で示す。
  K 条件は NF の built-from-below（bfb: 引数の臨界部分項添字 ≤ 親+1）に依存。bfb は未形式化（ST_PS 帰納で要証明）。
- 構成: (A) NF⟹cnf, (B) NF⟹bfb, (C) principal 順序保存(bfb 使用), (D) cnf+principal保存 ⟹ lex=DM 和順序。

**結論**: 両核とも substantial な original formalization（leveled-Acc / NF-bridge）。次セッションで (1) の leveled-Acc を
Python で design 検証 → Isabelle 構築、が最有力。今セッションの主成果＝**致命的 soundness バグ(nneg)の発見と修正**。

### 検証済 (2026-06-08): op_NF 分解は正しい（Python 0 反例）
- **NF ⟹ cnf**: 全 NF 項で cnf（兄弟非増）成立（272 項 sample 全て True）。
- **principal 順序保存**: `(a,b)<lex(e,f) ⟹ Th a(embed b) <o Th e(embed f)`（27730 pairs, 0 fail）。
  ＝K 条件（a<e で Kn a(embed b)⊆ <o Th e(embed f)）が embed 像で成立。embed b の内部添字構造（bfb 系）に依存。
- **分解**: (1)`cnf_ST_PS`（ST_PS 帰納, decrease lemma 類似の oper 解析）, (2)`bfb`/principal 順序保存（K 条件）,
  (3)`cnf w∧cnf x∧w<o x(three) ⟹ embed w<o embed x`（非増列で lex=DM 和順序, glue 補題）。
  いずれも **ordinary induction**（非 impredicative）＝ L_ThF の leveled-Acc より achievable。op_NF が先に閉じる見込み。
- tool: `tools/test_op_nf.py`（op_NF・cnf・principal-pres の経験的検証）。

### 検証 (2026-06-08 続): op_NF の a=e ケースは cnf+bfb 必須
- **argument-monotonicity `g<o h ⟹ Th a g <o Th a h` は偽**（一般 wfo omfree nneg でも 13886/231555 反例）。
  反例 g は Su（和, 複数 Th0 principals で cnf 違反）。∴ a=e ケースは NF の cnf+bfb 構造に依存（一般項では不成立）。
- a<e ケースは `Th_lt_of_sub_lt`（Kn_dom）で**証明済・汎用**。a=e は cnf+bfb 必要。
- ∴ op_NF 完成には `cnf_ST_PS`＋`bfb`（ともに ST_PS/oper 帰納, decrease lemma 級の新規開発）が不可欠で確定。
- three 順序を直接 WF にする route(B) も検討したが、three は nat 添字（soundness bug 無し）でも崩壊 WF には
  Om-scaffold 相当が要り ot route と同難度。∴ 既存 ot 資産を活かす route(A) 継続が妥当。

### 残作業の総括（2026-06-08 セッション末）
両 headline 核とも **decrease lemma 級の独立した大規模 formalization**:
- **op_NF**: `cnf_ST_PS`(NF⟹cnf, oper 帰納)＋`bfb`(子添字≤親+1, oper 帰納)＋principal保存(a<e済/a=e要)＋lex=DM glue。
- **L_ThF[0≤p<n]**: leveled M_n/Acc_n（Towsner 3.7-3.12 を絶対 subscripted ψ 用に再導出; FCset≠Towsner FC のため original; Om-scaffold 込み）。
今セッション確定の最重要成果＝**致命的 soundness バグ(nneg)修正**（旧証明は L_ThF=偽に依存し無効だった）。
+ Kn_dom/Th_lt_of_sub_lt/cntbl_downclosed/nneg 機構を証明。architecture は健全化済（残2 sorry は真の目標）。

### 進捗 (2026-06-08 続2): op_NF の a<e ケース完全証明＋glue 基盤完成
- **証明済**: Kn_dom, Th_lt_of_sub_lt（K条件 a<e）, bag_embed/bag_embed_P, collapse_lt_dom/collapse_neq_Zero（DM single-dominator, Zero/singleton/Su 全形）, eprincs_form/eprincs_lt_Th（tail 支配）, tops/cnf_tops_le（cnf 添字上限）, translate_takeWhile_snoc_le, cnf_snoc/cnf_butlast。
- **`op_lt_a`（op_NF の a<e 完全証明）**: cnf w のみで embed(P a b c)<o embed(P e f g)。leading Th(int e)(embed f) が全 summand 支配。
- **残る op_NF**: a=e。
  - principal (b<o f): Th(int a)(embed b)<o Th(int a)(embed f), K条件 r=int a サブケースで bfb 要（embed b の level-(int a) 臨界部分項 h と embed f の関係）。
  - tail (b=f,c<o g): prepend 補題 `collapse xs<o collapse ys ⟹ collapse(d#xs)<o collapse(d#ys)` 経験的成立(0/3710)だが **singleton x=y ケースで ot-irrefl 必要** ＝ olt_trans[c=Su[a=Su]] sorry に依存（headline に dead sorry を再混入させてしまう）。回避には embed 単射性 or ot-irrefl の独立証明 or 別構成。
- **依存関係**: op_NF を閉じるには cnf_ST_PS（w∈NF⟹cnf w, op_lt_a が要求）も必須。
- **重要**: ot-irrefl(olt_trans)が op_NF tail に効いてくるなら、olt_trans[c=Su[a=Su]] は dead ではなく **op_NF 経由で headline 依存** になる可能性。要再検討（embed 単射で回避できるか）。

### 進捗 (2026-06-08 続3): injectivity 完成＋op_NF tail の ot-irrefl 障害の精査
- **証明済**: `embed.uncollapse`/`uncollapse_collapse`/`collapse_inj`/`embed_inj`（embed 単射, c≠g⟹embed c≠embed g）。
- **op_NF tail (a=e,b=f,c<o g) の障害**: prepend `collapse xs<o collapse ys ⟹ collapse(d#xs)<o collapse(d#ys)`
  は d が mset 差で相殺され成立するが、サブケース（xs 多元・ys 単元 y1 で y1∈xs）が **a sum < その summand**
  ＝ y1<o Su xs<o y1 の 2-cycle ⟹ **ot-irrefl(Th)** が要る。ot-irrefl(Th) は第1選言で Kn_lt_Th と cycle になり
  **asym/olt_trans に依存**（既知の entanglement）。∴ **olt_trans[c=Su[a=Su]] は dead でなく op_NF tail に必要**。
- **回避可能性**: cnf により c の全 principal は g の leading より lex-小 ⟹ y1(=g の principal) ∉ eprincs c。
  ∴ application では問題サブケースは起きない。op_cnf tail を**汎用 prepend でなく cnf 構造**で直接証明すれば irrefl 不要。
  ＝ prepend に "dominator ∉ xs" 系の仮定（cnf から導出）を付ければよい。
- **新優先度**: olt_trans[c=Su[a=Su]] は重要度上昇（order meta ＋ op_NF tail 両方）。ただし cnf 経由回避が op_NF には有効。
- mem_lt_Su（α∈set xs⟹isH α⟹α<o Su xs, irrefl 不要）は証明可能で有用。

### 進捗 (2026-06-08 続4): cnf_take 完成＋cnf_ST_PS bad case の分解（sorry 非依存と確認）
- **証明済**: `wf.cnf_take`（cnf は prefix take k で保存, iterated cnf_butlast）。
- **cnf_ST_PS bad case は three-level の機械的証明**（translate は three 値, cnf も three の olt 使用）
  ⟹ **three-olt_irrefl（証明済, sorry 非依存）** を使う。ot-irrefl(olt_trans sorry) には依存しない。安全。
- **構造**: M[n]=take j0 M @ concat(copies)。butlast M = take j0 M @ block（block=M[j0..j1)）。
  ∴ M[n] = butlast M @ C（C=copies 1..n-1）。cnf(butlast M) は cnf_butlast。
  - **i1=0** (d0=0): C=block^{n-1}（block=butlast M の trailing block の複製・等しい siblings）。
    append-one-block で兄弟 (w0, translate R) が Z-tail 比較で不変 ⟹ cnf 条件不変、内部は ¬(x<o x)=three-irrefl。
    ＝ `cnf_dup_trailing`（trailing block 複製で cnf 保存）＋ n 帰納。
  - **i1=1** (d0>0): copies は昇順で nest（単一深化木）。core_i1 構造。別途。
- **残**: cnf_dup_trailing（i1=0, ~50行, boundary 解析）＋ i1=1 nesting（~50行）＋ assembly。three-level なので安全だが分量大。
- ＋ bfb_ST_PS（a=e principal 用）＋ op_cnf assembly ＋ L_ThF leveled-Acc。

### 進捗 (2026-06-08 続5): cnf 機械を全証明、cnf_ST_PS 組立だけ残す
**証明済の cnf 機械（全緑・commit済）**:
- `mechanized.translate_block_append`（block@reopening-tail = 単一 principal）
- `wf.cnf_replicate_block`（block^n は cnf, i1=0 exact-copy core, three-irrefl 使用）
- `wf.cnf_ctx_cong`（cnf 文脈合同: cnf(G@Z2)⟹cnf(G@Z1), 一般化 b1≤o b2 で i1=0/i1=1 両対応; translate_ctx_cong+three-trans で境界保存）
- `wf.cnf_tail`（cnf(G@T)⟹cnf(T), tail 抽出）
- `wf.cnf_take`/`cnf_butlast`/`cnf_snoc`/`cnf_tops_le`

**残: cnf_ST_PS の組立**（ST_PS 帰納）:
- diag: cnf_diag。oper short(Lng≤1): M[n]=M, IH。oper Pred: cnf_butlast。
- oper bad（cnf_oper_bad）: M[n]=take j0 M @ concat(copies)。setup は translate_oper_bad 模倣(j0,j1,B,C,R)。
  - Z1=B@C, Z2=B@[lp], G=take j0 M。cnf M=cnf(G@Z2)。
  - cnf(B@[lp])=cnf_tail[cnf M]。これから cnf(R)[i1=0] or cnf(R@[lp])[i1=1]。
  - cnf(Z1)=cnf(B@C): **i1=0 は cnf_replicate_block[cnf R] で OK**。
    **i1=1 は cnf(R@C) が要る＝ascending copies の cnf（未）**: shift 不変性（row-0 一様 shift+row-1 不変で translate 不変）＋ n 帰納+cnf_ctx_cong で nesting 各段保存、が筋。`cnf_nest` として要証明。
  - decr=translate(B@C)<o translate(B@[lp])（core_i0/core_i1）。lead(b1≤o b2): i1=0 同 b=translate R; i1=1 b1=translate(R@C)<o b2=translate(R@[lp])。
  - cnf_ctx_cong 適用 → cnf(M[n])。
- **次セッション**: (1) cnf_nest(i1=1 ascending copies cnf), (2) cnf_oper_bad 組立, (3) cnf_ST_PS。その後 bfb_ST_PS, op_cnf 組立, L_ThF leveled-Acc。

### 進捗 (2026-06-08 続6): translate_shift 証明＋i1=1 cnf の難所分析
- **証明済**: `mechanized.translate_shift`（row-0 一様 shift で translate 不変）。
- **i1=1 cnf の難所**（cnf_oper_bad の唯一の未解決部）:
  - 外側 cnf_ctx_cong[Z1=B@C, Z2=B@[lp], G=take j0 M] は OK（B 共有で lead 成立, b1=translate(R@C)≤o b2=translate(R@[lp])）。
  - 唯一要るのは **cnf(translate(B@C))=cnf(translate(R@C))**（i1=1 は単一木 P w0 (translate(R@C)) Z）。
  - **内側 cnf_ctx_cong[Z1=C, Z2=[lp], G=R] は使えない**: C(=cp1@..)の先頭 (v0+d0, w0) と lp=(v0+d0, row1 j1) は
    row-0 同じだが **row-1 が異なる**（RedCondA: j0=parent1(j1) で row1 j0 = row1 j1 - 1 = w0 ≠ row1 j1）。
    ∴ lead（同 subscript）不成立。
  - **筋（次セッション）**: R@C は「good prefix R @ tiled copies C」＝**bad block を一段内側に入れた構造**で、
    **cnf_oper_bad が再帰的**（i1=1 は block 深さで nested induction, 各 copy は translate_shift で同一 translate）。
    or: cnf_nest を n 帰納で（M[n+1]=M[n]@cp n, cp n は最深 block を append）＝append-deeper cnf。
  - i1=0 側は cnf_replicate_block で解決済（cnf(B@C)=cnf(block^n)）。
- **要点**: cnf_oper_bad の組立は (1) oper setup(~40行, translate_oper_bad 模倣), (2) i1=0=cnf_replicate_block,
  (3) i1=1=cnf_nest(上記, 再帰 or append-deeper), (4) cnf_ctx_cong 適用。i1=1 が research-level の残核。

### 進捗 (2026-06-08 続7): cnf_oper_i1eq0 完全証明＋i1=1 の de-risk
- **証明済 (no sorry)**: `wf.cnf_oper_i1eq0`（i1=0 oper bad ケース完全）。cnf_ST_PS の i1=0 分岐 完了。
- **i1=1 の重要発見（Python 検証）**: i1=1 bad block `[j0,j1)` の **row-0 は strictly increasing**（17/17）。
  ⟹ block は各列が前列の**引数位置(b)に nest する純 tower**（兄弟なし）。
  純 b-nesting tower（tail 全部 Z）は **cnf 自明**（cnf(P a b Z)=cnf b で Z まで降下）。
  ⟹ **cnf_oper_i1eq1 は当初恐れたより容易**: copies も chain で、R@C が（ほぼ）純 nesting tower ＝自明 cnf。
  - edge: block-max = row0(j1) のケース（1/17）で cp1 root が block 末と同レベル → sibling 生成の可能性。
    その場合のみ sibling 順序条件（cnf_ctx_cong or 順序）要。大半は純 nesting で自明。
- **次セッション cnf_oper_i1eq1 方針**: (1) `block_row0_increasing`（i1=1 で block row-0 strictly inc を ST_PS から証明、
  climb 構造由来）, (2) 純 nesting tower の cnf 自明補題（or translate が単一 b-chain ⟹ cnf）, (3) edge ケース処理。
  ＝当初の「再帰 cnf_oper_i1eq1」より直接的。
- **cnf_ST_PS 組立**: ST_PS 帰納＋oper setup で cnf_oper_i1eq0（i1=0）/i1eq1（i1=1）を instantiate。

### 進捗 (2026-06-08 続8): cnf_ST_PS 完全証明（cnf 機械 全完成、wf.thy sorry=0）
- **続7 の de-risk は誤りだった**: i1=1 bad block の row-0 は **厳密増加とは限らない**（Python 再検証で
  reduced ST_PS 6000 サンプル中 351 件が非増加、例 `(0,0)(1,1)(1,1)(1,1)` の block row0=[0,1,1]）。
  純 nesting tower 戦略は不成立。ただし **cnf(translate M) は全 6000 ST_PS で成立**＝cnf_ST_PS は真。
- **正しい構造**: `translate(R@C)` は自己相似。`copies d0 blk (Suc n) = blk @ shiftr0 d0 (copies d0 blk n)`
  （front-peel）＋ translate の shift 不変性。鍵は **w0 < snd lp**（i1=1 の row-1 増加）による spine 支配。
- **手法**: `cnf_ctx_cong` を「先頭 principal 非増加 `P a1 b1 Z ≤o P a2 b2 Z`」に一般化（a1<a2 も許可。
  subscript が縮むと sibling 条件は easier ＝ olt_ole_trans 一発）。これで i1=0/i1=1 両対応。
- **新規証明 (all no sorry, wf.thy)**: `shiftr0`/`copies` 定義＋補題群（shiftr0_shiftr0/_concat/_0/Nil,
  translate_shiftr0, copies_Suc_front/_0/_1/_replicate/_v0_le/_tl_gt, hd_copies, copies_nonempty）,
  `cnf_copies`（n コピーの cnf, copies_Suc_front 帰納＋一般化 cnf_ctx_cong）,
  `cnf_oper_i1eq1`（自己完結: core_i1 で decr 内部導出）, `cnf_oper`（全 oper 分岐: Pred=butlast/cnf_butlast,
  bad=cnf_oper_i1eq0/i1eq1）, `cnf_ST_PS`（ST_PS 帰納）。
- **新規 (mechanized.thy)**: `oper_bad_blocks`（bad 分岐分解を obtains で公開: M=G@blk@[lp],
  oper M n=G@copies, R条件, v0<fst lp, d0=0∨(0<d0∧w0<snd lp∧fst lp=v0+d0)）。
- **罠**: obtain の discharge を `by blast` にすると **無限ループ**（∀set+∨ で blast 探索爆発, 400s timeout）。
  `by (rule oper_bad_blocks[OF ...])` で決定的に解決。また translate を大 symbolic 項へ展開する `by simp` も
  遅い→ list 等式を別途立て `by (simp only: leq)` で回避。
- **残る headline sorry は 3 つのみ**: wo.olt_trans[c=Su[a=Su]], buchholz.L_ThF[0≤p<n], embed.op_NF[P/P]。
- **次**: op_NF（cnf_ST_PS 入手済→ NF は cnf 使用可）。bfb_ST_PS（principal bag finite/bounded）＋
  op_NF の a=e principal ケース＋op_cnf 組立。その後 L_ThF leveled-Acc, wo.olt_trans。

### 進捗 (2026-06-08 続9): 方針決定（ユーザー指示）＝(A) L_ThF → olt_trans → op_NF。Pohlers §9.6.2 取得
- **ユーザー方針**: 私の推奨 (A) L_ThF を transitivity-free で先に閉じる → olt_trans → op_NF の順。
- **参考文献**: `../1989-W.Pohlers-Proof-theory-The-first-step-into-impredicativity.pdf`。
  §9.6.2「The well-ordering proof」= printed 114-117 = **PDF page 116-119**。§9.6.1(coding) = printed 108-113 = PDF 110-115。
- **L_ThF の現状（重要）**: buchholz.thy の L_ThF は**既に 9 割完成**。`d∈acc oltRwF` の acc 帰納で、
  `Th n d` の accI: r<o Th n d を場合分け: (Su=和)→`acc_of_bag_elemsF`済 / (Th p e, disj1 Kn支配)→`dom_acc`済 /
  (disj2 p=n∧e<o d)→acc帰納IH済 / **(disj2 0≤p<n)のみ sorry**。残りはこの1ケースだけ。
- **olt_trans 依存に注意**: 現 L_ThF は olt_trans（未証明 sorry）を**使わず**書かれている（Kn_le_self/olt_Th_of_le_Kn/
  Kn_mono_le=「一般推移律なし」）。p<n も同じ Kn スタイルで推移律を避けて埋める。
- **Pohlers §9.6.2 構造（写経元）**:
  - 9.6.9 定義: `α<0 β ⟺ α<β<Ω`(=oltRwF), `Acc≡Acc(<0)`(=acc oltRwF), `M:={α|SC(α)∩Ω⊆Acc}`(controlled),
    `α<1 β ⟺ α<β∧α∈M∧β∈M`(M制限), `Prog_i(F):=∀ξ∈field(<i).(∀η<i ξ.F η)→F ξ`, `TI_i(α,F)`。
  - 9.6.12: Acc は + で閉（→`acc_of_bag_elemsF`済）。9.6.13: Prog_1→Prog_0。9.6.14: Acc は Veblen φ で閉
    （**ot には φ 無し→omfree 断片では Su 和のみ＝9.6.12 で尽きる。この段は不要/自明**）。
  - **9.6.15(核)**: `Acc_Ω:={α| α∉M ∨ (∃ξ∈K(α).α≤ξ) ∨ ψ(α)∈Acc}` に対し `Prog_1(Acc_Ω)`。
    証明: α∈M ∧ K(α)⊆α と仮定→ψ(α)∈Acc を示す→`∀ρ<ψ(α).ρ∈Acc`を**ρの項長帰納**で:
    ρ∉SC→SC(ρ)⊆Acc(IH)+9.6.12で ρ∈Acc。ρ∈SC→∃ρ0.K(ρ0)⊆ρ0<α,ρ=ψ(ρ0)。SC(ρ0)∩Ω の各 ξ=0 or ψ(η)で
    η∈K(ξ)⊆K(ρ0)⊆ρ0<α かつ ξ=ψ(η)<ψ(α)→項長IHで SC(ρ0)∩Ω⊆Acc→ρ0∈M かつ ρ0<α→ρ0<1 α→
    **外側 Prog_1 仮定**で ρ0∈Acc_Ω→(K(ρ0)⊆ρ0,ρ0∈M)第3選言で ψ(ρ0)=ρ∈Acc。
  - **9.6.16 Condensation**: K(α)⊆α,α∈M,TI_1(α,F)⟹ψ(α)∈Acc。9.6.15+TIで ρ0∈Acc_Ω→ψ(α)∈Acc。
- **ot への相対化（追加設計＝p<n の正体）**: Th n a はレベル n 付き。Pohlers の単一 ψ を「レベル n、p<n は
  下位 Acc に既収」と読む。`Mn`/`AccB`/`Acc n`（既存, `Acc_subset_AccB:m<n⟹Acc m⊆AccB n`完備）がレベル別 Acc。
  p<n ケース: Th p e の acc は **n の外側帰納の下位レベル IH**＋e の controlled 性（Kn p e の臨界部分項が下位 acc）で。
  核は「e が controlled ⟹ e∈acc」＝Pohlers 9.6.15 の項長帰納に相当。
- **設計上の注意**: ctrl/Acc_Th を新設するより既存 Mn/AccB を使う（wf_oltRwF 配線の二重化回避）。9.6.14(φ)段は不要。
- **次の一手**: L_ThF を n の外側強帰納に再構成し、p<n を controlled-set（Mn/AccB）＋下位 IH で埋める。
  推移律を避ける。まず statement ラダーを sorry 骨組みで compile→核(9.6.15 項長帰納の崩壊サブケース)を埋める。

### 進捗 (2026-06-08 続10): L_ThF 再構成完了＋核の正確な所在
- **DONE (commit, 緑)**: `L_ThF` を **外側=レベル k 強帰納(less_induct on nat k, n=int k)＋内側=d の acc 帰納**に再構成。
  p<n ケースは `p=int j, j<k` で **levelIH(下位レベル)** により `Th p e∈acc` を `e∈acc` から導出。
  残 sorry は **`eacc: e∈acc oltRwF`** 1点のみ（dom_acc/eq(=accIH)/Su(=bag) は全て既済）。olt_trans 不使用を維持。
- **核 `e∈acc` の難所（重要分析）**: e は omfree/wfo/nneg（→最終的に masterF で acc だが masterF は L_ThF 依存で循環）。
  文脈: `∀γ∈Kn p e. γ<o Th n d`(Acond), p<n。
  - **構造帰納 on e は破綻**: e=Th q h で **q≥n** の場合（p<q なので Kn p e=Kn p h に潜るが e 自身の level q は ≥n）、
    levelIH(level<n のみ) が効かず e∈acc を出せない。同レベル/上位 level の Th collapse を扱えない。
  - ∴ **Towsner 3.10-3.11 / Pohlers 9.6 の完全 distinguished-set 構成が必要**。
- **既存機構の整理**: `Awf S`=S の acc 部分(汎用), `wf_on_Awf`=Awf 上 wf（済）。`Mn n prev`/`AccB`/`Acc n`=
  **幅(ground/FCset cardinal, `nat(-gnd a)≤n`, `Klt`=Kn 0∩below Om0)で stratify** した distinguished set
  （`Acc_subset_AccB:m<n⟹Acc m⊆AccB n`完備）。注意: この stratify 軸は **Om-幅** であって **Th-subscript n とは別軸**。
  masterF はこの2軸（幅 collapse=Mn/AccB と subscript collapse=L_ThF）を構造帰納で組合せている。
- **核の正しい筋(Pohlers 9.6.15 写経, 要 Mn/AccB)**: `controlled a ≡ a の臨界部分項(SC∩Ω=Kn-below-Om)が下位 Acc に入る`
  を定義し、`controlled a ⟹ a∈acc` を **a の項長帰納**で: a∉SC→SC(a)⊆acc(IH)+bag閉包/9.6.12。
  a∈SC(=Th collapse)→arg の controlled 性＋ `<1`(M制限順序)の Prog で acc。e の controlled 性は Acond の
  γ<o Th n d 達が（下位 level/acc IH で）acc になることから。**これが残りの全作業**。
- **olt_trans の扱い**: 核を Kn-style(推移律無し)で書けるか要検討。書けなければ olt_trans を先に閉じる必要。
- **次セッション**: controlled 述語＋`controlled⟹acc`(9.6.15) を statement で置き(sorry骨組)→compile→
  項長帰納の崩壊サブケースを Mn/AccB と levelIH/accIH で埋める。op_NF/olt_trans はその後。

### 進捗 (2026-06-08 続11): advisor 改訂計画＝olt_trans 先行。出典・帰納形・順序の確定
- **advisor 補正(出典)**: q≥n の壁の精密な出典は Pohlers §9.6 ではなく **Towsner §3.2 Lemma 3.10/3.11**
  （多レベル Ω_n collapse 閉包＝二軸）。Pohlers 9.6.15=単レベル帰納の型、Towsner 3.10/3.11=多レベル二軸版。
  Towsner は相対 shifting(α^{≤0}_{-1}, α*)で書くので、それを剥がして絶対系 Mn/AccB へ写す。
- **advisor 補正(帰納形)**: 「e の構造帰納」は誤り。正しくは **「引数 α∈Acc_n の main 帰納(整礎部分の accessibility 帰納)
  ＋ predecessor γ の内側構造帰納」**。predecessor γ=Th q h(q≥n 含む)は **M_n(controlled)条件＋main IH** で吸収。
  subscript ごとの level 帰納は不要。q≥n が levelIH で届かないのは正しいが、届かせる必要が無い。
- **advisor 回答 Q1**: 既存幅 Mn/AccB 再利用(新述語最小)。二軸は M_n が FC-ground(幅)＋K-control(bfb=臨界部分項が
  下位 Acc)を1述語に束ねて統合。**確認事項**: 既存 Mn が K-control(bfb)を持つか。無ければ最小限足す。
  真に新規なのは「collapse 閉包補題(3.10)を main-on-argument 帰納で証明」1補題のみ。
- **advisor 回答 Q2＋順序改訂**: 前回「L_ThF 先行」は「残り1ケースの早い勝ち」前提で、それは今や偽(e∈acc は
  impredicative の核そのもの)。**順序を改訂: olt_trans → L_ThF核(Towsner 3.8/3.10 転写) → op_NF(FC最重量,最後)**。
  理由: olt_trans 残(c=Su[a=Su])は combined induction で closeable、(a)op_NF 和ケース解禁、(b)核のクロスレベル
  合流(Towsner 3.8 の multiset/和)解禁。核を transitivity-free に縛ると結局 olt_trans 要で二度手間リスク。
- **advisor 健全性確認点**: main-on-arg 帰納の整礎性(e∈Acc_n, predecessor 厳密下位, 外側 level 帰納と非循環)、
  「collapse はレベルを下げる」(Towsner 3.11: level n 崩壊→⋃_{m<n}Acc_m)が絶対系 encoding で成立すること。
- **olt_trans の難所(私の分析)**: sorry は wo.thy の c=Su,a=Su(¬isH a)＝**Su/Su/Su 一段 DM 推移律**(Towsner 3.8)。
  **単一支配元 one-step DM `∃β∈ms ys-xs.∀α∈ms xs-ys.α<o β` は、base order が全順序でないと推移的でない**
  （反例: α1<β1,α2<β2,他は incomparable な部分順序で Su{α1,α2}<Su{α2,β1}<Su{β1,β2} だが ¬(Su{α1,α2}<Su{β1,β2})）。
  ∴ ot 上で olt が**全順序であること(totality)を併せて要する**。現状 asym/irrefl は trans 依存で、totality 未証明。
  → **trans + totality(asym/trichotomy) を combined induction で同時証明**が必要（summary の 3-way 相互依存）。
  全順序なら「対称差の最大元」で Su DM 推移律が出る。これが olt_trans を閉じる本体。
- **olt_trans 実装方針**: `olt_tri: a<o b ∨ a=b ∨ b<o a`(totality) と `olt_trans` を1つの size 帰納で相互に証明。
  Su/Su/Su trans は tri(下位要素)で max 元論法、または witness 直接操作。まず tri 単独が size 帰納で閉じるか試し、
  trans の Su ケースで tri を使う。olt_asym/irrefl は tri+trans から従う。

### 進捗 (2026-06-08 続12): olt_trans を Python 検証＝真だが ot 固有性に依存（重要）
- **olt/Kn を Python 移植して検証**: ot 小項(depth2, subscript0-3, 145項/Su101項)で **olt_trans 反例ゼロ**＝真。
  Su[u,v] と Su[v,u] は <o-incomparable かつ ≠（**olt は ot 上で全順序でない**）が、それでも trans は成立。
- **決定的発見**: 単一支配元 one-step DM `∃β∈ms ys-xs.∀α∈ms xs-ys.α<o β` は **抽象的には推移的でない**。
  反例(抽象 transitive+asym 部分順序): a1<b1, a2<b2, 他 incomparable で
  A={a1,a2}≺B={a2,b1}≺C={b1,b2} だが A⊀C（b1 は a1 のみ、b2 は a2 のみ支配、単一支配元が無い）。
  ∴ **olt_trans の Su 節は asym だけの汎用 multiset 論法では証明不可。ot 固有の totality/trichotomy が要る**。
- **ot 固有性の正体**: ot では a1<b1∧a2<b2∧a1⊥b2∧a2⊥b1 という配置が起きない（incomparable は Su-permutation 等
  限定的で、上記反例パターンを実現できない）。これを保証するのが **ot 上の trichotomy**。
- **∴ olt_trans 実装**: `olt_trans` ＋ `olt_tri`(ot 上の三分律: x<o y ∨ y<o x ∨ x≃y)を **1つの size 帰納で同時証明**。
  ≃ の定式化が要注意（Su-permutation incomparable は ≠ かつ ⊥）。Su/Su/Su trans は tri(下位)で対称差の最大元論法。
  これは Towsner Lemma 2.1 の順序メタ理論本体＝数百行規模の combined induction。olt は wfo 制限なしの無条件命題なので
  trichotomy も全 ot で要る（あるいは olt_trans を wfo/normalized 断片に制限する設計変更も選択肢）。
- **Python 検証スクリプト**: /tmp/olt_check.py（olt/Kn 移植＋反例探索）, /tmp/abstract_dm.py（抽象 DM 非推移性）。
- **設計判断ポイント(要相談 or 自走)**: (i) trichotomy ≃ をどう定式化するか、(ii) olt_trans を無条件のまま combined
  induction で攻めるか、それとも実利用箇所(oltRwF=wfo∧omfree∧nneg)に合わせ wfo 断片へ制限して totality を確保するか。

### 進捗 (2026-06-09 続13): advisor 出典補正＋Path 決定（Path B＝DM 維持）
- **advisor 出典補正**: linearity の出典は Towsner ではなく **Buchholz 1986 [Buc1] Lemma 2.1**（<が T 上の狭義全順序）。
  Towsner は Def 2.3 で順序定義のみ。**姉妹 repo pss-proof §7.1 が [Buc1] Lemma 2.1 を既に形式化**
  （`lessBT`/`lessBP` を**降順ソート済リスト＋辞書式 lex**で持ち, lessBT_irrefl/trans/total を相互構造帰納で**無条件**証明, repo 全体 sorry 6個）。
- **難所の根本原因（advisor）**: 2 repo の「和」表現の違い。pss-proof=ソート済リスト+lex（lex は成分全順序なら無条件に全順序・推移的）。
  ya-pss(本 repo)=Su を **multiset(#)** で持ち単一支配元 DM。私が見つけた DM 非推移性も Su permutation 非全順序も**全て multiset-# 表現の副産物**。
- **Path A（辞書式ソート表現へ替える）**: linearity が pss-proof からほぼ移植・無条件。permutation も DM 非推移性も消滅。
  **コスト測定→禁止的**: mset/mult/Su 依存が wo(142/64/120)・buchholz・embed・wflevel(54/37)・accinfra 全体 ~3000行に深く浸透。
  整礎性も lex(int 添字)では非整礎で別途やり直し（現 mult 整礎機構が好適）。**∴ 不採算**。
- **Path B（DM 維持, 採用）**: olt_trans を combined induction で。Su/Su/Su trans は単一 witness で閉じない
  （β1∈ms bs∩ms zs の sub-case で β2 が α を支配せず詰まる）→ **tri-mod-≃(≃=hereditary mset 同値)が必須**。
  ≃ は inductive で定義（eqv(Om m)(Om m); eqv(Th m a)(Th m b)←eqv a b; eqv(Su xs)(Su ys)←要素 eqv の mset 同値）し、
  (1)同値関係(2)olt-congruence(olt x y=olt x' y' when eqv x x', eqv y y')を証明→ combined `trans + (x<o y ∨ eqv x y ∨ y<o x)`
  を size 帰納で。Su trans は eqv-商上の線形性（対称差の最大元）で。
- **DECISION**: Path B。次は eqv 定義＋combined trans+tri を wo.thy に実装。olt_asym は既存(無条件・独立)を流用可。
- **作業順(確定)**: olt_trans(Path B) → L_ThF核(Towsner 3.10/3.11+Pohlers 9.6.15, main-on-arg 帰納) → op_NF(FC構造, Buchholz survey k⁺/Thm 2.4)。
- **強度ラベル**: TFBO = ψ_0(ε_{Ω_ω+1})（survey §4-5）。

### 進捗 (2026-06-09 続14): multp ライブラリ調査＋single-dom vs multp の wrinkle
- **advisor 指針**: HOL-Library.Multiset_Order の `multp` で対称差-最大元論法は既済。olt_Su を multp に橋渡し→trans/tri 継承。
  ≃-congruence は mset 経由で自動（top-level）。
- **Isabelle2025-2 (/opt/Isabelle2025-2) の Multiset_Order 補題**: `multp`/`multp\<^sub>D\<^sub>M`(DM)/`multp\<^sub>H\<^sub>O`(HO),
  `transp_multp\<^sub>H\<^sub>O`(trans のみ要), `totalp_multp\<^sub>D\<^sub>M`/`totalp_multp\<^sub>H\<^sub>O`(total 要),
  `asymp_multp\<^sub>H\<^sub>O`(asym+trans), `multp_eq_multp\<^sub>D\<^sub>M: asymp r⟹transp r⟹multp r=multp_DM r`,
  `multp\<^sub>D\<^sub>M_imp_multp`, `multp_imp_multp\<^sub>H\<^sub>O`, `multp\<^sub>H\<^sub>O_implies_one_step_strong`。
  ※wo.thy は現状 `HOL-Library.Multiset` のみ import。Multiset_Order を足す必要。
- **wrinkle（重要）**: olt-Su は **単一支配元** `∃b∈Y.∀a∈X.a<b`。multp_DM は **複数支配元** `∀a∈X.∃b∈Y.a<b`。
  **single-dom ⊊ multp_DM**（single⟹multp は易、逆は uniform max が要＝totality）。∴ 橋渡し `olt_Su⟺multp` は
  **成分全順序のときのみ**。permutation 非全順序のため無条件には不成立。
- **olt_trans が真の本当の理由（確定）**: **olt が ≈-不変(hereditary permutation congruence)**。これが反例配置
  a1<b1∧a2<b2∧a1⊥b2∧a2⊥b1 を矛盾(b2≈a1<b1→b2<b1, a2≈b1<b2→b1<b2, asym 矛盾)で排除。
  shallow(top-level Su)congruence は olt 定義が mset 使用なので自動。hereditary(Th 引数内 permutation)は congruence 帰納が要る。
- **olt_trans 実装の確定方針（2案）**:
  - 案1: olt ≈-invariance(hereditary congruence)を帰納で証明 → 反例排除 → single-dom trans を asym+IH+多重集合帳簿で。
  - 案2: olt-Su を multp_HO に橋渡し(transp_multp_HO は trans のみ要)。ただし single-dom=multp_HO が成分全順序要なら
    結局 ≈ 経由。multp_HO_implies_one_step_strong が単一支配元への橋渡しに使える可能性大→要確認。
  - いずれも「olt が成分の ≈-class 上で全順序」を確立するのが鍵。multp ライブラリは ≈-class が = に潰れた multiset 上で動く。
- **次**: (a) Multiset_Order を import、(b) olt-Su ⟷ multp_HO/DM の橋渡し補題を試作(single-dom と multp_HO_implies_one_step_strong
  の関係確認)、(c) 成分 linearity-mod-≈ を構造帰納で、(d) trans/tri をライブラリ継承。≈ は mset 経由で極力自動化。

### 進捗 (2026-06-09 続15): Path B 実装＝(b1) 採用。multp は単一支配元を直接与えない確定＋mnl 簡略化
- **multp_HO_implies_one_step_strong 確認**: `∀k∈K.∃x∈J. R k x`（複数支配元）。olt-Su は `∃b∈J.∀k∈K` 単一支配元。
  **single-dom ⊊ multp、ライブラリは drop-in でない**確定。
- **(b2) olt-Su を multp に再定義は技術的に不可/高リスク**: olt の function 定義に `multp olt` を入れると
  関数パッケージが（higher-order・非構造再帰で）termination を通しにくい。現 single-dom 節は size 再帰で素直。∴ **(b1) 採用**。
- **(b1) の簡略化（重要）**: 別途 `oteq` を inductive 定義＋congruence 証明…ではなく、**`mnl x y ≡ ¬(x<o y)∧¬(y<o x)`**
  （olt から直接、asym より refl+sym）を使い、**combined size 帰納で `olt_trans` ＋ `mnl 推移的`(=olt が strict weak order
  =mnl-class 上で全順序)を同時証明**。Su/Su/Su trans は mnl-class 上の対称差最大元で single-dom を構成。
  これで hereditary oteq の inductive 定義と olt-congruence の手書きを回避。
- **building block（易方向, 無条件）**: `olt(Su xs)(Su ys) ⟹ multp\<^sub>D\<^sub>M (<o)(mset xs)(mset ys)`
  （X=ms ys-ms xs, Y=ms xs-ms ys, 単一 b が各 k を支配）。逆は totality 要（mnl で代替）。
- **実装順**: import Multiset_Order → olt_Su_imp_multp_DM(易) → mnl 補題群(refl/sym, asym から) →
  combined trans+mnl-trans(size 帰納, Su は multp の transp/totalp 補助＋mnl-class max) → olt_trans 完成。
- **注意**: wo.thy の import 変更は全 rebuild(~13s)。olt_asym は既存(無条件)流用。

### 進捗 (2026-06-09 続16): advisor 訂正＝single-dom は全順序成分上で multp と一致（懸念は杞憂）
- **訂正(安心材料)**: single-dom ⊊ multp は**部分順序**の話。**全順序成分上では single-dom = multp**
  （max 元論法: multp_HO の ∀k∈X.∃y∈Y.k<y、Y 全順序有限非空 → max(Y) が X を単独支配; 逆 single⊆multp は自明）。
  ot principal は ≃ を法に全順序 → **wfo 断片で olt-Su = multp**。∴ single-dom は標準 DM/Buchholz 順序の単一支配元表記。
  embed.collapse_lt_dom の単一支配元構成も妥当な multp witness。**「順序が変」ではなく one-step 形なので推移律に成分全順序が要るだけ**。
- **(b1) 確定**（advisor 同意）。(b2) 旨み小（wfo で multp=single-dom、再検証コストのみ。embed single-dom 補題は b1 で無傷）。
- **技法2択**: **(A) 橋渡し**: wfo 上 `olt-Su = multp (<o)` を示し library の transp_multp/totalp_multp(or _on 版)継承。
  逆向き(multp⟹single-dom)は `one_step_implies_multp` 系＋全順序での max 元一致。multp は「全 ot で≠」でも全順序 carrier 上で使える。
  **(B) 直接**: 成分全順序(相互 IH)前提で max(Y∪Y') が合成対称差を単独支配、を手書き。→(A) 推奨(library 活用)。
- **≃ 最小化(重要)**: olt-Su は既に **mset 経由定義**（節が mset xs/mset ys 使用）ゆえ **Su レベル ≈-不変は構成上自動**。
  congruence の手作業は **Th/Om の hereditary 再帰部のみ**(~50-100行削減)。
  代替: Su を真の ot multiset(BNF nested `Su "ot multiset"`)化すれば permutation=等号で ≃ が = に潰れ congruence 消滅
  （ただし list 構造依存(embed/wflevel)の改修が要り invasive。Path A の lex 化よりは小だが今は見送り）。
- **着手順(advisor 推奨)**: ≃ の扱い見極め(multiset 化するか/mset 経由 congruence か) → 橋渡し補題(olt-Su=multp on wfo) → library 継承。
- **次セッションの具体手順**: (1) `olt_p_total`(principal Om/Th が ≃ 法で全順序)を構造帰納で, (2) 逆橋渡し
  `multp(<o)(mas)(mbs) ⟹ olt(Su xs)(Su ys)`(全順序成分・max 元), (3) olt_trans Su を 易橋渡し(済)+transp_multp+逆橋渡しで.
  combined: principal total と olt_trans は相互依存(Th/Th が arg の trans/total を要する)ので 1 つの size 帰納で。

### 進捗 (2026-06-09 続17): olt_trans の実行可能レシピ確定（全ライブラリ部品特定）＋極大性で mnl-trans 不要判明
- **完了(commit/緑)**: `olt_Su_imp_multp\<^sub>D\<^sub>M`(易・無条件), `olt_Su_imp_multp`(forward 橋渡し, multp\<^sub>D\<^sub>M_imp_multp 経由)。
- **重要簡略化**: 逆橋渡しの極大元 m は **極大性だけ**で `∀x∈J. x=m ∨ ¬olt m x` を満たす（mnl-trans/weak-order 不要！）。
  各 k∈K に対し ∃x∈J. olt k x、x≤m を: x=m→olt k m; x≠m→¬olt m x、さらに olt x m なら trans で olt k m、
  ¬olt x m なら mnl x m で **mnlcong** より olt k m。∴ 要るのは **trans + mnlcong のみ**（mnl-trans 不要）。
- **全ライブラリ部品(Isabelle2025-2 確定)**:
  - `Finite_Set.bex_max_element`: `finite A ⟹ asymp_on A R ⟹ transp_on A R ⟹ A≠{} ⟹ ∃m∈A.∀x∈A. x≠m⟶¬R m x`（極大元）。
  - `multp\<^sub>D\<^sub>M_imp_multp`, `multp_imp_multp\<^sub>H\<^sub>O`(asymp+transp 要), `multp\<^sub>H\<^sub>O_implies_one_step_strong`(J=B-A≠{}, ∀k∈#A-B.∃x∈#B-A.R k x),
    `transp_on_multp\<^sub>H\<^sub>O`(wo.thy line 312, transp_on で), `totalp_on_multp\<^sub>D\<^sub>M`/`\<^sub>H\<^sub>O`。
  - asymp: olt_asym(既存・無条件)→ asymp_on 自明。
- **olt_trans Su レシピ**: ab,bc →(olt_Su_imp_multp)→ multp 2本 →(transp on summands=IH で transp_multp or _on)→ multp(mas)(mzs)
  →(multp_imp_multp\<^sub>H\<^sub>O)→ multp\<^sub>H\<^sub>O →(one_step_strong)→ J=mzs-mas≠{} ∧ ∀k∈K=mas-mzs.∃x∈J. k<o x
  →(bex_max_element on set_mset J, asymp_on=olt_asym, transp_on=IH)→ 極大 m∈J
  →(各 k: x≤m を trans/mnlcong で k<o m)→ ∃m∈#(mzs-mas).∀k∈#(mas-mzs). k<o m = olt(Su as)(Su zs)。
- **残実装 = combined size 帰納 `olt_trans + mnlcong`**（両 3 項・同 induction）:
  - trans: 既存 olt_trans の証明（c=Om/Th/Su[a principal] 済）＋ Su[a=Su] を上記レシピで。
  - mnlcong: `olt k x ∧ ¬(x<o m) ∧ ¬(m<o x) ⟹ olt k m`（=olt が ≃ を右で尊重, ≃-congruence）。Su-level は mset 経由自動、
    Th/Om hereditary を帰納で。olt_asym は流用。
  - mnlcong も summands(smaller)で要るので combined IH に同梱。size 測度は (size k+size x+size m) 等。
- **実装の安全則**: wo.thy を壊さないため、緑コミット毎に。combined への restructure 前に現 olt_trans(1 sorry)は緑。
  まず `multp_imp_olt_Su`(逆橋渡し, mnlcong+transp_on を仮説に取る形)を独立補題で緑化→次に combined で仮説供給。

### 進捗 (2026-06-09 続18): forward/reverse 橋渡し完成（olt_trans の hard core 済）＋olt_asym は非独立判明
- **完成 (commit/緑, wo.thy, olt_trans の前に配置)**:
  - `olt_Su_imp_multp\<^sub>D\<^sub>M` / `olt_Su_imp_multp` / `olt_Su_imp_multp\<^sub>H\<^sub>O`（forward 橋渡し3本, 単一支配元⟹各 multiset 順序, 無条件）。
  - **`multp\<^sub>H\<^sub>O_imp_olt_Su`（reverse 橋渡し＝最難関の最大元論法, 完成）**: 仮説 `asymp_on/transp_on (set xs∪set ys)` ＋
    `mnlcong`(k∈set xs, x m∈set ys: k<o x ∧¬x<o m∧¬m<o x ⟹ k<o m)。証明: one_step_strong→`Finite_Set.bex_max_element`で
    surplus(mset ys-mset xs)の極大 m→各 deficit a は ∃x. a<o x、x≤m を trans(x<o m)/mnlcong(¬x<o m∧¬m<o x)で a<o m。
    **olt_asym を使わず carrier 仮説で書いた**ので olt_trans の前に置けて循環なし。
- **重要判明**: `olt_asym` は **独立でない**（Su/Su 節で `olt_ole_trans`→`olt_trans` を使用）。∴ asym を olt_trans の前に
  単独で置けない。→ **trans + asym + mnlcong を combined size 帰納で同時証明**が必要（3-way 相互依存、確定）。
- **残り = combined 帰納のみ**（全 helper 準備済）:
  `lemma olt_meta: "∀x y z. size x+size y+size z ≤ n ⟹ (x<o y⟶y<o z⟶x<o z) ∧ ¬(x<o y∧y<o x) ∧
    (x<o y⟶¬(y<o z)⟶¬(z<o y)⟶x<o z)"` を n 上の帰納で。asym は z 無視。
  - trans の Su/Su/Su: ab,bc→olt_Su_imp_multp\<^sub>H\<^sub>O→multp_HO 2本→`transp_on_multp\<^sub>H\<^sub>O`(carrier=summands, asymp_on/transp_on は IH)
    で multp_HO(mas)(mzs)→`multp\<^sub>H\<^sub>O_imp_olt_Su`(asym/trans/mnlcong は summands で IH 供給)→ olt(Su as)(Su zs)。
  - trans の他ケース(Om/Th/Su[a principal]): 既存 olt_trans 証明を流用（IH 名を combined に合わせる）。
  - asym: 既存 olt_asym 証明を流用、olt_ole_trans 使用箇所を combined IH(trans)に置換。
  - mnlcong: ≃-congruence。Su-level は mset 経由自動、Th/Om hereditary を IH で。新規証明（~中規模）。
  - 導出: `olt_trans`/`olt_asym`/`olt_mnlcong` を olt_meta から系として。olt_irrefl は asym から（既存）。
- **次セッション着手**: olt_meta を組む。既存 olt_trans(400行)+olt_asym(140行)を combined に統合し mnlcong を追加。
  measure は size の和、asym/mnlcong/trans を1帰納で。helper(橋渡し)は全て緑で利用可。

### 進捗 (2026-06-09 続19): 重大発見＝olt の Su 節(多重集合・単一支配元)の線形性は一次資料なし
- **Buchholz 1986 [Buc1] §2 精読**: 項 `(a_0,…,a_k)` は **ソート済み降順**(a_k≼…≼a_0, OT2)、< は **ソート lex**。
  Lemma 2.2/2.3 は o(a)(順序数写像)の順序保存で linearity。**pss-proof と同じソート lex**。
- **Towsner は Def 2.3 で順序定義のみ・linearity 未証明**。∴ **本 repo の `olt` Su 節(多重集合・単一支配元)は
  Buchholz/Towsner どちらとも異なる非標準形で linearity の一次資料が無い**(Python では真と確認済, 証明は自前)。
- **measure 難所(確定)**: combined trans+asym で asym-Th/Th(XA∧YA)が `g<o Th n d ≤o g' ⟹ g<o g'` の trans を要し、
  instance (g,Th n d,g') の中央 y=Th n d が full size＝asym(x,y) の size を減少させない。naive size-sum 帰納が回らない。
  Buchholz/pss はソート lex ゆえ起きない問題。
- **olt_trans 必要範囲(再確認)**: buchholz.thy(L_ThF)は **olt_trans 不使用**(transitivity-free)。
  **olt_trans が要るのは embed.thy op_NF 和ケースのみ**(embed.thy:519)。
- **完成済(緑)**: forward 橋渡し3本＋reverse 橋渡し `multp_HO_imp_olt_Su`(最大元論法, carrier 仮説付)。
  olt_trans Su の multiset 核は完成。残るは carrier 仮説供給の combined trans+asym+mnlcong のみ。
- **戦略選択肢(要 advisor 判断)**: (a) 非標準 linearity を自前 combined 帰納(subtle measure, 一次資料なし, 高難度)。
  (b) op_NF 和ケースに必要な弱い trans 事実だけ示す(full linearity 回避, op_NF 限定で最小)。(c) Su 節をソート lex 寄せ(部分)。

### 進捗 (2026-06-09 続20): advisor 最終指針＝再順序化(L_ThF 核先行)＋olt_trans 最小化。以降は自律
- **advisor 最終回答（以降 advisor 不在・完全自律）**:
  - **Q1**: op_NF 和ケースは full olt_trans 不要。**像 summand(embed の Th-principal)上の制限版 trans** で足りる。
    olt_trans の唯一の利用者は op_NF なので、op_NF 着手時に実際に呼ぶ trans instance を1つ抜き、像に限った
    制限版(collapse_lt_dom 系/像の構造帰納)で出す。full linearity 不要＝(b)。
  - **Q2**: **L_ThF 核を先行（再順序化）**。L_ThF 核は深い(impredicative 崩壊)が transitivity-free・出典明確
    (Towsner 3.10/Pohlers 9.6.15)＝「難しいが地図のある」仕事、依存なし、最深 headline sorry を消す。
    olt_trans-full は非標準・一次資料なし・measure subtle・op_NF 専用＝不確実。リスク収益比で L_ThF 先行が明確に良い。
  - **full linearity が将来必要なら**: 自前 subtle measure 帰納は書かない。**carrier 上で olt_Su=multp の橋渡しを完成
    （forward は済、reverse=multp_HO_imp_olt_Su も済）→ asym/trans/total を HOL-Library multp から継承**。
    library が measure を多重集合順序機構で内部処理＝full-size 中央項問題が起きない。相互再帰は外側項サイズ帰納で底打ち、
    summand 性質(IH)を multp 補題に供給。既存橋渡し資産がそのまま活きる。
- **確定作業順（自律）**: (1) **L_ThF 核 e∈acc**(Towsner 3.10) → (2) op_NF(最小 trans 含む) → (3) olt_trans は op_NF が要る分だけ。
- **L_ThF 核の正しい帰納(Towsner 3.10, 要再構成)**: 現 L_ThF は「外側 level 帰納＋内側 d-acc 帰納」だが、advisor 指針は
  「**引数 d∈acc の main 帰納 ＋ predecessor r の内側構造帰納**」。predecessor r=Th p e の臨界部分項 Kn p e は
  **r より小さい predecessor**(γ<o Th n d=Acond, size γ<size r)→ **r の構造帰納 IH で γ∈acc**→ e は controlled(Kn p e⊆acc)
  →「controlled⟹accessible」(Pohlers 9.6.15 核, Mn/AccB)で e∈acc→Th p e∈acc。q≥n は controlled で吸収(level 帰納不要)。
  ＝現状の「外側 level 帰納」より「predecessor 構造帰納＋controlled」が正しい枠。要 L_ThF 再構成。
- **次の一手**: L_ThF を「accI 内で predecessor r に構造帰納、Kn p e⊆acc を IH で、controlled⟹acc 補題で e∈acc」に再構成。
  controlled⟹acc が核(Mn/AccB 利用 or 直接の項長帰納)。これが残る最深 sorry。

### 進捗 (2026-06-09 続21): 核の深層分析確定＝Towsner 完全構成が必要(単純帰納は本質的に不可)
- **致命的発見1: 単一レベル controlled⟹acc は q≥n で破綻**。`Φ(n)≡ Kn n a⊆acc ⟹ a∈acc` を構造帰納で示そうとすると、
  a=Th q h で q>n のとき Kn n(Th q h)=Kn n h⊆acc から h∈acc は出るが、**Th q h∈acc には L_ThF(q,h) が必要**(q 無限大可)。
  実例: `Th 0 (Th 5 (Su[])) <o Th 1 d` が成立(Kn 0(Th 5 Z)=Kn 0 Z={} で B-lt 枝, 0<1)。∴ predecessor の引数 e は
  レベル q≥n の Th を含み得る。**レベル帰納(k 有界)も項長帰納も単独では不足**。memo 続20 の「controlled で吸収」は誤り。
- **致命的発見2: masterF↔L_ThF は相互に絡む**。masterF(Th 節)は L_ThF を呼び、L_ThF 核(e∈acc)は本質的に masterF(e) 相当。
  この絡みは Towsner の **超限 distinguished-set 構成 ＋ level-drop 補題 3.11** でのみ解ける。eq 副ケース(e''<o g)は
  引数 g の acc を要するが controlled だけでは出ない＝引数の acc は GIVEN な d∈acc に anchor するしかなく、cross-level の
  e は d と順序関係を持たない(collapse なので e は d より大きく得る)→ Towsner は shift で同レベル化して main IH。
- **致命的発見3: shift は nneg を壊す**。Th p e=shift(p-n)(Th n(shift(n-p)e)) だが p-n<0 の shift は subscript を負に
  し得て nneg(=soundness 必須, Th(-k)Z 降下)を破る。∴ oltRwF 上で Towsner の shift 自己同型(acc_shift は oltRw 用で
  oltRwF 不可)を直接使えない。**omfree も単独では非整礎**(Th 0 Z>o Th(-1)Z>o…, omfree な負添字降下を確認)。nneg 必須。
- **重要発見4: 既存 Mn/AccB は Towsner Def 3.7 の Acc_n そのもの**(誤解訂正): `nat(-gnd a)≤n`=G(α)≥-n, `Klt`=K_{<0}α,
  `norm`=β*, `normd`=FC=0 or omfree, `AccB(Suc n)=AccB n∪Awf(Mn n(AccB n))`, `Acc n`=M_n の wf 部=Acc_n。完全一致。
  ∴ ladder 3.8-3.12 を既存 Mn/AccB(full order <o + Om + shift)上で証明するのが faithful path。
- **Towsner ladder (一次資料 /tmp/towsner.txt 492-665 に全文)**:
  - 3.8 sum 閉包: m≤n,α∈Acc_m,β∈Acc_n ⟹ α^{≥0}_{-(n-m)}#β∈Acc_n。(main:m→α→β の三重帰納)
  - 3.9 ω^ 閉包: α∈Acc_n⟹ω^α∈Acc_n。(我々の系は ω^ を Su/Th に畳み込み済→不要かも)
  - 3.10 同レベル ϑ 閉包: α∈Acc_n⟹ϑ(α^{≤0}_{-1})∈Acc_n。**n=-∞(=omfree)で α˘=α**。main 帰納 on α + 構造帰納 on γ<ϑα。
  - 3.11 level-drop: α∈Acc_n,n>-∞ ⟹ (ϑα)*∈⋃_{m<n}Acc_m。**cross-level の核心**。
  - 3.12 master: ∀α,∀n≥G(α*). α*∈Acc_n。項の構造帰納＋上記補題。
- **残る最大リスク=接続(7)**: Mn/AccB は full order <o(Om 込)上の Awf。最終目標 wf oltRwF(omfree+nneg)への接続が非自明。
  Awf(M_n)-acc → acc oltRwF: oltRwF-predecessor b<o a が M_n に入る保証なし(Su は isH 無, Klt 条件未保証)。
  この接続補題が 2-6 と同等に難しい可能性。**接続が健全に書けるか未確認＝着手前に要検証**。
- **決定(自律)**: Option II=faithful Towsner ladder を既存 Mn/AccB 上で。ただし**着手順を「接続(7)の健全性検証」から**:
  接続が書けなければ Option III(omfree-native 再設計)へ。まず wflevel/proofs が要求する正確な wf ターゲットを確認し、
  接続の形を最小化できないか探る。olt_trans/shift_olt/acc_shift(oltRw)/Kn/FCset/gnd/norm は既存資産。
- **次の一手**: (A) wflevel.thy の reduction 連鎖と proofs.thy の Rnf/NF 定義を読み、wf の正確な必要形を確定。
  (B) 接続補題 Awf(Mn..)→acc oltRwF の健全性を紙で検証。(C) 健全なら 3.8 から着手、不健全なら native 再設計。

### 進捗 (2026-06-09 続22): 障害の数学的確定＝predecessor 非有界→超限 distinguished-set 必須。三 sorry とも大型
- **決定的障害(証明済)**: `Th n d` の oltRwF-predecessor は **size もレベルも非有界**。
  実例: `Th 0 (Th 5 Z) <o Th 1 d`(Kn 0(Th 5 Z)=∅で B-lt枝, 0<1)。d を小さく取れば predecessor のサイズ>Th n d。
  ∴ **構造帰納・size帰納・level帰納のいずれも predecessor を有界化できない**。残る道具は acc-rank(超限)のみ。
  Towsner も「Acc_n 全体の構成は Π¹₁-CA₀ 不可」と明記＝本質的 impredicative。Isabelle の inductive `acc` が超限エンジン。
- **masterF↔L_ThF↔Coll の相互entanglement(確定)**: 
  - `Coll(n): Kn n e⊆acc ⟹ Th n e∈acc` の eq副ケース(同レベル, e''<o e)は引数 e の <o 帰納を要し、e∈acc が要る。
  - `Acc_at(n): Kn n e⊆acc ⟹ e∈acc` は **偽**(e=Th q h, q>n は Kn q h 制御が無く非acc可)。
  - level 帰納(IH<n)も上方の Coll(q>n) を要し破綻。size 帰納も非有界で破綻。
  - ∴ acc を使った distinguished-set(Towsner Acc_n=既存 Mn/AccB)＋ladder 3.8-3.12 が唯一の筋。
- **我々の順序 ≠ Towsner 順序(逐語転写不可)**: Towsner ϑα<ϑβ は subscript 無し(レベルは引数内 Ω)。我々 `Th m a<o Th n b` は
  明示 `m<n∨(m=n∧a<o b)`＋Kn 条件。∴ Towsner の補題証明(shift/Ω 操作)は**そのまま転写できず、戦略のみ流用の独自実行**。
- **接続(7)の難所(確定)**: Towsner ladder は full order <o(Om込)上の Awf(M_n)。masterF(oltRwF)へは
  `x∈Acc_m ⟹ x∈acc oltRwF` が要るが、M_n は <o-predecessor で閉じない(Kn 0 制御が predecessor の Kn 0 に伝播しない;
  Kn 0⊄Kn p'')。接続自体が構成と絡む大仕事。
- **olt_trans も大型(再評価)**: 9ケース中 Om/Th 関連8ケースは size帰納で証明済。残 Su/Su(line 997)は単一支配元の
  多重集合推移律で **carrier 上 totality 必須**(max 支配元を取るため; 単一支配元は標準DM=多重支配元より強い)。
  totality は wfo 依存の可能性＋full-size 中央項問題(IH の size 三項和が 1要素3回使用で破綻)。
  ∴ 自前 combined linearity(trans+total+asym 同時size帰納, Buchholz Lemma 2.1 型)が要る＝大型。
  advisor 指針通り **full olt_trans は回避し op_NF 用の像制限 trans のみ**が賢明。
- **op_NF(embed.thy:480)**: 像(embed の Th-principal)上の最小 trans で足りる(advisor)。最も self-contained の可能性。未精査。
- **三 sorry 難易度(確定)**: L_ThF(研究級, 超限構成+接続) ≫ olt_trans(combined linearity, 大型だが標準) > op_NF(像制限,具体)。
- **作業方針(自律, 続22)**: 紙の分析は十分。**Isabelle で経験的に反復**。Towsner ladder を scratch で漸進ビルド
  (各補題 compile)。まず最も具体的な閉包(sum/bag は acc_of_bag_elemsF で既済)→3.10 同レベル ϑ 閉包の我々順序版を試作。
  接続が破綻したら native(Th-subscript stratify)へ転換。各 green ステップで commit。

### 進捗 (2026-06-09 続23): mnlcong 経験検証→olt_trans は wfo 制限で multp_HO bridge 可。順序=「置換合同を法に線形」
- **python 検証 (tools/olt_check.py 拡張)**:
  - **mnlcong は非 wfo で偽**(74036 CE; CE は `Su` 内 `Su` 等の非 wfo 項)。**wfo 項で真**(25950 instances, CE=0)。
  - **principals は全順序でない**(CE 42): `Th 0(Su[Om0,Om1])` と `Th 0(Su[Om1,Om0])` は非比較(引数が置換)。
  - **wfo 順序は permutation-congruence ~ を法として線形**(total-mod-perm CE=42=上記の Th)。
    ~ の定義: Su 置換 ＋ `Th p c ~ Th p c'` if `c~c'`(再帰)。非比較⟺ ~ 等価。∴ mnlcong は「~ が <o を保つ congruence」から従う。
  - olt_trans 自体は**無条件に真**(CE=0, 非 wfo 含む)。但し bridge 証明(mnlcong 経由)は wfo のみ。
- **使用箇所解析(重要)**: `ot` の olt_trans/olt_ole_trans/olt_asym/olt_irrefl の**下流(buchholz/wflevel/embed)使用は無し**
  (wf.thy の olt_ole_trans/olt_irrefl は `three` 順序=mechanized で別物・証明済)。wo 内部(ole_trans→asym→irrefl)＋
  将来 op_NF(像=wfo)のみ。bag_mono/wf_olt_of_principal は wfo 仮定下。**∴ olt_trans を wfo 制限版に置換可**(下流は全 wfo)。
- **olt_trans 確定方針**: `olt_trans_wf: wfo a⟹wfo b⟹wfo c⟹a<o b⟹b<o c⟹a<o c` を
  **combined size 帰納(trans_wf ∧ asym_wf ∧ mnlcong_wf 同時)**で。Su/Su は multp_HO bridge
  (`olt_Su_imp_multp\<^sub>H\<^sub>O`✅ forward, `multp\<^sub>H\<^sub>O_imp_olt_Su`✅ reverse)＋carrier 仮説を IH 供給。
  carrier transp_on: distinct 三項は size 和<total で IH 適用、x=z は asym で vacuous。mnlcong_wf は ~-congruence。
  既存 8/9 ケース(Om/Th)は wfo 付きで流用(Kn 元/summand の wfo は wfo_Kn/wfo Su で従う)。scratch_trans.thy に bridge 配線雛形。
- **olt_asym も wfo 化**: 現 olt_asym(無条件)は Th/Th XA-YA で olt_ole_trans 使用。wfo 版なら Kn 元 wfo で OK。olt_irrefl も wfo。
- **規模**: ~150-250 行の combined induction(Buchholz [Buc1] Lemma 2.1 型, 但し本系の単一支配元 Su 節は非標準で自前)。
- **三 sorry 確定方針**: (1) olt_trans_wf(combined linearity, 上記, 最も mapped) → (2) op_NF(wfo-trans+NF K条件) → (3) L_ThF(超限構成, 最難)。
  ＝advisor の「olt_trans 回避」を**部分修正**: full(無条件)は回避だが**wfo 制限 olt_trans は必要かつ実現可能**(op_NF が要る最小 trans＝これ)。

### 進捗 (2026-06-09 続24): bridge green 検証済。combined linearity 実装計画確定
- **bridge 検証 green (RC=0)**: scratch_trans.thy `su_su_trans_via_bridge`(carrier asym+trans+mnlcong 仮定下で Su/Su 推移)
  ＋`transp_on_multp\<^sub>H\<^sub>O'`(library `transp_on_multp\<^sub>H\<^sub>O[OF asym trans] auto` で B_sub_A discharge)がコンパイル。
  ∴ olt_trans Su/Su の道筋＝carrier 仮説供給のみが残課題。
- **olt_trans 全 9 ケース精査完了**: 8ケース(c=Om 各/c=Th 各/c=Su[a-principal])は **trans-IH のみ・wfo 不要・asym/mnlcong 不要**。
  **Su/Su(line 997, a=Su∧c=Su)のみ** bridge 必要。
- **実装方針(確定)= combined linearity `olt_lin`** (wo.thy の olt_trans を置換, scratch で先行ビルド):
  ```
  lemma olt_lin: "(∀a b c. size a+size b+size c ≤ N ⟶ wfo a⟶wfo b⟶wfo c⟶ a<o b⟶b<o c⟶ a<o c)
                ∧ (∀a b.   size a+size b      ≤ N ⟶ wfo a⟶wfo b⟶ a<o b⟶ ¬ b<o a)
                ∧ (∀k x m. size k+size x+size m ≤ N ⟶ wfo k⟶wfo x⟶wfo m⟶ k<o x⟶ ¬x<o m⟶ ¬m<o x⟶ k<o m)"
    proof (induction N rule: less_induct) case (less N)
  ```
  - less.IH から IHtrans/IHasym/IHmnl を抽出(size 和<N で各 conjunct)。sub-term は常に size<N なので IH 適用可。
  - **trans 節**: wo.thy 781-1248 の8ケースを移植＋各 IHtrans 呼出前に sub-term の wfo を `wfo_Kn`/`wfo Su summand`/`wfo Th arg` で供給。
    Su/Su は bridge(`olt_Su_imp_multp\<^sub>H\<^sub>O`,`transp_on_multp\<^sub>H\<^sub>O'`,`multp\<^sub>H\<^sub>O_imp_olt_Su`)＋carrier asym/trans/mnlcong を IH から。
    carrier transp_on: distinct 三項 size 和<N で IHtrans、x=z は IHasym で vacuous(transp_on_multp\<^sub>H\<^sub>O が内部処理する形に合わせる)。
  - **asym 節**: wo.thy 1266-1402 olt_asym 移植＋wfo。Th/Th XA-YA で IHtrans(Om/Th sub, 済ケース型)、Su/Su は IHasym(smaller)。
  - **mnlcong 節(新規)**: k<o x, x~m(非比較) ⟹ k<o m。x,m の形で場合分け。~ は置換合同。IHtrans/IHasym/IHmnl 使用。最も不確実。
  - 帰結: `olt_trans_wf`/`olt_asym_wf`/`olt_irrefl_wf`/`olt_ole_trans_wf`/`ole_olt_trans_wf` を olt_lin から。
- **wo.thy 置換時の注意**: 現 olt_trans(無条件,sorry)/olt_ole_trans/ole_olt_trans/olt_asym/olt_irrefl を wfo 版に。
  下流(buchholz/embed)は ot の trans/asym/irrefl 不使用＝安全。wo 内 bag_mono/wf_olt_of_principal(代替WF経路, 要確認)は wfo 仮定下。
- **規模**: ~400-500 行(trans 移植が大半)。mnlcong が新規で要注意。**手順: scratch で trans→asym→mnlcong を順に green 化→wo.thy 統合**。

### 進捗 (2026-06-09 続25): monolithic combined induction 破綻→midH 分解に修正（重要）
- **scratch で combined induction を試作**: trans 節の8ケース(Om/Th, c=Su[a-principal])は **wfo 付きで green 完全証明**、
  Su/Su(b=Su)は bridge 配線が combined 帰納内で動作(green, carrier 境界は sorry)。構造は妥当。
- **しかし monolithic(trans+asym+mnlcong を単一 size 帰納)は破綻**: asym の Th/Th XA-YA ケースで
  trans を **中央項 Th n d=full size** で呼ぶ(`olt_ole_trans(g,Th n d,g')`)→ measure(size g+size(Th n d)+size g')が
  現 asym measure(size x+size y=2 size(Th n d))より**大きく**、IHtrans 不適用。＝**「full-size 中央項問題」**(memo 既述)。
  ∴ trans/asym を単一 measure で相互 IH すると asym が閉じない。
- **正しい分解(確定)= midH 経由で循環を断つ**:
  1. **`olt_trans_midH: isH b ⟹ a<\<^sub>o b ⟹ b<\<^sub>o c ⟹ a<\<^sub>o c`**（中央 b が principal の推移律, 自己完結 size 帰納, asym/wfo 不要）。
     再帰は常に中央=b(principal)を保つ。a=Su∧c=Su∧b-principal も込み(現 olt_trans が sorry にしている部分)。
  2. **`olt_asym`(無条件)** を midH 経由で（Th/Th の trans 呼出は中央=Th n d=principal なので midH で足りる; full olt_trans 不要）。
     ＝現 olt_asym の `olt_ole_trans` を midH ベースに差し替え。
  3. **`mnlcong`(wfo 制限, python で wfo 真)** を midH+asym で。trans 呼出が principal 中央か要確認、不足なら asym 併用。
  4. **完全 `olt_trans`**: 現8ケース＋Su/Su を「b principal→midH、b=Su→bridge(global asym+mnlcong＋IHtrans on carrier)」で。
     b=Su の carrier transp_on は IHtrans(size 帰納, distinct 三項 size 和<現 measure)＋`carrier_sum_lt`。asymp_on は global asym(対角=irrefl 込)。
- **ヘルパー(carrier_sum_lt, sum_set_size_lt_Su)**: 要修正(`sum_set_size_lt_Su` の auto 失敗→手動 cases a∈set xs; `sum_Un_le`→`sum.union_inter` 経由)。
  size(Su xs)=Suc(size_list size xs), size_list size(a#xs)=Suc(size a+size_list size xs)。transp_on(b=Su bridge)用に必要。
- **wfo 範囲**: midH/asym は無条件可。mnlcong は wfo 必須(非wfo偽)。∴ 完全 olt_trans の Su/Su(bridge)が wfo 依存→ olt_trans 全体 wfo 制限。
  下流(buchholz/embed/op_NF)は全 wfo で安全。
- **次の一手**: scratch で midH を書く(現8ケース移植, 中央 principal に特化で簡略)→asym→mnlcong→olt_trans 統合→wo.thy へ。
  wfo_Kn/nneg_Kn を wo.thy へ移動(olt_lin が wo に入るため; 現状 wflevel)。

### 進捗 (2026-06-09 続26): size 境界ヘルパー green 完成。midH 分解の3すくみ entanglement 判明
- **scratch_trans.thy が green(sorry 0)**: 再利用可能な検証済みピース:
  - `su_su_trans_via_bridge`(carrier asym+trans+mnlcong 仮定下で Su/Su 推移)＋`transp_on_multp\<^sub>H\<^sub>O'`。
  - **size 境界群**: `sum_set_size_lt_Su`(∑set xs<size(Su xs))・`sum_Un_le_ot`・`carrier_sum_lt`・`size2_distinct`・`size3_distinct`
    (distinct 2/3 項 ⊆ carrier の size 和<三 Su サイズ和)。bridge の carrier transp_on の IHtrans 境界に必要。
- **midH 分解の難所(重要・確定)**: olt_trans_midH(中央 principal)を自己完結に証明したいが、その a=Su∧c=Su 節が
  **irrefl(z) を要する**(∀v∈as.v<o b≤o z で z∈as だと z<o z 派生→矛盾に irrefl 必須; witness を zs-as に取るため)。
  そして irrefl(Th m c) は 2-cycle(Th m c,γ)を asym で潰す必要、asym(Th/Th)は trans を**中央 Th n d=full size**で呼ぶ
  →midH 必要。∴ **irrefl ↔ asym ↔ midH の3すくみ**で、full-size 中央項のため単純な size 同時帰納では閉じない。
  ＝Buchholz [Buc1] Lemma 2.1 の linearity 同時帰納そのものの難しさ。olt_trans の8ケースは size-IH のみで OK だが、
  Su/Su を閉じるには linearity(irrefl+asym+trans+mnlcong)の正しい同時帰納設計が要る(measure 工夫: 多重集合 or lexicographic)。
- **次の一手の候補**: (a) Buchholz Lemma 2.1 型の linearity 同時帰納を measure 慎重設計で(全 4 性質)。
  full-size 中央項は「中央項を測度で優先する lexicographic 測度」or「multiset {a,b,c} 測度」で吸収できる可能性。要検討。
  (b) もし olt_trans が op_NF のためだけなら、op_NF が実際に呼ぶ trans instance(像=wfo の特定形)に限定した最小版を直接証明。
- **現状コミット**: baseline 3 sorry 緑維持。scratch は ROOT 外(参照用 green ファイル)。

### 進捗 (2026-06-09 続27): olt_trans_aH(左principal限定)も不可。olt_trans は本質的に linearity 同時帰納が必要
- **aH ショートカット検討→不可**: ot の trans 使用は asym 内(左 g,g'∈Kn=principal)のみ・op_NF も左 γ principal。
  そこで `olt_trans_aH: isH a⟹trans` を既存証明から(a=Su 消去で)出せると思ったが、**Th/Th ケースが引数 (e,f,d) の trans を要し、
  引数 e,d は Su になり得る**(line 1186-1188 IH(e,f,d))。∴ 左 principal 制限では内部再帰が破綻。
  同様に `olt_trans_HH`(両端 principal)も Th/Th 引数再帰で破綻。**引数 trans は size-IH(小 Su/Su 含む)で扱う＝Su/Su を閉じる必要**。
- **確定**: olt_trans Su/Su を閉じるには **linearity(trans+asym+mnlcong)の同時 size 帰納**が必須で、asym の Th/Th が trans を
  **中央 Th n d=full size** で呼ぶ「full-size 中央項問題」を測度設計で吸収する必要。**姉妹 repo pss-proof は簡単版 linearity すら
  sorry**(p_7_1_lessBT_linord、[Buc1] Lemma 2.1 を外部引用扱い)＝標準でも難物。本系は非標準(多重集合単一支配元)で一次資料無し。
- **三 sorry の真の規模(確定)**: (1) olt_trans=非標準 linearity 同時帰納(研究級, full-size 中央項) (2) L_ThF=超限 distinguished-set
  (研究級) (3) op_NF=(1)依存＋NF K条件。**全て研究級の順序論/証明論コア**。memo/adviser の当初想定より大きい。
- **戦略的選択肢(要判断)**: (A) 全て自前完全証明(数週間規模)。(B) 姉妹 repo 同様、標準メタ理論(linearity 等)を一次資料引用(sorry/axiom)
  扱いにし、新規部分(translate/decrease/embed/崩壊核)に原証明を集中。但し本系の順序は非標準で引用が弱い。
  (C) 順序を標準形(Buchholz [Buc1] の lex/辞書式)に作り替えて linearity を引用可能にする(大改修)。
- **検証済み資産(再掲)**: baseline 3 sorry 緑。scratch_trans.thy(green): bridge 配線＋size 境界群。trans 8ケースは wfo 付き緑(別 scratch, commit 62c3dcb)。

### 進捗 (2026-06-09 続28): 【重大訂正】mnlcong は wfo でも偽。multp_HO bridge ルート無効
- **深さ3 wfo テスト(完走)**: mnlcong wfo: 80,294,809 instances 中 **CE 1,311,260**＝**mnlcong は wfo でも偽**。
  続23 の深さ2 テスト(CE=0)は浅すぎた誤り。CE 例:
  u=`Th 0(Su[Om0,Om1])`, v=`Th 0(Th 0(Su[Om0,Om1]))`, m=`Th 0(Su[Om1,Om0])`。
  u<o v(v の Kn 0={u} で u∈Kn→u<o v)、v~m(非比較)、だが u,m は引数が置換(Su[Om0,Om1]~Su[Om1,Om0])で非比較→¬u<o m。
- **帰結(重大)**: 逆橋 `multp\<^sub>H\<^sub>O_imp_olt_Su`(mnlcong 必須)は wfo でも使えない＝**olt_trans Su/Su の bridge ルートは死んだ**。
  scratch_trans.thy の bridge 配線・size 境界は「mnlcong を供給できない」ので olt_trans には使えない(資産だが本筋外)。
  ＝続23-27 の「wfo 制限 bridge」方針は誤り。
- **訂正された状況**: trans 自体は無条件に真(python CE=0)だが、**単一支配元 DM 推移律を multp 経由で出す道は無い**(mnlcong 偽)。
  順序は「置換合同を法に線形」でもない(u が v の下だが置換 m の下でない＝下方集合が置換で不変でない)。続23 の特徴づけも誤り。
- **olt_trans Su/Su の正しい証明は未知**: 直接証明(中央 b で場合分け、size-IH のみ)を要するが、単一支配元の witness 構成に
  comparability が要り、それが無い(非線形)ため標準手法が効かない。**要再設計**。これも研究級で、当初想定より難しい。
- **戦略判断の重要性が増大**: bridge 死亡で olt_trans (A 完全証明)の道筋が不透明化。(B)引用 or (C)標準順序作り替え の比重が上がる。

### 進捗 (2026-06-09 続29): 方針A確定。olt_trans 直接証明の構造解析＝full-size 中央項サイクルが核心難所
- **ユーザー確定: 方針A（完全自前証明, sorry ゼロ）**。本系はオリジナル $p_a(b)$＝非標準なので引用不成立。
- **witness 経験則(python, 15678ケース)**: `Su a<o Su b<o Su c` の `Su a<o Su c` の witness w∈#(c-a) は
  **常に w1 か w2（=a<b の支配元 / b<c の支配元）のどちらか**。「どちらも不可」=0。w2 が効くことが多く(13634)、駄目なら w1(2044)。
  ∴ 直接証明は「w2 を試し、駄目なら w1」。各 u∈#(a-c) は u∈#(a-b)→u<o w1, さもなくば u∈#(b-c)→u<o w2（クリーン, trans不要）。
- **しかし witness 選択の正当化に asym/irrefl 必須**: w1∈#(b-c) なら w1<o w2(trans-IH)で w2 が全 u を支配。だが
  count_A(w2)>count_B(w2) の枝で w2<o w1<o w2 の2-サイクル→ asym/irrefl が要る。∴ 直接証明も asym 依存。
- **asym の full-size 中央項サイクル(核心難所, 確定)**: asym(Th m c, Th n d) の XA-YA で
  サイクル `Th m c ≤o g <o Th n d ≤o g' <o Th m c`(g∈Kn n d, g'∈Kn m c)。最終矛盾は asym-IH(g,g')(小, size g+size g'<size x+size y ✓)
  だが、g<o g' / g'<o g を作る中間 trans が **中央 Th n d / Th m c = full size**→ measure が asym の size x+size y を超え得る(size g<size y だが size x 未満とは限らない)。
  どの collapse も full-size 端点(x,y)＋追加元を含み、size 和でも multiset 測度でも tie/超過。重み付け(asym を2×)は trans→asym 方向で逆に破綻。
  ＝**標準 linearity 帰納(size/multiset 測度)では閉じない**。Kn-domination 節が生む固有の難所(Buchholz lex 順序には無い)。
- **次の一手候補(A 継続)**: (i) rank ベース測度(整礎性で定義する rank)or (ii) より強い命題を束ねる(connectedness 込)or
  (iii) asym を「中央 principal の trans=midH」complete 先行で(但し midH 自身が Th 引数で Su/Su trans を要し循環)。
  要・測度の本質的工夫 or 文献(Buchholz [Buc1] 2.1 の正確な帰納測度)精読。

### 進捗 (2026-06-09 続30): 【方針確定 A2】ot 順序を Buchholz 標準形へ再定義（ユーザー確定）
- **ユーザー確定: (A2)** — `p_a(b)` 記法(datatype)は保持、`ot` の **olt/wfo を Buchholz 標準形に再定義**。
  ＝支配(K)条件を**順序の比較から外し wfo 条件へ**移す。Su を**辞書式(非増加リスト)** に。Th を**純辞書式 lex** に。
- **根拠(Buchholz [Buc1] 精読)**: 彼の order は (<2) `Dᵤa<Dᵥb⟺u<v∨(u=v∧a<b)`(純 lex)・(<3) タプル辞書式。
  **K 支配は OT3 `Gₒb<b`(=wfo) に在る**。∴ **Lemma 2.1 linearity は "Straightforward"**。姉妹 pss-proof の `lessBT/lessBP` も同形。
  我々の現 olt は K 支配を比較内に入れた非標準設計＝自滅(full-size 中央項/mnlcong偽/単一支配元非推移)。
- **再設計の核心難所 = Om(明示カーディナル)の扱い**: Buchholz は Ω を項に持たない(暗黙)。我々は WF 足場(Towsner Acc_n)で
  Om を明示項にしている。Om vs Th の比較は意味論的(Ω_n vs ψ_m(a))で純 lex に乗らない＝現 olt が Kn ベースにした理由。
  WF target は omfree(Om 無し)＝embed 像も omfree。∴ **omfree fragment(Th+Su)上で新 order を lex/辞書式に**するのが主戦場。
- **新 order 設計(omfree, Buchholz/lessBT 準拠)**:
  - principals = Th n a。tuple = Su xs(非増加, isH 要素)。principal p は length-1 tuple [p] 扱い。
  - `Th m a < Th n b ⟺ m<n ∨ (m=n ∧ a<b)`(純 lex)。
  - `Su xs < Su ys` = 辞書式(<3): (i) proper prefix 小 (ii) 最初の差で ak<bk。
  - principal vs Su は [p] vs ys の辞書式。
  - **支配 Gₒb<b は wfo へ**: `wfo(Th n b) = wfo b ∧ (Th n b の臨界部分項 < b 相当)`。詳細は Buchholz OT3 を omfree に写す。
  - Om: WF 足場。omfree 順序には不要かも。新 WF 証明が Om 足場を要するか要再検討(Buchholz の C(α) は別足場)。
- **影響範囲(中規模リファクタ)**: wo.thy(olt/wfo/Kn/全 order 補題)・wflevel・buchholz(masterF/L_ThF=WF)・embed(op_NF/順序保存)・proofs。
  three の order(mechanized)は既に純 lex で linear 証明済＝ot も同様にできる手本。
- **手順**: (1) scratch で新 order(omfree Th+Su)＋linearity(straightforward 確認)→ (2) wfo(支配条件)再定義 → (3) WF(新 order で)
  → (4) embed 順序保存 → (5) Om/足場の要否決定。まず (1) で「linearity が本当に容易」を実証。

### 進捗 (2026-06-09 続31): 【A2 検証成功】Buchholz lex order の linearity 完全 green
- **scratch_order.thy が green(RC=0, 16s)**: 新鮮 datatype `bt=Trm "bp list" and bp=Thb int bt`(omfree fragment)に
  Buchholz 辞書式/lex order `lessT/lessP`(支配節なし)を定義し、**linearity を完全証明**:
  - `less_neq`(lessT a b⟹a≠b), `less_irrefl`(¬lessT a a), `less_total`(trichotomy=全順序!), `less_trans`(推移律)。
  - 全て `lessT_lessP.induct`(関数の相互帰納規則)＋簡単な cases で**数行**。total は plain `auto`。
  ＝**(A2) 決定的検証**: lex order で linearity は容易。現 Towsner-K-支配順序(olt)では研究級だったのと対照的。
- **新 order 定義(確定, omfree)**:
  ```
  lessT (Trm []) (Trm bs) = (bs≠[])
  lessT (Trm(a#as)) (Trm[]) = False
  lessT (Trm(a#as)) (Trm(b#bs)) = (lessP a b ∨ (a=b ∧ lessT (Trm as)(Trm bs)))
  lessP (Thb u a)(Thb v b) = (u<v ∨ (u=v ∧ lessT a b))
  ```
  irrefl は less_neq 経由。trans は induct 規則＋(cases c; cases 内側list)。
- **統合の核心未解決問題 = lex order の WF(L_ThF 相当)をどう証明するか**:
  - Towsner 3.10-3.12 の組合せ的 WF は **K-支配順序(Def 3.5)用**。Buchholz lex の WF は §2.2 順序数同型(ε_{Ω+1}, 形式化重い)。
  - 候補(a): lex order の WF を Towsner 流組合せ論で再導出(支配は wfo=Gob<b 条件として)。
  - 候補(b): lex order と K-支配 order が **normal 項(Gob<b)上で一致**を証明し、WF は K-支配(Towsner)で、linearity は lex で。
    ＝両方の良いとこ取り。但し「lex=Kdom on normal」の証明＋embed 像が normal の証明が要る。
  - 候補(c): WF も lex order で Towsner 流に直接(Acc_n を lex order で再定義)。
- **統合作業(大)**: ot を bt/bp 式に(Om の扱い決定要)→ olt=lessT 式 → wfo に支配条件 → WF 再構築 → embed 順序保存(lex→lex で容易化見込) → proofs。
- **重要教訓**: テストは必ず `timeout 240` で(bo2 が metis ループで1時間 OOM kill された。同マシン他エージェントへの配慮も)。

### 進捗 (2026-06-09 続32): ot 単一型の Su[p]=p 問題判明→統合は bt/bp 二型式が筋
- **scratch_order2(ot 上 lex order oltL+prins)を試作→linearity が反対称性で破綻**:
  ot は Om|Th|Su が**単一型**。principal p(=Om/Th) と `Su [p]`(length-1 tuple) は `prins` が同一([p])で
  **順序的に等しいが項として p≠Su[p]**。∴ total/irrefl が raw 等号で成立せず(`prins a=prins b∧a≠b` が起きる)。
  wfo(Su length≠1)に制限すれば prins 単射だが、証明に wfo を thread する必要＝煩雑。
- **対して scratch_order の bt/bp は clean**: `bt=Trm "bp list" and bp=Thb int bt`＝**principal(bp) と tuple(bt) を別型**に分離。
  単一 principal は `Trm[p]`(bt)で、"p as bt" は存在しない＝Su[p]=p 問題が**構造的に消滅**。だから linearity が数行で green だった。
- **結論**: (A2) 統合は **ot を bt/bp 式の二型 datatype に作り替える**のが正しい(Buchholz の T1-T3 そのもの: 0/principal/tuple)。
  現 ot(Om 込・単一型)に order を足すのは Su[p] 問題で筋が悪い。bt/bp なら linearity 自明・Om は別途(WF 足場用に principal 種を足す等)。
- **統合作業(大, 次フェーズ)**: (1) 新 datatype(bt/bp 式, 必要なら Om 相当の principal 種)→ (2) 順序=lessT/lessP(green 実証済)
  → (3) wfo に支配条件(Gob<b)→ (4) translate/embed を新 datatype へ(decrease は three のまま, embed: three→新)→ (5) WF(L_ThF)を新 order で
  → (6) op_NF(lex→lex)。three(p_a(b))は不変。L_ThF(WF 核)は順序 style 不問で impredicative=研究級のまま。
- **教訓再掲**: 単一型 ot の設計が諸難の根。bt/bp 二型が Buchholz 標準。テストは必ず timeout 240。

### 進捗 (2026-06-09 続33): 【最小 A2 発見】非増加リスト上で 多重集合順序=辞書式順序 → olt_trans_cnf 最小修正
- **python 検証(7056比較, 差異0)**: **非増加(cnf)リスト xs,ys 上で `Su xs <o Su ys`(現・多重集合単一支配元) = 辞書式順序(Buchholz <3)**。
  ∴ olt_trans の linearity 困難は Su 多重集合節だが、**cnf 項に限れば Su 節=辞書式で推移律が容易**(scratch_order で辞書式 trans 緑実証済)。
- **最小 A2 修正(順序も WF も変えない!)**:
  1. ot 上に `cnfo`(hereditary 非増加 Su ＋ wfo)述語を定義。
  2. bridge: 非増加 xs,ys で `Su xs <o Su ys ⟺ dictSu xs ys`。
  3. `olt_trans_cnfo: cnfo a⟹cnfo b⟹cnfo c⟹ a<o b⟹b<o c⟹a<o c` を size 帰納で(Su/Su は bridge＋辞書式 trans, Th/Om 既証明)。
  4. op_NF は embed 像(cnf)なので olt_trans_cnfo で足りる。embed 像が cnfo を証明。
  5. 一般 olt_trans(sorry)は op_NF が cnfo 版に切替後、他に ot trans/asym/irrefl 利用者なし(buchholz/wflevel は多重集合機構を直接, 確認済)なら**削除**。
- **利点**: WF(多重集合 bag_mono/wflevel/buchholz)は無変更。embed/ot 構造も大半保持。olt_trans sorry を最小手数で解消。
  Th-collapse の WF(L_ThF)は依然 impredicative=研究級(Su とは無関係)。
- **注意**: cnfo は ot 述語(three の cnf とは別, embed 像用)。embed 像の非増加性は collapse(非増加)から従う。
- **次**: scratch で cnfo+bridge+olt_trans_cnfo を実装・緑化(timeout 240)→ wo.thy 統合→ op_NF 着手。

### 進捗 (2026-06-09 続34): 【deadlock 回避の鍵】辞書式 trans は自己完結（asym 不要）→ olt_trans_cnf の正しいルート
- **deadlock 分析**: multp_HO bridge は carrier asym 必須。asym(Th/Th)は trans を full-size 中央項で呼ぶ→combined 帰納でも
  measure 超過(size g+g'>size x 可)。∴ bridge ルートは olt_trans↔olt_asym の deadlock。
- **鍵**: **辞書式(dictionary)trans は自己完結**(scratch_order の less_trans は asym 不要で証明済, 関数帰納のみ)。
  ∴ olt_trans Su/Su(cnf)を **bridge でなく辞書式ルート**で証明すれば asym 不要＝deadlock 回避。
- **正しい olt_trans_cnf 手順**:
  1. **bridge 補題**: 非増加 xs,ys で `Su xs <o Su ys ⟺ dictSu xs ys`(多重集合単一支配元=辞書式, python 検証済)。← 組合せ的山場
  2. dictSu trans(自己完結, scratch_order 型)。
  3. olt_trans Su/Su(cnf) = bridge＋dictSu trans。**asym 不要**。
  4. 8 ケース(Om/Th)は既証明(cnfo sub-term は heredity で IH 適用)。→ olt_trans_cnf 完成。
  5. その後 olt_asym(cnf)は完全 olt_trans_cnf を使い健全(full-size 中央項は complete trans なら OK)。
- **bridge 補題の証明方針**: 非増加リスト＋要素 comparable(cnf-total, これは Th/Th で γ<a の IH で full-size 中央項なし＝clean)。
  多重集合差の dominator = 辞書式 first-difference。要素 total と sortedness で帰納。~100-150 行見込み。
- **次**: scratch_cnf で (a) cnfo_total(clean size 帰納, Th/Th は γ<a の IH) → (b) bridge → (c) dictSu trans → (d) olt_trans_cnf。
  全て timeout 240 でテスト。完成後 wo.thy 統合・op_NF を olt_trans_cnf に。

### 進捗 (2026-06-09 続35): 【根本原因確定】K-dom が問題。WF と linearity で要求が逆。L_ThF は olt_trans 非依存→集中
- **deadlock の根本**: ot の olt は Th 節に K-dom(∃γ∈Kn n b.Th m a≤oγ)を持つ(Towsner Def 3.5 式)。
  irrefl(Th m c)/asym(Th/Th)は「γ<o Th m c かつ Th m c<oγ の2-cycle」を潰すのに **trans を中央 Th m c=full size で**呼ぶ
  →size-IH で measure 超過(full-size 中央項)→ 単純帰納で証明不能。bridge(辞書式)も x=y head 節で irrefl 必須→同 deadlock。
  ∴ **K-dom-in-order を消さない限り linearity(irrefl/asym/trans)は閉じない**。
- **重要な分離(確定)**:
  - **K-dom は WF(Towsner Acc_n)に適合**(Towsner の順序自体が K-dom)。∴ ot(K-dom)で L_ThF は Towsner 直接転写可能。
  - **K-dom は linearity/op_NF に有害**。op_NF は三系→ot の順序保存で ot trans 要。
  - **three(p_a(b))は既にクリーン辞書式順序＝linear 証明済**(mechanized)。ot は K-dom を three レベルにも付けた迂回(omfree に不要)。
- **(A2) の正しい意味**: omfree(=embed 像)上は K-dom 不要＝three のクリーン順序で十分。olt_trans/op_NF はそちらで。
  WF 足場のカーディナル比較のみ K-dom(内部)。＝et(カーディナル拡張, three 部クリーン)設計。但し大リファクタ。
- **重要: L_ThF(WF 核)は olt_trans に非依存**(buchholz/wflevel は ot trans/asym 不使用, 確認済)。bag_mono は多重集合機構直接。
  ∴ **olt_trans を解決せずとも L_ThF を進められる**。L_ThF は最深 sorry・最高価値・Towsner 転写可能(ot は K-dom で Towsner 整合)。
- **方針(継続作業)**: **L_ThF(Towsner Acc_n ラダー 3.8-3.12)に集中**。既存 Mn/AccB=Towsner Acc_n。olt_trans/op_NF(A2 et 化)は後回し。
  predecessors 非有界(続21-22)＝超限 distinguished-set 必須。Lemma 3.8(sum 閉包)→3.9→3.10→3.11→3.12 を ot 上で。
- **運用**: timeout 廃止(valid build を殺す/他agent影響)。**build は background＋Monitor アラーム**で監視、runaway は isbman で手動 kill。

### 進捗 (2026-06-09 続36): L_ThF の sorry を impredicative 核1点に縮小(green 多数)
- **pacc を size 強帰納に再構成(green)**: `Kn p e ⊆ acc`(控除性)を pIH(predecessor の size 帰納)で証明済。
  measure_induct_rule が premises を IH に thread することを確認。
- **ctrl_acc を構造帰納で部分証明(green)**: `Kn p e⊆acc ⟹ e∈acc` を e の構造帰納で:
  - e=Su: summand に IH＋bag 閉包。green。
  - e=Th r h, r≤p: `Kn p(Th r h)={Th r h}`⊆acc → 直接。green。
  - e=Th r h, p<r<n: `Kn p h⊆acc`→IH で h∈acc→**levelIH(r<k)** で Th r h∈acc。green。
  - e=Th r h, **r≥n**: ← **唯一の残 sorry**。
- **残差(正確)**: `r ≥ n, h∈acc, omfree/wfo/nneg h, p<r, Kn p h⊆acc ⟹ Th r h∈acc`。
  ＝**L_ThF(r,h) を r≥n(=現在証明中の level k 以上)で**。h は d と順序無関係(buried 部分項)・r 無界。
  ∴ per-term 帰納(level-k/acc-on-d/size)では measure 不在で不可能＝**global Towsner Mn/AccB 構成が必須**(続21-22 と整合)。
- **重要**: 残差は「L_ThF を全 level 同時に(global に)確立する」必要を示す。現 key 帰納(less_induct on k)は level<k に限定され不足。
  Towsner Acc_n(=既存 Mn/AccB)は超限的に全 level の accessible を一括構成＝この residual を吸収する唯一の枠。
- **次フェーズ(深い研究核, ~300行, 複数セッション)**: Mn/AccB の ladder(Towsner 3.8 sum/3.9 ω/3.10 同レベル ϑ/3.11 level-drop/3.12 master)。
  接続(AccB⊆acc oltRwF)は Towsner 3.10 の「ϑα の predecessor は全て acc」=現 pacc/ctrl_acc 構造で部分的に実現済。
  我々順序は K-dom＋明示レベルで Towsner 順序と差異あり＝戦略流用の独自実行。
- **状態**: baseline 緑, 3 sorry(L_ThF=残差1点に縮小・大半 green / olt_trans / op_NF)。scratch: order(green,lex linearity), trans(green,bridge+size), cnf(foundation), order2(廃).

### 進捗 (2026-06-09 続37): 残差の構成方針＝Th-subscript-stratified distinguished sets（Om-based Mn は omfree に degenerate）
- **残差再掲**: `h∈acc, Kn p h⊆acc, p<r ⟹ Th r h∈acc`(r≥n)。h は d と順序無関係(buried)・r 無界 → per-term 帰納不可。
  確認: r は e(predecessor の arg)の部分項の添字で、固定 e では r≤maxsub(e)<∞ だが e 横断で無界。h∈acc を「運ぶ」のは L_ThF(r,h) で循環。
- **既存 Mn/AccB は Om-based で omfree に degenerate**: `gnd`/`FCset`/`Klt`(=Kn 0∩below Om0)は omfree で FCset={}→gnd=0→自明。
  ∴ omfree 残差には **Th-subscript を軸とした新 distinguished sets** が要る(memo 続21 の「別軸」が正しい)。Om-based Mn は ψ-with-Ω 用。
- **構成方針(次フェーズ, ~300行, fresh context)**: Th-subscript レベル n で stratify した accessible-controlled 集合 `B n` を
  acc で定義(`B n = acc-part of {controlled-at-level-n principals}`)し、Towsner 3.8-3.12 を Th-subscript 版で:
  - level-drop: Th p e(p<r の collapse)は level p に「落ちる」→ B p で accessible。
  - 残差 Th r h: h∈acc かつ Kn p h⊆acc → h を B r に入れ(controlled at r? 要 Kn r h⊆acc, h∈acc から従う: Kn r h≤o h∈acc)
    → B r の collapse 閉包で Th r h∈acc。＝鍵は「h∈acc ⟹ Kn r h⊆acc(各 γ≤o h∈acc)」＋ B r 構成。
  - 実は h∈acc から Kn r h⊆acc は出る(Kn_le_self＋acc_downward)！∴ 残差は「Kn r h⊆acc ⟹ Th r h∈acc」=ctrl_acc at level r。
    だが ctrl_acc(level r)も同じ q≥r 残差を持つ＝循環。global B n の超限構成で一括解決するしかない。
- **今セッション成果(全コミット, baseline 緑 3 sorry)**: L_ThF 大半 green(Kn p e⊆acc 証明・ctrl_acc 構造帰納)・sorry を核1点に縮小;
  (A2) lex order linearity 緑検証(scratch_order); 根本原因=K-dom-in-order 特定; 多重集合=辞書式 on 非増加 検証。

### 進捗 (2026-06-09 続38): 【決定的】残差は §2 multi-ϑ_n 特有の cross-subscript ケース＝Towsner §3.2 に存在しないギャップ
- **残差を Towsner 3.10 の証明と精密照合した結論**: 我々の系は wo.thy の通り §2(ϑ_n, Ω_n を absolute int subscript で持つ複数崩壊関数系)。
  Towsner の distinguished-set WF 証明(§3.2 Lemma 3.8-3.12)は §3(単一 ϑ＋Ω の de Bruijn polymorphic)用。**§2 の WF 証明は論文に無い**(§2 は Key Lemma 2.5/2.7 の動機付けのみ)。
- **Towsner 3.10(崩壊閉包)の場合分けと我々の対応(精密)**:
  - Towsner Case 1 (β<α, predecessor の arg が小): = 我々の **p=r ∧ e<o d**(accIH で green)。
  - Towsner Case 2 (α<β, 支配): = 我々の **domination ∃γ∈Kn n d. Th p e≤oγ**(dom_acc で green)。
  - **我々の p<r cross-subscript ケースは Towsner 3.10 に対応物が無い**。単一 ϑ には subscript が無く、ϑ_p e<oϑ_r h が「p<r かつ Kn p e<oϑ_r h」で成立する経路自体が §3 に存在しない。
  ∴ **wo.thy の「§2 terms＋§3.2 proof」ハイブリッドは本質的に不完全**。p<r ケースは §3.2 が cover しない。multi-ψ_n 版(Buchholz 1991)の追加論証が要る。
- **downward-closure は FALSE(反例確定)**: M_n(critical-subterm 制御集合)は <o で下方閉でない。
  反例: q=ϑ_0(0) <o a=ϑ_5(0)。Kn 0 q={ϑ_0(0)}, Kn 0 a=Kn 0(Su[])={}。∴ Kn 0 q ⊄ Kn 0 a 由来の制御に乗らず q∉M_0。
  K-単調性「q<oa ⟹ Kn n q が Kn n a に支配される」も同反例で FALSE。∴ connection を downward-closure で出す素朴ルートは全滅(既存 Mn/AccB/Acc も同病)。
- **omfree は FC=∅ の単一基底(Acc_{-∞})**: omfree 項は Ω を含まず FCset={}→全て「可算」=Towsner の M_{-∞}。
  Ω-ground で sub-stratify されない(gnd≡0)。∴ omfree fragment 全体を 1 レベルで一括 WF する必要＝Lemma 3.10 の -∞ 版＝まさに L_ThF。Th-subscript stratify(続37)も自己参照(ϑ_j(g) は Kn(≥j) に自分自身を含む)で破綻。
- **核の正体(確証)**: 残差 ϑ_5(0)∈acc 等は**真**(masterF で言えば 0∈acc からの崩壊閉包 level5)だが、
  level-k 帰納(k=n)は level<k しか与えず到達不能。P(0)="∀r. ϑ_r(0)∈acc" は ϑ_1(0) の predecessor ϑ_0(ϑ_100(0)) が ϑ_100(0)∈acc を要求…と r 無界に相互依存し、r にも h にも size にも整礎順序が無い。
  ＝**Buchholz の崩壊関数整礎性定理の既約核**。素朴帰納(level/acc-on-d/size/構造)では原理的に閉じない(本セッションで全て反証)。
- **確定した次フェーズ**: multi-ψ_n(ϑ_n, n∈ℕ)の整礎性を Buchholz 1991/Schütte 流の **全 level 同時の超限構成**で。
  §3.2 単一 ϑ の素直な移植では p<r が抜けるので、subscript を明示扱いする独自拡張が必須。複数セッション規模。
  - 候補: Buchholz の C(α,β) 閉包 or operator-controlled。あるいは Ω_n 足場を証明内に導入し ϑ_n を Ω_n 崩壊として multi-level Acc_n を全 n 同時帰納で構成し、最後に omfree(=Ω_n を含まぬ像)へ connection。
- **状態**: baseline 緑・3 sorry 不変(L_ThF 残差1点 / olt_trans Su/Su / op_NF)。本セッションは核の構造解明と誤ルート(downward-closure, Th-subscript stratify, level/size 帰納)の確定的反証＝今後の手戻り防止が成果。

### 進捗 (2026-06-09 続39): 【Route 確定】proofs.thy は lex/NF の対角 accessibility に帰着＝ユーザー本来の設計。両ルート収束＝L_ThF が臨界経路
- **proofs.thy 再読の発見**: 最終目標 `wf Rnf` は **`three`(mechanized lex 順序)を NF=translate`ST_PS(標準形)に制限**した Rnf。
  ot/buchholz/embed は私が足した**並行ルート(Route A)**。proofs.thy(ユーザー設計)は `wf_Rnf_from_diag` で **対角 accessibility `∀v. D(v)=translate(diagSeq 0 v)∈acc Rnf`(Route B)に帰着済**。
- **Route A は過剰一般化**: wf_oltRwF は**全 omfree 項**(非標準形 ϑ_0(ϑ_100(0)) 等の病的 buried-subscript 項を含む)を対象＝厳密に必要以上に難しい。
  残差(r≥n buried collapse)を生むのはまさにこの非標準項。NF(標準形)は -s でそれらを除外。
- **しかし Route B も Buchholz 核を含む(確認)**: lex 順序が NF 上で整礎なのは「標準形＝真の順序数表記」だから。
  その順序同型＝Buchholz 構成そのもの。acc Rnf ＝「expand 停止」の言い換え(ST_PS は diag+expand 生成, expand は減少)で**循環**＝独立に易しくならない。
  対角 D(v)=ϑ_0(ϑ_1(...ϑ_v(0))) は基本列で cofinal・増加。その accessibility＝順序数の整礎性核。
- **結論(確定)**: **どちらのルートでも Buchholz WF 核が臨界経路**。Route A の L_ThF を完成させ wf_oltRwF→(embed/op_NF)→wf Rnf が、ot 機構を再利用できる分むしろ近道。
  ＝**L_ThF(multi-ψ_n distinguished-set 構成)に集中**で正しい。ユーザー指示「Buchholz/Towsner variant で行くしかない」と完全一致。
- **次の実装(multi-ψ_n, Ω 足場)**: omfree は FC=∅ 単一基底だが、その整礎性証明には Ω_n を**証明内に足場導入**し全 n 同時帰納で multi-level Acc_n を構成、最後に omfree(=Ω を含まぬ像)へ connection するのが正道。
  §3.2 単一 ϑ では p<r が抜けるので subscript 明示の独自拡張。Buchholz 1991/Schütte 流。複数セッション。次セッション: scratch_wf.thy で定義＋connection を build 検証から着手。
- **退化バグ特定(actionable)**: wo.thy `FC_def`/`gnd_def` は `FCset={}→0`。これが Towsner の **−∞ レベルを level 0 に潰している**。
  Towsner では sup∅=−∞, min∅=−∞ で omfree(FCset={}) は **FC=−∞ の可算基底 M_{−∞}**。現慣習(=0)だと omfree が level 0(Ω_0 と同列)に化け、stratify 退化。
  ∴ 構成では FC/gnd を **−∞ を持つ型(int option / 番兵)**で定義し直し、omfree を真の −∞ 基底に置くのが正道。Acc_{−∞}⊆acc は omfree の oltRwF-下方閉から自明(Awf 定義)。
- **但し −∞ 修正だけでは閉じない(再確認)**: 3.10 を −∞ で multi-ϑ_n に展開すると predecessor ϑ_s β(s<r, cross-subscript)ケースが残る。
  β 任意 omfree で buried ϑ_{r'}(h)(r' 無界)を含み得る＝**multi-ϑ_n 固有の既約核**(単一 ϑ には無い)。dom/s=r ケースは clean、s<r が核。
  ＝Buchholz ψ_n 整礎性定理の本体。subscript への帰納＋coefficient 制御の超限構成が必須。これが「実装すべき残り全て」。

### 進捗 (2026-06-09 続40): 【アーキテクチャ分岐確定】絶対§2系では shift-down が ill-founded 領域を生む＝Towsner §3 多相系が正道
- **scratch_wf.thy green seed 作成(ROOT 登録, build RC=0, 20-30s 高速ループ確立)**: 修正版階層の base(Mbot=−∞)＋
  `Abot_iff_acc`(base level は acc oltRwF と同値＝tautological＝gap の明示)＋詳細実装計画(Towsner 3.8-3.12 多相版の補題列)をコメントで記載。
- **致命的発見(shift-down)**: (B2) s<r cross-subscript の buried 高崩壊 ϑ_{r'}(h')(r'≥r) を処理するには Towsner は shift で ground を下げ Ω に吸収する。
  だが**絶対 int 系では shift k(Th r' h')=Th(r'+k)(shift k h'), k<0 で添字が負に**＝ϑ_{-k} は **ill-founded**(memo 既述: ϑ_{-(k+1)}0<oϑ_{-k}0 無限降下)＝acc に居ない。
  ∴ **shift-down が accessibility を保たない**＝絶対系では Ω-scaffolding が shift で機能しない。wo.thy「絶対§2＋§3.2証明」ハイブリッドの根本的破綻点。
- **結論(アーキ分岐)**: Towsner の distinguished-set 証明が実際に閉じるのは **§3 多相系(単一 ϑ＋相対 Ω de Bruijn, ΩpJq)**。
  そこでは shift が Ω-index に吸収され負領域を作らない。我々の絶対 multi-ϑ_n(§2)では閉じない見込み大。
  - **選択肢(a)**: §2 を int-option ground で refactor＋多相版 ladder を絶対系に無理に移植 → shift-down 問題で詰む可能性大。
  - **選択肢(b)**: WF ターゲットを Towsner §3 多相系(新 datatype: 単一 ϑ＋ΩpJq de Bruijn)に切替、§3.2 を素直に移植して wf を閉じ、three(PSS)→§3系 へ embed。大改修だが**証明が実際に閉じる正道**。
  - **選択肢(c)**: 別の WF 証明(Buchholz 1991 operator-controlled 等)。
- **次アクション**: ユーザーに方針相談(§3 多相系への切替が妥当か、特定の構成/参照の意図があるか)。＝研究級の真の分岐点で domain 知識が数セッション分を節約。

### 進捗 (2026-06-09 続41): 【続40 を訂正】shift-down 問題は omfree では生じない可能性大→絶対系を先に実験すべき
- **続40 の shift-down 悲観論を訂正**: `norm a = shift(−FC a) a`。**omfree 項は FCset=∅→FC=0→norm=恒等**。
  ∴ 3.10/3.11 の正規化シフトは**omfree ターゲットでは恒等**＝負添字 Th を作らない。shift が Om を生むのは Om 含有中間項のみで、それは ground レベル(M_n の gnd≥−n 制約)で処理される(Towsner の Ω_{−1} 扱い)。
  Th 添字 r' は FCset に寄与しない(FCset は Om index のみ)ので正規化対象外。∴ buried ϑ_{r'}(h') の正規化で負添字化は起きない。
- **修正結論**: 絶対§2 系でも **omfree ターゲットの collapse closure は distinguished-set で閉じ得る**。§3 への大改修は early。
  まず **scratch_wf で Om-scaffolded distinguished-set を実験的に構築**し、(B2) s<r ケースが level-drop で閉じるか高速ビルド(20-30s)で実証すべき。
- **次セッションの具体作業(fresh context 推奨)**: scratch_wf の実装計画に沿って
  (1) prev に Mbot(base) を含む修正 Mn' 定義、(2) connection(Acc n⊆acc, master と組で n 帰納)、(3) 3.10 collapse closure を experimental に。
  ビルドが速いので theorize より code＋build feedback で進める。ユーザー相談は absolute が実証的に詰んでから(§3 切替判断時)で十分。

### 進捗 (2026-06-09 続42): 【§2 絶対系の循環を具体的反例で確証】＝§3 切替判断点
- **scratch_wf 実装進展(green)**: `Accl_omfree_acc` の **within-level predecessor ケースを実証明**(acc(R_n)-帰納, q∈Mlv は accIH で閉じる)。
  残差は cross-level(q∉Mlv n)1点に分離。Mlv/Bst/Accl 定義＋単調性＋Bst_omfree_acc(n 帰納)も green。
- **§2 絶対系の循環＝具体例で確証(decisive)**: collapse closure CC(r): e∈acc⟹Th r e∈acc を subscript r 帰納で試みると:
  - level 0 は clean(predecessor の p<0 が nneg で不可能→cross-subscript 無し)。
  - level r>0 の p<r predecessor `Th p e'` は e'∈acc を要し、e' の **buried `Th s g`(s≥r)** で詰む。
  - **最小反例**: `Th p (Th r 0) <o Th r 0`(p<r, control は Kn p(Th r 0)=Kn p 0={} で vacuous 成立)。
    ∴ acc(Th r 0) は acc(Th p(Th r 0)) を要し、後者は CC(p)[arg=Th r 0] 経由で acc(Th r 0) を要す＝**直接循環**(実サイクルではない: Th r 0≮o Th p(Th r 0) を確認、asym OK)。
  ＝局所帰納(subscript/acc/構造/size いずれも)では原理的に証明不能。**インピーディカティブ**。
- **§3 多相系が必要(確定)**: de Bruijn Ω^{(J)} の相対化で buried subscript が有界化され、Towsner 3.7-3.12 の全 n 同時 distinguished-set 構成で循環が解ける。
  絶対§2 には公刊 WF 証明が無く、上記循環で自前証明も不能。
- **ユーザー相談事項(方針分岐)**: (b)§3 多相系へ datatype 切替(大改修, Towsner 証明が閉じる正道) / (b')§2→§3 順序埋め込み(§2 資産再利用＋§3＋embed 追加) / (c)別構成 / (d)WF を文書化前提として他全証明で完了。

### 進捗 (2026-06-09 続43): 【方針確定 route(A) 意味論】PDF 精読で順序が lex と判明・AFP 導入へ
- **PDF 精読(conventionals.md に要約, PDF 再読不要)**: Buchholz 1986 を実読し**根本的誤りを発見**:
  - Buchholz の順序 (<2) は `D_u a<D_v b ⟺ u<v∨(u=v∧a<b)` ＝**純粋辞書式, K-domination 無し**。
  - ∴ `wo.thy` の `ot`(K-dom) は **Buchholz と非互換の私の誤変種**。`mechanized.thy` の `three`(lex, 線形性 green) が正しい Buchholz §2 系。
  - WF 対象は OT(標準形, OT3=`G_v b<b`)。`proofs.thy`(three/lex/NF→対角 accessibility)が正しい配線。
  - **3 sorry の整理**: olt_trans は mechanized で既 green; op_NF は three→ot 埋込が不要で消滅; 残るは**対角 accessibility(=OT の lex 整礎性)1点**。
- **WF 証明 = Buchholz 意味論 (route A, ユーザー確定)**: o:OT→順序数(ψ_v) の順序同型(Lemma 2.2(c) `a<c⟹o(a)<o(c)`, 2.3)で WF。
  ＝ §3 多相系への datatype 移行は不要、絶対系 `three` のまま。
- **要 AFP/ZFC_in_HOL**: ψ_v は Ω_v=ℵ_v(非可算基数)を使うため順序数ライブラリ必須。AFP 未インストール→ネット可→**AFP 導入中**(ユーザー承認 "1")。
- **次作業**: AFP 導入→ZFC_in_HOL ビルド→`psi.thy` で §1(C_v/ψ_v/補題1.2,1.3,1.5)＋§2(OT,o,Lemma2.2(c))転写→`three` の lex 整礎性→proofs.thy 対角 accessibility 接続。
- **規模注意**: §1-2 の意味論転写は ℵ_v の正則性・基数算術(|C_v(α)|<Ω_{v+1})を含み大(多セッション)。ZFC_in_HOL の cardinal/regularity API を要確認。
- **誤迂回の扱い**: wo.thy/buchholz.thy/embed.thy(K-dom ot) は route A では不要→破棄候補(当面は残置、A 完成後に削除)。

### 進捗 (2026-06-09 続44): 【route A 実装着手】ZFC_in_HOL 上に Buchholz ψ_v 構成中（ord/psi.thy, session PSI, green）
- **AFP 導入済**: `/home/koteitan/afp-dl/afp-2026-06-05`（Isabelle2025-2 対応）。`ZFC_in_HOL`(順序数/基数/Kirby 順序数和/Ordinal_Exp ω^/ZFC_Cardinals Aleph) 利用。
  ビルド: `cd git && isbman build -m .. -d /home/koteitan/afp-dl/afp-2026-06-05/thys -d /home/koteitan/proofs/ya-pss/git PSI`（**-d は絶対パスで**, cwd 不安定なため）。ZFC_in_HOL ヒープは git ディレクトリの isbman 隔離heapにキャッシュ済(再ビルド ~40s, PSI のみ ~1-10s)。
- **ord/psi.thy (session PSI in ord, ROOT 登録済) の green 内容**:
  - `Om v`(=Ω_v=ℵ_v, v>0; 1 if v=0)＋ Ord/Card/単調(Om_less_Suc)。
  - `Cstep`/`Cset`/`psi`(=transrec で C_v(α)＝Om v からの「+閉包∪{p ξ u:ξ∈X∩α}」反復の可算 sup, ψ_v α=LEAST Ord∉Cset)＋`psi_unfold`。
  - **well-defined**: `psi_ex`(Cset small ⟹ 全順序数は含まれない, big_ON)・`Ord_psi`・`psi_notin`(ψ_v α∉C_v(α))。
  - **閉包 C1-C3**: `Om_subset_Cset`・`Cset_add_closed`(+)・`Cset_psi_closed`(ψ_u, ξ<α)＋補助(elts_Cstep, Citer 単調 Citer_subset_mono, Cset_mem_iff)。
- **ZFC_in_HOL API メモ**(再利用): small(elts x)=small_elts; small(f`X)⟸small X=replacement[OF .., where f=..]; small(UNIV::nat)=small_image_nat[of "λx.x" UNIV]; small_Times; smaller_than_small[OF small_elts Int_lower1]; elts_sup_iff; elts_Sup(small range); big_ON(¬small ON=Collect Ord); Ord_LeastI_ex/Ord_Least; less_succ_self; Aleph_increasing/InfCard_Aleph; ≤ on V = less_eq_V_def(elts⊆elts); 順序数和は Kirby の +。**型注意**: nat 添字は `(UNIV::nat set)` 明示で多相化回避。
- **次(§1 続き→§2)**: Cset⊆Ord; Lemma 1.2(ψ_v 0=Om v, Om v≤ψ_v α, ψ_v α∈P 加法的主要数, |Cset|<Om(v+1)⟹ψ_v α<Om(v+1)＝基数算術); 1.3(ψ_v 単調: α<β∧α∈C_v α⟹ψ_v α<ψ_v β, psi_notin 利用); C の α 単調; 1.5; 1.9(G_u). →§2: o:three→V, Lemma 2.2(c) 順序保存 → three/NF の lex 整礎性 → proofs.thy 対角 accessibility。

### 進捗 (2026-06-09 続45): route A §1 大幅前進（ord/psi.thy 全 green, Lemma 1.3 まで）
- 追加 green: `Om_le_psi`(Ω_v≤ψ_v α)、C の α 単調(`Cstep_mono_param`/`Citer_mono_param`/`Cset_mono_param`/`CC_mono`)、
  `psi_mono_arg`(α≤β⟹ψ_v α≤ψ_v β)、**`psi_strict_mono_arg`=Buchholz 1.3**(α<β∧α∈C_v α⟹ψ_v α<ψ_v β, 順序保存の鍵)。
- ZFC_in_HOL API 追加メモ: `Ord_Least_le`(⟦Ord k;P k⟧⟹(LEAST i.Ord i∧P i)≤k)・`Ord_LeastI`・`Ord_mem_iff_lt`・`Ord_not_le`・`Ord_in_Ord`・`Ord_add`(順序数和閉)。
  **罠**: schematic 補題(Ord_psi 等)を `[OF]` に渡すと multiple unifiers/HO 暴走→ **`rule`+明示ゴールで unification 駆動**、または `[of ..]` で固定。`auto`+条件付補題は後ろ向きループ注意(Ord_in_Ord)→決定的に。premise は ⋀⟹ より ∀⟶ が [OF] 安全。
- **次**: Lemma 1.2 残(ψ_v 0=Ω_v, ψ_v α∈P 加法的主要数, ψ_v α<Ω_{v+1}＝基数 |C_v α|<ℵ_{v+1}), 1.5, 1.9(G_u)。→§2: o:three→V, Lemma 2.2(c) 順序保存(psi_strict_mono_arg 利用)→ NF lex 整礎性→ proofs.thy 対角 accessibility。

### ★(2026-06-10) pure-lex に回帰 + wfE 設計の決定的発見
- route A（ZFC 順序数 ψ）破棄：oV=Buchholz ψ 値が PSS 標準形の対角を collapse（D(2)=D(3)
  が同じ ψ_0(ψ_2(0))；P進ブログ comment 欄/Maksudov 標準形条件 β∈C_ν(β) で確認）。順序数経由は原理的に閉じない。
- 本命 = **pure-lex 構文的 WF（wf.thy, 順序数なし, sorry 1個）**。PSS_terminates ⟸ wf_Rnf ⟸
  wf_Rnf_from_within_level[OF wfE_within_level]。maxsub 単調(maxsub_mono_NF')＋CNF(cnf_ST_PS)は緑。
- **★決定的: olt は全 three（添字有界でも）で整礎でない。** 反例 `t_k = D_0^{k+1}(D_1 0)` は
  無限降下（全添字≤1）：t_0=D_0(D_1 0) > t_1=D_0(D_0(D_1 0)) > …（各段、引数先頭添字 0<1 で減少）。
  ⟹「添字有界フラグメント WF」は偽。`wfE` は **NF 不変 inv2（spine が 0,1,…,m で始まる）が本質**。
  t_k は inv2 違反（spine=[0,0,…,1]）で NF から排除される。
  ⟹ wfE 証明は inv2/cnf を最後まで通す必要。multiset 和還元も base(args)が一般には非WF＝NF threading 要。
- wfE 攻略の足場: NF level-m 項は spine=[0,1,…,m] prefix（inv2）。先頭 D_0(b_0), b_0 の spine は
  [1,…,m] で始まる（1段シフト）。崩壊核は Towsner §3.2 ladder を構造参考に独自帰納で。

### ★(2026-06-10 続) 和の層剥離 完了（wfsum.thy 緑）→ 残 sorry = wf_ArgsL ただ1つ
- wfsum.thy: NF=非増加和 p0(b_i)（NF_lead0/NF_zerotops/sargs_noninc）、olt=lex on 引数列
  （olt_sum_decomp 先頭差分分解）→ multiset 拡張に埋め込み（olt_sum_mult, one_step_implies_mult）
  → wf_mult+inv_image でレベル内 wf（wf_level_from_args）→ wf_UN で全レベル（wfE_from_args）
  → wf_Rnf → PSS_terminates。**ライブチェーンの sorry は wf_ArgsL のみ**。
- デバッグ教訓: 500s runaway の原因は sorted_wrt まわりの auto/metis。bisect は「新規部を別theory
  (wfsum) に分離して本体 green を維持」が速い。`wf_mult[OF wf_ArgsL]` は隠れ schematic ?m に
  `of margs` が誤適用 → `wf_ArgsL[of m]` 明示。連言 hyp は simp で分割されない → auto。
- **wf_ArgsL の実証調査（tools/wfe_explore.py, ST 214項）**:
  - ArgsL 元の (lead, maxsub): level0→(0,0), level≥1→lead=1 のみ。危険な t_k 型（lead0 で
    中に1以上）は**トップ引数位置に出現しない** ⟹ wf_ArgsL は真の見込み。
  - 深さ1・深さ2 の引数はすべて consec-from-lead（spine が [lead..max] 連続）。
  - **深さ3以降で consec は破れる**（例 p2 の引数 spine [1,0,1,2,…]）⟹ consec の遺伝的帰納は不可。
  - **頑健な遺伝不変条件: lead(arg) ≤ sub+1**（全主要部分項 1684 個で違反 0、lead=sub+1 は到達）。
- 次段設計: 引数クラスの帰納は (i) lead≤a+1 + cnf の規律で Towsner 風 ladder を組むか、
  (ii) 引数クラスを数列側（部分ブロックの translate）で特徴づけ sub-block 不変条件を nfinv_ST_PS
  流に証明するか。深さ1,2 の綺麗さは (ii) を示唆。

### (2026-06-10 続2) wf_ArgsA の knot 分析（設計上の確定事項）
- 一般 peel 完了で chain: PSS_terminates ⟸ wfE ⟸ wf_ArgsL ⟸ wf_SingA ⟸ **wf_ArgsA**（唯一 sorry）。
- **有限 peel では閉じない**: 和 peel→添字 peel→引数…の繰り返しは構造的に底をつかない。
  添字 j の singleton p_j(c) の前者には任意の p_i(d) (i<j, d 任意) が来る → 下から順も上から順も循環。
  lead(arg)≤a+1 で「p_a の引数はレベル a+1 材料」だが maxsub≤m の cap の所で lead-0 再入
  （実測 (a,lead)=(2,0) あり）→ 添字 0→…→m→0 の閉ループ＝ψ collapse の非可述性そのもの。
- **レベル 0 は閉じる**: wf_ArgsA 0 は単一添字 p0 の遺伝的 cnf クラス → PrSS hord/multp と同型の
  構造帰納（acc-of-multiset + constructor-acc）で証明可能。これが ladder の base。★次の実装対象。
- **ladder の正しい形**（Towsner Def3.7 の構造のみ借用）: レベル m の帰納で
  「∀i<m. レベル i の全クラス wf」を仮定に持つ形に再編。within-level-m の危険な再入
  （t_k 型・lead-0 部分）は「critical 部分項が ⋃_{i<m}Acc_i に入る」型の条件で制御する
  M_n 流のクラス定義が要る（純構文条件では t_k を排除しつつ NF 材料を含む線引きが未確立）。
- 次手: (1) wf_ArgsA の m=0 を prss 流に証明（実装可能・base 確立）。
  (2) m 帰納の statement 再編（wf_ArgsA を「∀i<m wf 仮定」付き compound induction へ）。
  (3) critical-subterm 条件の設計（P進の Adm/Mark に相当する切り口の可能性も検討）。

### ★(2026-06-10 続3) 崩壊核クラスの不変条件 狩り（dual-OT3 発見と x_k 反例）
- **dual-OT3 (ok3) 発見**: 「主要部分項 p_a(c) で lead(c) ≤ a ⟹ c <o P a c Z」
  （引数が項を超えるのは真正 climb＝lead=a+1 のときだけ）。
  genuine 全 3132 箇所（ST 695 項）で違反 0。t_k=D_0^k(D_1 0) 連鎖を正確に排除
  （F(t)=P 0 t Z の反復は2段目で ok3 違反）。Buchholz OT3 (G_v b<b) の ascending 双対。
- **しかし ok3 でも不足**: 交互チェーン x_k = p0(p1(x_{k-1}))（核 X=p1(0)、spine [0,1,0,1,…,1]）は
  inv2 ✓ cnf ✓ ok3 ✓ consec ✓ で無限 <o 降下。reduced(M_k) も True（P進 Red では排除されない）。
  防壁は ST_PS 非所属のみ: 深 BFS（268029 форм, len≤18, seed≤5, n≤6）で
  (0,0)(1,1)(2,0)(3,1) は standard、(0,0)(1,1)(2,0)(3,1)**(4,0)** も standard だが
  (0,0)(1,1)(2,0)(3,1)**(4,1)** = x_1 は**非 standard**。
- ⟹ 第4の不変条件は **行1の許容性（P進の Adm/parent1 規律）** に対応する項側条件。
  (2,1) が (1,1) の子は OK（x_0=(0,0)(1,1)(2,1) standard）だが、(2,0) を挟んで再上昇した
  (3,1) の上にさらに (4,1) は禁止される——「climb の後の同レベル再 climb」の制御。
- 次段: (a) 標準/非標準の近接ペアを大量に diff して Adm 由来の項側条件 (adm3) を同定、
  (b) ladder クラス = inv2+cnf+ok3+adm3 で within-level 帰納を再設計、
  (c) NF ⟹ 各不変条件の Isabelle 証明（nfinv_ST_PS/cnf_ST_PS の流儀）。

### (2026-06-10 続4) adm3 対照データ＋P進 Adm 定義
- P進 Adm: `nadm M j ⟷ j > Lng M ∨ (nextR M 1 (j-1) j ∧ nextR M 1 j (j+1))`（行1 Next 連鎖の
  中間 index が非許容）。Adm M j = j が許容ならj、否なら直前の許容 index。
- 対照（corpus 9274 standard）: 一般には row0 連続 [·,1][·,0][·,1] の直後 row1=1 は許容
  （674例; 2 も 234例）。**しかし (0,0)(1,1)(2,0)(3,1) 開始では5番目 row1 は常に 0**
  （779例; 1/2 は 0 例）＝x_1 を排除する規則は局所でなく行1木（親子文脈）依存。
- ⟹ adm3 の項側化には three の添字を「行1値」として読む行1-Next 構造の項上対応物が要る。
  次バースト: (a) 行1木を three 側で再構成（spine/添字列から nextR1 を復元できるか）、
  (b) x_1 文脈で (4,1) が禁止される正確な理由を P進 §6（content.md 行1木/Red/Adm 節）で特定、
  (c) adm3 候補を定式化→ genuine 検証→ ladder クラス {cnf, ok3, adm3} で再挑戦。

### (2026-06-10 続5) LPO 還元の検証（否定的だが決定的な近さ）
- 仮説「NF 上で olt = LPO（添字 precedence, lex status）」を検証: 400 NF 項の全対で
  **159332 一致 / 268 不一致**。不一致は全て olt=T/lpo=F、典型パターン
  `p0(p1(0)+p0(X)) <o p0(p1(0)+p1(0))`（任意 X）＝ subscript-first の無条件
  `p0(X) < p1(0)` が LPO の引数 guard (∀args<t) と衝突。collapse の本質そのもの。
  ⟹ 古典 path-order（LPO/RPO/WPO）への直接還元は**不可**。
- 標準 near-miss 5984 例 vs 標準全位置: 局所規則 hasP1（正 row1 は親1を持つ）と
  climb≤p0(r1)+1 は標準側違反0だが x_1 を殺せず。x_1 の悪さは局所でない。
- 残る攻め筋（次バースト）: (i) P進 content.md §6-7 を精読し標準形の emergent 不変条件
  （Trans I–VI が前提にする構造）を抽出, (ii) parent1 横方向比較（copy 由来の bound）の
  規則 mining 続行, (iii) minimal-bad-sequence を NF の展開系譜と組み合わせる新規路線
  （Kruskal/Veldman 流: bad seq の極小性 + 展開生成性で矛盾を導く）。

### (2026-06-10 続6) P進 §6-7 精読の結果（降順性は x_1 に無力、戦略再評価）
- P進「降順性」: 標準形の le0-切片は単項かつ Br(切片) が (row0頭,row1頭) lex 非増加
  （k帰納で証明済 in content.md）。**しかし x_1 では全切片の Br が単数で空虚**＝x_1 を殺せない。
- 横ばい子（r1[child]=r1[parent]≥1）は trunk 上/外どちらにも大量出現（2453/1977 等）→ 局所規則不成立。
- 系譜: (0,0)(1,1)(2,0)(3,1) = x_0[2]、(0,0)(1,1)(2,0)(3,1)(4,0)(5,1) = x_0[3]。
  x_1=(…)(3,1)(4,1) は「コピー元 (2,1) が子を持たないのに copy に子を生やした」非正規表記。
  ⟹ 排除条件は「各部分木の形がコピー系譜と整合」型＝生成依存。純局所構文では届かない公算大。
- P進の停止性本体 (content.md 2821-) は decrease + [Buc] OT-WF 引用構造であり wf 核の新手法は無し。
- ⟹ **残る本物の内容 = Buchholz Lemma 2.2（OT 整礎）級の核**を pure-lex/NF 向けに自前構築する事。
  次バースト: [Buc1] §2 Lemma 2.2 の証明本体を精読（o の順序同型経由か、構文的か）し、
  NF-pure-lex に直接移植できる形（または Acc_n 型の非構文クラス定義）を設計する。

### ★★(2026-06-10 続7) Buc1 §2 精読 → route A 資産の正しい解釈（サルベージ可能性）
- **Buchholz OT の順序 (<2)(<3) は pure-lex そのもの（olt と同一）**。OT と NF は
  「同じ項型 three・同じ olt 上の異なる正規形クラス」：OT=G条件名（降順正規）、NF=昇順タワー名。
- D(2)=D_0D_1D_2(0) の OT3 違反は「collapse する非正規名」だから（同値の正規名 = D_0(D_2 0)、
  ψ0ψ1ψ2(0)=ψ0ψ2(0) のブログ事実と完全整合）。
- ⟹ **route A の psi.thy（§1 完備）＋ otembed（wf3=OT, oV_order_pres 4ケース緑）は
  『wf(olt on wf3クラス)』の証明として誤りでなく、ほぼ完成していた**。偽は NF⊆OT のみ。
  Ccond（o b∈C_a(o b)）は OT3 から Buchholz 1.9（G_u γ⊆α ⟺ γ∈C_u α）経由で証明可能
  → 2.2(c) が OT 上で閉じ、wf_VWF 経由で **wf(olt on OT) が sorry-free になる見込み**。
- 残る橋: **NF→OT の順序保存（または値同値）変換**＝P進 Trans 級。content.md §7（2044-2821,
  scb分解/Mark/条件I-VI/許容的親子）に完全な構成の参照あり。
- 分岐: (α) pure-lex 自前帰納のクラス探し続行（x_k で生成依存と判明、未解決級リスク）
  vs (β) wf(olt on OT) 自前完成＋NF→OT 橋（重いが参照完備; pss-proof との差別化=2.2自前+pure-lex前半）。
- 次: (β) の根拠固め＝ord/psi.thy に 1.9 を追加し otembed の Ccond を wf3 クラスで閉じる
  （ROOT に PSI 復活、ZFC ベースのまま）。閉じたら方針相談を提示。

### ★★★(2026-06-10 続8) wf_olt_wf3 SORRY-FREE 達成（Buchholz Lemma 2.2 自前証明）
- **`wf {(w,x). olt w x ∧ wf3 w ∧ wf3 x}` が sorry なしで緑**（PSI: psi.thy + otembed.thy、
  ZFC_in_HOL 上の自前 ψ 意味論）。pss-proof が引用で済ませる Buchholz 2.2 を独自に完全証明。
- 鍵: (i) C_build（G-臨界値 < α ⟹ oV t ∈ C_v(α)；v 超え添字は Ω 跳躍で C1、v 以下は ψ閉包+OT3）、
  (ii) oV_order_pres を Buchholz 流 **left-size 主帰納**（右項 arbitrary）に再構成し
  Ccond を IH から導出（Gterm_size / wf3_Gterm）。otembed は NF 非依存（YAPSS.mechanized のみ）。
- 残る橋＝ **NF → wf3 の順序保存変換**（collapse する昇順名を OT 正規名に潰す Trans 級写像）。
  これが埋まれば wfE（pure-lex 側）も wf_subset で閉じる。
- 全体の現状: 2 本柱が完成: (A) pure-lex 前半（def/mechanized/proofs/wf/wfsum: 減少+maxsub+CNF+
  peel+level0、残 sorry = wf_ArgsA）、(B) wf_olt_wf3（sorry-free）。橋 1 本でどちらの経路でも完結:
  (β1) NF→wf3 順序埋め込み ⟹ wfE 直接 ⟹ wf_ArgsA 不要。
  (β2) ST_PS→wf3 翻訳+展開減少 ⟹ 停止性直接（pure-lex 前半をバイパス、P進構成に近い）。

### ★(2026-06-10 続10) seqlex.thy 緑: translate は列 lex への順序同型（olt_iff_seqlex, sorry-free）
- blockok d（row0≥d・先頭=d・ステップ≤+1）の下で olt(translate M, translate N) ⟺ seqlex M N。
  証明: 長さ和帰納＋先頭差分の arg/tail ゾーン整列（seqlex_arg_or_tail）。1ビルド15分で完成。
- 残: ST_PS ⊆ blockok 0（標準形の row0 規律、ST_PS.induct で oper の保存性）→ wfE の BMS ネイティブ化:
  wfE ⟺ 「seqlex の標準形無限降下なし」。
- デバッグ教訓: 新 theory はまず単独でビルド可能に小さく（metis 乱用が 90s+ ループ源、
  stepprops_tl 型のヘルパで決定化）。`case Cons2: (Cons q rr')` が正しい label 構文。

### ★(2026-06-10 続11) seqlex.thy 完全緑（sorry-free）: 標準形の blockok 規律＋順序同型
- blockok_ST_PS（diag: nth計算 / oper: steps1 合成則。コピー junction は
  e0(j1)-e0(j1-1)≤1 に帰着、i1=1 は le0_entry0_mono、i1=0 は nextrel0_entry0_less）。
- **olt_ST_iff_seqlex: 標準形上で translate M <o translate N ⟺ seqlex M N**（順序同型、sorry-free）。
- wfE は「ST_PS（同 maxsub）上の seqlex 整礎性」と同値に。
- デバッグ根因: steps1_append case3 の `by auto`（IH 不使用）が発散。教訓: 帰納 case の
  auto には必ず IH を using で渡す。HO unification は [where n= and F=] で明示。
- 現状の全体図: (A) pure-lex 前半＋peel＋level0（sorry=wf_ArgsA のみ）
  (B) wf_olt_wf3 sorry-free (C) olt=seqlex sorry-free。
  残る本丸は不変: 崩壊核（wf_ArgsA ⟺ seqlex-WF on ST ⟺ NF→wf3 橋のどれかを閉じる）。

### ★(2026-06-10 続12) (α)決定後の設計探索: ArgsA 実証＋Towsner WF 構造の完全解析
- ユーザー決定: **(α) wf_ArgsA を自前帰納で閉じる**（wf_olt_wf3 は oracle 候補として使用可）。
- ArgsA 実証（tools/argsa_check.py, corpus 1550）:
  - y_k 連鎖（y_0=p1(0), y_{k+1}=p0(p1(y_k))）は k≥1 で ArgsA に**不在** ⟹ wf_ArgsA 真の見込み。
  - **y_1 = translate((0,0)(1,1)(2,1)) ∈ NF**（標準!）、y_2 = translate(x_1) から非標準。
    降下アンカーは「re-entry 後の横ばい climb」p1(p1(0)) の位置（Adm 規律の項側像）。
  - ArgsA[m] は m≥2 で全員非 NF（lead≥1 の内部ブロック、spine 下降混在 [2,1,0,1,2,…]）かつ
    全員 maxsub=m（**レベル降下なし＝再入**）。ArgsA[1] は NF/非NF 混在。
  - 標準族 t(x_0[n])=p0(p1(p0(p1(…p0(p1 0)…)))) は re-entry 入れ子 rank~n **無限大**で olt **上昇**列
    ⟹ 入れ子深さ有界は不変条件にならない（続3の補強）。
- Towsner §3.2 完全解析（2504.02131v2）:
  - 順序定義自体に **K-guard**（ϑα<ϑβ ⟸ α<β ∧ ∀γ∈K^{<0}α. γ<ϑβ）。y 型連鎖は
    **順序の段階で降下にならない**（guard 違反で非比較）。
  - Acc_n/M_n 梯子（M_n = FC=0 ∧ G≥-n ∧ K-部分項* ⊆ ⋃_{i<n}Acc_i、Acc_n=M_n の WF 部）は
    閉包補題 3.8-3.11（和/ω/ϑ-collapse、collapse は Acc_n 帰納×側構造帰納）→ Thm 3.12
    「全項 α* ∈ Acc_{G(α*)}」。最終断片 M_{-∞} は**無条件**（guard が全部支える）。
  - ⟹ **pure-lex（guard なし）には直接移植不可**。我々のクラス（標準ブロック）内降下は
    rank を無限遡行できる: y_1 の下に t(x_0[n]) が全 rank、さらに任意降下点の下にも
    tail 詰めで全 rank ⟹ 深さ/rank 梯子では降下列を単一層に閉じ込められない。
- **次の照準: Buchholz–Schütte distinguished set 法**（pure-lex 順序＋クラス条件の組で
  OT の WF を直接証明する古典手法; Pohlers 1989 PDF が手元にある）。
  クラスに要求される閉包公理を抽出 → 標準性（ST_PS 生成＋P進 Adm/条件I-VI）から
  その公理群を証明する設計へ。reduced の構文特徴づけ=条件(A)(B)（content.md 1056-）も確認済
  （ただし reduced ⊋ standard なので単独では不足）。

### ★★★(2026-06-10 続13) 大発見: 値正規化 nrm が NF→OT 順序埋め込み（実証）— (α) の新本線
- P進 Trans 全容把握: T_PS 全域で定義（Red 経由）、本体は Adm による挿入位置補正
  （条件I-VI + scb/Mark, §8 の減少証明 ~3000行）。クラス制限ではなく「修復写像」。
- 半面、衝突ペアの片割れ (0,0)(1,1)(2,1)(3,2)（=D_0D_1D_1D_2 0、stay後climb）は**非標準**と確認
  ⟹ レベル内 oV 単射性が生存 ⟹ 値写像路線が復活。
- **値正規化器 nrm を発見・実装**（tools/valnorm.py, ~40行）:
  - D_a(b): b̄=nrm(b) とし、G_a(b̄) に ¬(g <T b̄) な g があれば b̄ := max G_a(b̄) と射影し反復
    （ψ_a 定数区間の右端への投影 = 値保存の名前書換え）。和は「後方に大きい主項があれば吸収」。
  - 検証: 全像 OT ✓ / 冪等 ✓ / nrm(D0D1D2 0)=D0(D2 0) ✓ / t_k 値一定 ✓ / y_k 値一定 ✓。
- **INJ 実験: NF・ArgsA 全レベル内 + クロスレベル NF 全体（244,650ペア）で
  衝突 0・逆転 0** ⟹ 予想（α-core）: **s <o t on NF ⟹ nrm s <o nrm t**（nrm は順序埋め込み）。
- ⟹ 新本線: wf_Rnf = inv_image wf_olt_wf3 nrm。レベル分解・peel・wf_ArgsA 不要。
  残 sorry は nrm_order_pres（構文的・実証済・y_2 は非標準なので標準性規律が本質的に必要）
  ＋ nrm 像 ⊆ wf3（Gterm は構成から、hdle は吸収の弱降下から）。
- 重要: **nrm の値論的正しさは証明に不要**（順序保存・像∈wf3・wf_olt_wf3 の3点で閉じる）。
  ψ 意味論は nrm の発見的根拠にすぎない。P進 Trans との差別化: 挿入修復 vs 構造射影、
  かつ我々は Buchholz 2.2 も自前（wf_olt_wf3）。
- 次: nrm.thy（fun nrm + 像∈wf3）→ wf_Rnf 別証ルート → nrm_order_pres の本格帰納
  （クラス C = 標準ブロックの規律、NF⊆C は ST_PS.induct、y_2/stay-after-reentry 排除が鍵）。

### ★★(2026-06-10 続14) nrm 帰納の分解確定＋proj の数列側特徴づけ（E5/E6）
- **FULL proj-mono: 真の引数集合 A_a（a=0:4655, a=1:4961, a=2:1593, a=3:603）全ペアで違反 0**。
  分解: proj-mono = 弱単調 + CRUX（proj の A_a 上単射性、衝突 0 実証）。
  注意: 弱単調は任意 wf3 ペアでは大量に偽（lead 制約違反ペア; A_a は lead≤a+1 等の規律下でのみ成立）。
  min-no-fire 特徴づけ（T1）は偽（項順序と値順序が非OT項でズレるため）— 不要なので破棄。
- **E5/E6: proj は数列側で「セグメントの“最初の最大 row1 列”からの接尾辞切り出し」**
  （fire ケース 1176/1176 完全一致、遺伝的に全再帰深度で）。
  ただし no-fire ケースでは恒等（一様破棄の NTseq 定義は 3336 不一致で却下）⟹
  **測度は nrm∘translate のまま、接尾辞特徴づけは減少証明内の補題**として使う。
- ok4 候補（re-entry 引数の臨界 < ラッパー）は標準ブロックで 3144 違反 → 却下。
  (0,0)(1,1)(2,0)(3,1)(4,2)（re-entry後の2段climb）も非標準と確認。
- **アーキテクチャ確定**:
  - ord/nrm.thy: Glist/maxo/proj(膨張的・停止性=Gterm_size)/ins/nrm + wf3_nrm（証明済、ビルド検証中）
  - live chain は **nrm_step_dec**（展開ステップ減少 nrm(translate(M[n])) <o nrm(translate M)、
    単一ホスト・oper 場合分け・E6 接尾辞補題で攻める）→ PSS_terminates が inv_image で閉じる
  - nrm_order_pres（NF 全ペア保存）は上位目標として別 sorry（wf_Rnf まで閉じる）
- 次バースト: (a) ビルド緑→commit、(b) nrm.thy に step-dec 層追加、
  (c) 実証: 展開ペアの NT 第一差分を分類して oper 場合分けの証明ケース木を作る、
  (d) E6 補題（proj y (NT dom) = NT(首最大row1接尾辞)）の Isabelle 化から着手。

### ★(2026-06-10 続15) ord/nrm.thy 緑（sorry = nrm_order_pres のみ）＋ループ根因
- **PSI 緑 3s**: Glist/maxo/proj(停止性=Gterm_size)/ins/nrm 定義、proj_id/proj_rec（subst単発展開）、
  proj_wf3/proj_G/Gterm_wf3/wf3_ins/**wf3_nrm**（像⊆OT）全て証明済。
  wf_Rnf_nrm（order_pres⟹wf Rnf）・nrm_step_dec（order_pres+m_step_decreases から導出）・
  **PSS_terminates_nrm**（inv_image wf_olt_wf3 (nrm∘translate)）が rule 連鎖で完結。
- **デバッグ根因（2時間費消）**: `by (simp add: proj.simps Let_def)` — function の simps を
  simpset に入れると再帰 RHS の proj 呼び出しを無限展開（False分岐で条件未決定のまま発散）。
  **教訓: 再帰関数の unfold は `by (subst f.simps) (simp add: Let_def)` の単発展開補題
  （proj_id/proj_rec 型）を作り、それだけを使う。** simp-free の決定的 Isar
  （unfolding proj_id/proj_rec + rule）が最終形。並列処理のためエラー(line58)と
  ループが同居し 950s 沈黙→二分探索+ベースライン計測（psi+otembed キャッシュは4s）で特定。
- m_step_decreases は ST_PS 前提なし（OF L n のみ）。
- 次: nrm_step_dec の直接証明キャンペーン（order_pres から独立に）。武器: E6 接尾辞補題
  （proj y (NT dom) = NT(首最大row1接尾辞)）、E7 ケース木（第一差分は prefix/sub の2種のみ）、
  oper 場合分け機構（m_step_decreases の全補題群）。
- (続15補) 統一閉形式「proj = max(NT dom, NT 首最大row1接尾辞)」は**偽**（15302中2595不一致）。
  根因: **G_a の可視性規則 = row1 < a の列の支配ブロック内部には降りない**（Gterm の if u≤a）。
  E5/E6 の一致は fire ケース標本での偶然。⟹ step-dec キャンペーンは項側
  （Gterm/proj と構造編集 butlast/copy-append の相互作用補題）で直接進める。

### ★★(2026-06-10 続16) nrm-snoc の完全特徴づけ（Pred ケース設計確定）
- **実証定理（2263 snoc ペアで完全一致）**: 標準 C@[m] に対し nrm(translate(C@[m])) は
  nrm(translate C) から (i) 葉 D_y(0) を1箇所挿入（2220例）または
  (ii) 1つの葉の添字を増分 D_{y'}(0)→D_y(0), y'<y（43例、fire-flip、全例クリーン単一位置）
  のどちらか**だけ**で得られる。どちらも olt 厳密増加（単一位置合同）⟹ E7 の prefix/sub 二分と整合。
- fire-flip の機構: 末尾 climb 追加でタワー D_{y'}(D_y 0) 形成 → 上位 G で fire → D_y(0) に射影
  ＝「葉の置換」。タワー再帰でも単一 flip に潰れる（D0(D1(D2(D3 0)))→D0(D3 0)）。
- **証明設計（nrmstep キャンペーン）**: 関係 R = lext（葉挿入）∪ lflip（葉添字増分）。
  L1: R ⟹ olt（位置合同、容易）。**核心 = R の proj/ins-閉包**: x R y ⟹
  proj a x (R∪flip∪=) proj a y（G-集合が点ごと R-関連＋新規 leaf 臨界、max 選択の分岐が flip を生む）。
  これで nrm-snoc → translate_oper_pred の nrm 版（Pred ケース完了）。
  bad ケース（コピー）は「コピー素材の nrm 寄与 <o 最終列の寄与」を同機構で。
- (続16補・帰納設計): nrm_snoc_Rinc はセグメント版に一般化して証明
  （tail は ST_PS でないため）: 前提 = blockok/cnf/nfinv の遺伝事実（全て既存:
  blockok_ST_PS/cnf_ST_PS/nfinv_ST_PS）＋ p の付加条件（ホスト標準性から導出）。
  **声明強化**: 「NT seg の head = (y, proj y (NT dom))（top-level absorb 無し）」を
  同時帰納に含める（no-absorb が cnf＋head 保存から回る）。
  ケース: (A) p が tail 域 → IH+congruence＋no-absorb。(B) p が dom 延長 → IH(args)
  ＋ **proj_Rinc 閉包**（核心）: x' = x+leaf で x' のみ fire する分岐が flip の発生源
  （例: D1(0) vs D1(D2 0)→fire→D2(0) = lflip）。fire 構成が常にクリーン tower 形に
  なることを inv2/spine 純性（nfinv）で示すのが class 事実の使い所。
  まず無条件補題: proj_inflate（ole b (proj u b)、totality+帰納）から着手。
- (続16補2) nrmstep.thy 拡充緑: proj_inflate/proj_ole（膨張性）、Gterm_lext_sub/sup
  （臨界集合対応）、ins_noabsorb/ins_Rinc（条件付き congruence）、proj_Rinc_snoc（核心 target, sorry）。
  キャンペーン sorry 2個: nrm_snoc_Rinc（主帰納で proj_Rinc_snoc+ins_Rinc+新和分ケースに分解予定）
  ＋ proj_Rinc_snoc（fire-flip 解析、クラス事実は blockok/cnf/nfinv から導入予定）。
  live chain sorry は従来通り nrm_order_pres の1個のみ（nrmstep は攻略用で live 外）。

### ★★(2026-06-10 続17) snoc 主帰納 nrm_snoc_seg 緑！（Pred ケースの背骨完成）
- **nrm_snoc_seg 完全証明**: snocok 条件束（function 定義、dropWhile 再帰）の下で
  「1列追加 = nrm 像の Rinc 1ステップ」。3ケース（A 新和分=完全証明 / B tail=ins_Rinc 接続 /
  C arg=proj_Rinc_snoc 接続）＋基底ケース完全証明。
- nrm_snoc_Rinc = nrm_snoc_seg ∘ ST_snocok に再構成。**残 sorry: proj_Rinc_snoc + ST_snocok の2点**
  （nrmstep 内。live chain は nrm.thy の nrm_order_pres 1点のまま）。
- **Isar デバッグ教訓集（2時間級の沼、必読）**:
  1. batch の「Bad context for command X」= 直前コマンドの失敗（メッセージが出ない失敗もある）。
     probe を置いて二分すると速い。純骨格→ケース半分ずつ戻すのが結局最速。
  2. `function`+`termination` の f.simps は**既定 simp に入る**（translate/nrm/ins/snocok とも）。
     ins のように RHS が if の関数は「tail が具体的構成子のときだけ if 展開→条件地獄」
     （nC は通るのに nC' だけ落ちる罠）⟹ 計算等式は `simp only:` チェーンで段階的に。
  3. `induct rule: f.induct` は補題前提をケースに持ち上げ ?case は裸の結論。
     前提取得は **`by fact`** が最頑健（2.prems(1) は順序不定で rule が滑る）。
  4. case-fact（例 True: rest=[]）で書換えた後のゴールには rest を含む既出等式（nCs等）が
     もうマッチしない ⟹ `unfolding True` してから素の計算チェーン。
  5. simp は前提 ¬(∀x∈A.P) を ∃形に正規化するため if 条件（∀形）と噛み合わない
     ⟹ witness を obtain して takeWhile_append1/dropWhile_append1 に渡す。

### ★★(2026-06-10 続18) olt 版リストラ完了: nrmstep の sorry = ST_snocok ただ1点
- proj-Rinc 閉包は wf3 だけでは偽と実証（14541 чек中 EQ 407 = 葉が射影破棄域に入るケース、
  OTHER-ord 324。標準ホストでは end-append のため起きない）⟹
  **Rinc 保存を olt 保存に弱め、(C)分岐の proj-olt 条件を snocok 束に内蔵**。
  nrm_snoc_seg(olt版) 緑・ins_olt 緑・nrm_step_dec_pred 緑。proj_Rinc_snoc は削除。
- 残る nrmstep の sorry = **ST_snocok**（C@[q]∈ST_PS ⟹ snocok C q）只1点:
  内容 = (A)新和分: snd q ≤ snd p〔cnf/tops事実〕、(B)tail: no-absorb 2条件
  〔nrm像の hdsub/hdarg vs (snd p, pb)、兄弟順序＋nrm の head 保存〕、
  (C)arg: olt (proj y (NT rest)) (proj y (NT rest@[q]))〔E5/E6: proj=首最大row1接尾辞、
  append列は常に接尾辞内 ⟹ 同型の主張が1段深い接尾辞に再帰 = 数列側帰納で攻略〕。
- 全体図: PSS_terminates の残決定木 = nrm_order_pres（live, nrm.thy）∨
  〔nrm_step_dec 直接 = Pred(↑ST_snocokのみ) + bad ケース（コピー、同機構の拡張）〕。
- (続18補) ST_snocok_gen 緑: pre 付き一般化＋length_induct、(B)再帰は host' の結合付替え。
  最終 show は「unf iff を simp only: snocok.simps if_not_P[OF Tne] で取得→blast」
  （simp add だと等式仮定 snd p=hdsub… がゴール側 proj 引数だけ書換えて不一致になる罠）。
  nrmstep 残 sorry = ST_snoc_A（cnf/tops から snd q ≤ snd p）/ ST_snoc_B（no-absorb 対）
  / ST_snoc_C（proj-olt、接尾辞再帰）の3点。Pred ケース完成まであと3義務。
- (続18補2) **snocok を python 移植し全2263標準ホスト (butlast M, last M) で検証: 違反0**
  （A/B1/B2/C 全分岐）。3葉義務 ST_snoc_A/B/C は記述通り真。〔tools/mine_snocok.py〕
  次: ST_snoc_A から証明（host 標準性→cnf→セグメント兄弟 tops。host-translate と
  セグメント translate の部分項対応補題が必要）。その後 B（no-absorb=head保存+兄弟順序）、
  C（proj-olt 接尾辞再帰、E5/E6 機構の Isabelle 化）。

### ★★★(2026-06-10 続19) ins_olt_mono 発見で A/B 義務消滅 — Pred ケースは ST_snoc_C 1点に
- **ins_olt_mono（無条件！）**: olt t t' ⟹ olt (ins a b t) (ins a b t')。
  鍵: absorb が右だけ発火→右頭部が (a,b) を支配済みで olt 直出。absorb-左⟹absorb-右
  （olt_trans 経由）。absorb 両方→t vs t' = 前提。**no-absorb 条件は一切不要だった。**
- ⟹ snocok は「(C)分岐: fst p < fst q ⟶ proj-olt」只1条件に縮退。(A)新和分も
  ins_olt_mono[OF olt-Z-leaf] の直接インスタンス（yq 条件も不要）。
- nrm_snoc_seg / ST_snocok_gen / nrm_snoc / nrm_step_dec_pred 全て緑。
  条件抽出は全箇所「simp only: snocok.simps if_P/if_not_P[OF case-fact] で iff→blast/rule」
  パターンに統一（∀/∃正規化問題の根治）。
- **残: ST_snoc_C 1点**＝「標準ホスト pre@(p#rest)@[q]、rest 全支配、fst p < fst q のとき
  olt (proj (snd p) (NT rest)) (proj (snd p) (NT (rest@[q])))」。
  攻め筋: E5/E6 = proj は首最大row1接尾辞、append 列は常に接尾辞内。
  数列側の接尾辞再帰（同型の主張が suffix に降りる）＋ blockok/nfinv 事実。
- (続19補) **ST_snoc_C の証明地図**（ケース統計: no-no 12007 / fire-fire 1133 /
  ext-only 43 / **base-only 0**〔tools/mine_stc.py〕）。サイズ帰納＋4ケース:
  (i) 両不発火: proj=id 両方（proj_id）→ olt は nrm_snoc_seg の再帰（snocok rest q は
      ST_snocok_gen の相互再帰、長さ減少で整礎）から直接。
  (iii) 拡張側のみ発火: olt x x' ≤o proj x'（proj_ole）で自明。
  (iv) 基底側のみ発火: **排除可能**＝gap補題+Gterm_size+Gterm_lext_sup:
      max臨界 g >o x は g<x' だと size g > size x が必要（gap補題）だが Gterm_size で
      size g < size x: 矛盾 ⟹ g ≥o x' ⟹ partner臨界が x' を発火させる。
      **gap補題（純粋・新規）**: lext x x'（葉は Z 位置=末端挿入）⟹ x ≤o g <o x' なら
      g は x の末端拡張（size > size x）。証明: g≥x の上向き第一差分が x 内部なら
      x' も同位置で同値（葉は末端のみ差）→ g >o x' 矛盾; ∴差分は延長のみ。
  (ii) 両発火: max臨界 g_x の partner g_x' が葉を含む（=末端到達接尾辞、E5/E6 のクラス事実）
      なら (g_x, g_x') が再び lext ペア → サイズ帰納で再帰。
      必要なクラス事実 = 「標準セグメントの fire 時 max臨界は末端到達接尾辞」（E5/E6 の
      Isabelle 化）＋ maxo 選択の partner 対応（Gterm_lext_sub/sup + gap機構）。
- 必要な新部品: lext_end_gap（純粋）、maxo_partner（Gterm_lext + maxo_ub 復活）、
  末端到達性のクラス補題（ST_PS.induct or blockok 系から）。
- (続19補2) gap補題の精密化: lext（任意Z位置挿入）では gap に小型項が入り得る
  （空 arg への挿入は lex-走査の途中: g = P a (P w' Z Z) h 型の反例）。
  **正しい枠 = einc（lex-末端挿入 + 末端葉 flip）**: 実ペアでは追加列は常に
  最終ブロックの最深 tail = lex-末端 ✓。einc なら gap論法成立:
  g vs x の厳密内部解決点は x' でも同一（末端のみ差）→ g≥x ∧ g<x' は延長のみ
  → Gterm_size と矛盾 → fire 輸送 (iv) 排除。ケース(ii)の接尾辞再帰も末端性を保存。
  次セッション: einc 定義 → einc_gap → fire 輸送 → maxo_partner → 末端到達クラス事実
  （ST_PS.induct）→ ST_snoc_C 完成 → Pred ケース完了。
- (続19補3) **einc/eflip + gap補題 + fire_transport 全て緑（純粋部品完成）**:
  einc/eflip（lex-末端挿入/末端葉flip、einc_lext/eflip_lflip で lext/lflip に射影）、
  einc_gap/eflip_gap（¬olt g x ∧ olt g x' ⟹ size x ≤ size g、6ケース初等帰納）、
  Gterm_lflip_sup、**fire_transport**（einc∪eflip x x' ∧ x の fire 証人 ⟹ x' の fire 証人;
  gap+Gterm_size で証人が x' 未満に落ちないことを示し partner へ olt_trans）。
  ⟹ ST_snoc_C の (iv) ケース排除の部品が揃った。
  残部品: maxo_partner（max臨界の対応）、末端到達クラス事実、einc 版 snoc 特徴づけ、
  サイズ帰納での組立て。

### (2026-06-10 続20) 構造層の戦線分析（次キャンペーンの正確な地図）
- fire_transport/gap は einc∪eflip の**構造関係**を要求 ⟹ ST_snoc_C には
  「einc 版 snoc 構造特徴づけ」（olt 版 nrm_snoc_seg の強化）が必要で、
  そこでは absorb が許されないため **A/B 条件（snd q ≤ snd p・no-absorb 対）が復活**する。
  olt 弱化の利得は「olt 層が先に閉じた」こと（層分離）。構造層の請求書: A+B+C 級の class 事実。
- **ST_snoc_A の証明地図**:
  - single-close（q が p のブロックだけ閉じる、fst q > 親 h の row0）:
    セグメント translate が host translate の c-部分項に現れる ⟹ cnf 遺伝
    （cnf_ST_PS）から tops 非増加で snd q ≤ snd p。機械的。
  - multi-close（fst q ≤ fst h）: cnf 隣接が成立しない。blockok（row0 ステップ≤+1、
    blockok_ST_PS 済）で構成は制約されるが、排除には行1規律（row1≤row0 + 行1親）
    が必要 = P進 §2 条件(B)系の項側化。ST_PS.induct 系の新補題。
  - 実証は全 (A) 位置で違反0（mine_snocok）。
- 残キャンペーン手順: (1) einc 版グランド補題（snocokS 束 = A条件+B条件+C条件）骨格
  → (2) ST_snoc_A single-close（cnf 経由）→ (3) row1 規律補題（ST_PS.induct、
  multi-close 排除 + B の hdsub 上界）→ (4) 末端到達/max対応 → (5) ST_snoc_C 組立。
- (続20補) **nrm_snoc_str 緑（einc 構造版グランド補題、sorry-free）**: snocokS 束
  （A: snd q≤snd p / B: no-absorb対 / C: Einc on projections）の下で
  Einc (NT C) (NT (C@[q]))。(C)分岐は einc_argZ/eflip_argZ（tail=Z が all-dominated と
  正確に一致）、(A)は einc_tail[OF einc_end]、(B)は no-absorb+einc_tail/eflip_tail。
  nested-if 抽出は if_P[OF Tnil] if_P[OF qd] / if_not_P[OF qnd] の二段で。
  構造層の主装置完備: nrm_snoc_str + fire_transport + gap + maxo_ub。
  残: ST_snocokS_gen（葉義務 STS_A/B/C の class 証明）→ proj 転送 (iii)/(ii)
  → ST_snoc_C 導出。
- (続20補2) **projE 骨格 + ST_snocokS_gen 緑、ST_snoc_C は導出補題に**:
  projE（Einc の proj 転送）= ケース(i)同値・(iv)排除(fire_transport)は完証、
  (iii)/(ii) は projE_iii/projE_ii に分離（sorry）。ST_snocokS_gen の STS_C は
  「再帰 snocokS rest q → nrm_snoc_str → projE」で**導出**（葉義務から消えた!）。
  Pred ケースの決定木: nrm_step_dec_pred ⟸ nrm_snoc ⟸ ST_snocok ⟸ ST_snoc_C(導出)
  ⟸ ST_snocokS_gen ⟸ {STS_A, STS_B} + projE ⟸ {projE_iii, projE_ii}。
  **残 sorry 4点**: STS_A（兄弟tops、single-close=cnf遺伝/multi-close=行1規律）、
  STS_B（no-absorb対 = nrm の head 保存＋兄弟順序）、
  projE_iii（ext-only fire の flip 形）、projE_ii（both-fire の max対応再帰）。
- (続20補3) **残4補題の正確な照準（プローブ確定）**:
  - STS_A: 素朴形「最終列が閉じる全ブロック頭」は偽（45違反/1243）。真の形:
    (A)位置は all-dominated スパイン連鎖（頭の row0 は blockok により+1刻みで連続）の
    **fst p = fst q の要素**のみ。主張=「最終列 row1 ≤ 同 row0 スパイン列の row1」
    ＝P進 降順性級（content.md 1402、le0-切片 Br lex 非増加）。
    補題は「スパイン頭連続性」（blockok から）＋「row0揃いの row1 比較」（ST_PS.induct）に分解。
  - projE_iii: x は常に葉 D_w(0)（43/43）⟹ 補題に provenance 仮定
    （x = NT S, x' = NT(S@[q]), host 標準）を追加して projE/gen 経由で通す必要
    （現状の無仮定 sorry はおそらく一般には偽 — 証明時に書き換える）。
  - projE_ii / STS_B も同様に provenance 付きで証明する設計。
- (続20補4) segprov（provenance: pre@(pp#S)@[q]∈ST_PS ∧ all-dominated ∧ fst pp<fst q
  ∧ u=snd pp）を導入し projE_iii/projE_ii/projE に通した（緑）。
  残4 sorry は全て真な命題として確定: STS_A / STS_B / projE_iii / projE_ii。
- (続20補5) **INV 螺旋 retrofit 緑**: ST_snocokS_gen に「fst (hd C) ≤ fst q」を追加し
  stepsok（blockok の step 節の sublist 抽出、stepsok_sub）＋hd_dropWhile で螺旋を証明。
  (A)位置で fst q = fst p が**導出**され、STS_A は等式形（同 row0 の row1 比較）に確定。
  ST_snoc_C 側の起動は仮定 Q から自明。残4 sorry とも真な命題＋証明地図つき:
  STS_A（等式形・降順性級）/ STS_B / projE_iii（x葉）/ projE_ii（max対応再帰）。
- (続20補6) **STS_A 完全証明（緑）**: 等式形なら q は p ブロック直後の同レベル隣接和分
  ⟹ STS_A_aux（pre の長さ帰納、カット3分岐: 全通過/途中カット/段差カット）で
  translate_block_append ＋ cnf 節（¬ 隣接頭 olt）から snd q ≤ snd p。
  降順性の形式化は不要だった（INV 螺旋の等式化が効いた）。
  デバッグ: CNF の書換えは unfolding ベース（default simp の translate 展開回避）、
  length_induct の IH は rule_format+OF len then blast（Ball/meta 不一致回避）。
  **残 sorry 3: STS_B / projE_iii / projE_ii**。
- (続20補7) STS_B 前線分析: hdsub 節（snd h_T ≤ snd p）は h_T が deep-close
  （fst h_T < fst p、row0 の下りジャンプは blockok 非制約）の場合、セグメント translate が
  host-部分項にならず host-cnf から直接出ない。対策候補: ST_snocokS_gen に
  INV 螺旋と同型の「レベル整合（fst h_T = fst p となる経路条件）」を追加スレッディング
  →（A）同様 equality 化で cnf 隣接に帰着できる可能性。ただし (B) 連鎖の fst は
  弱降下なので等式不変式は単純には立たない — 次セッションで (B)-経路の fst 列を
  実証プロファイルしてから設計する事。
- (続20補8) **(B)-経路プロファイル: fst h_T = fst p が全9361降下で成立（drop 0件）**。
  構造証明スケッチ: 不変式 INV2「∀x∈set C. fst (hd C) ≤ fst x」が
  (C)降下（rest 全 > fst p ⟹ 新 hd = fst p+1 で再成立）と
  (B)降下（T ⊆ C ⟹ 全 ≥ fst p、T頭 ≤ fst p ⟹ 等値＋再成立）で保存、top は自明。
  ⟹ (B)位置で p と h_T は同レベル隣接和分 ⟹ STS_B の hdsub 節は STS_A_aux 型の
  cnf 隣接抽出（¬ olt 頭対 ⟹ snd h_T ≤ snd p ＋ 等号時 tr K_T ≤o tr K）で閉じる。
  さらに等号時の第2成分（tr K_T ≤o tr K）が hdarg 節の素材。
  残る真の核 = 兄弟引数の nrm∘proj 弱保存（hdarg 節と projE_ii の共通核）と
  nrm_hd（nrm が segment-translate の頭添字を保存、同帰納で同時に取れる見込み）。
  次セッション実装順: INV2 スレッディング → nrm_hd+hdsub 節 → 共通核 → projE_iii。
- (続20補9) **INV2 スレッディング緑**: ST_snocokS_gen に「∀x∈set C. fst (hd C) ≤ fst x」
  を追加、(B)位置で fst (hd T) = fst p を導出（hdTeq）し STS_B に等式仮定として渡した。
  STS_B は「同レベル隣接」前提つきに鋭化（hdsub 節は STS_A_aux 型 cnf 隣接 +
  nrm_hd（頭添字保存）で閉じる準備完了）。残 sorry 3: STS_B / projE_iii / projE_ii。
  小教訓: set (p#rest) 由来の選言は auto（simp では分解されない）、
  dropWhile の集合包含は set_dropWhileD。
- (続20補10) **収束確定: 残3補題は実質2つの核に集約**:
  (K1) クラスペア弱保存: 同レベル host-兄弟引数 K_h ≤o K_p（cnf から）に対し
       proj y (nrm (tr K_h)) ≤o proj y (nrm (tr K_p))（無逆転）。
       nrm_hd の等号ケース = STS_B hdarg 節 = projE_ii の max 対応が全てここに合流。
       注意: wf3 一般では偽（lead 不整合ペアで 72623 違反）、クラス（A_a 位置仲間）では
       実証ゼロ違反。強単調（INJ）と違い単射性は不要 — gap/fire 機構で届く可能性。
  (K2) projE_iii の葉ケース: x = D_w(0)（実証43/43）で proj u x' の flip 形。
  nrm_hd（頭添字保存）と STS_B hdsub 節は K1 が閉じれば STS_A パターンで機械的。
  次の本丸 = K1。攻め筋: olt 第一差分追跡 + fire/gap + 兄弟 cnf 事実、
  逆転には proj ジャンプの交差が必要でクラスでは gap 補題系が遮断する見込み。

### ★★(2026-06-10 続21) proj_once 定理 — 射影は1ステップで終わる（K1 純粋部品完成）
- **兄弟ペア実証**: 全4696ペアで「等しい(3681) or 和のprefix切詰め(1015)」のみ
  （sub差分・arg再帰ゼロ）= コピー系譜の構造。proj レベルでも同分類・真の逆転ゼロ。
- **proj_once（純粋定理・緑）**: max臨界は自分が発火しない（violator g ∈ G(m) ⊆ G(b)
  が Gterm_trans で持ち上がり、最大性 maxo_ub と size で矛盾）⟹
  proj u b = if fire then maxG(b) else b。**1ステップ確定**。
- **proj_submono（純粋・緑）**: Gterm u x ⊆ Gterm u y ∧ ole x y (∧ fire移送) ⟹
  ole (proj u x) (proj u y)。prefix-和（兄弟ペアの実形）は G-部分集合 ✓ なので
  K1 の proj 部分はこれで閉じる。クラス事実は「兄弟 nrm 像が prefix-和」のみに縮小。
- projE_ii も proj_once により「max臨界対応の有限推論」に縮退（再帰不要の見込み）。
- デバッグ: pfire/proj_nofire の定義位置（未定義だと自由変数として黙ってパースされ
  obtain が "Failed to apply initial proof method" になる）、blast+trans 連鎖は hang。

### ★★★(2026-06-10 続22) E6 マスター補題発見 — projE 攻略の決定版アーキテクチャ
- **E6 接尾辞定理（実証 15302/15302 + クラス 9918 セグメントで 0 違反）**:
  クラス = segprov 型支配セグメント (pp,S)（∃pre post. pre@(pp#S)@post ∈ ST_PS、
  S 全支配、u = snd pp。S 側 post=[q] と SQ 側 post=[] の両方）に対し
  - **(C1) nrm_hd**: NT S の頭添字 = snd (hd S)、spine 上で ins 吸収ゼロ (V1=0)
  - **(C2) fire 判定**: pfire u (NT S) ⟺ msfx S ≠ S ∧ vis u S ∧ olt (NT S) (NT (msfx S))
    （ホスト u 限定！任意 u では 930 違反 V3。使用箇所は全てホスト u なので OK）
  - **(C5) proj 値**: fire ⟹ proj u (NT S) = NT (msfx S)
  ここで msfx S = dropWhile (λc. snd c < maxr1 S) S（最初の max-row1 列からの接尾辞）、
  vis u S = 翻訳再帰で j0 の先祖列 row1 が全て ≥ u（再帰定義: 頭が max なら True /
  max が K 内なら snd c0 ≥ u ∧ vis u K / max が T 内（厳密に大）なら vis u T）。
- **projE_ii の還元**（both-fire 1133 = same-cut 1128 + q-cut 5）:
  - same-cut (snd q ≤ maxr1 S): msfx(S@[q]) = msfx S @ [q]（100%）⟹ 結論は
    **T = msfx S への snoc 命題 Einc (NT T) (NT (T@[q]))** — 長さ |T| ≤ |S| < |C| の
    強帰納で snoc グランド補題に再帰（循環なし！）
  - q-cut (snd q > maxr1 S): V4=0 より msfx S = [S最終列] ⟹ proj 両辺とも葉、
    eflip (maxr1 S < snd q)。純粋。
- **projE_iii の還元** (V5=0): S 単元 or msfx S = S。snd q > maxr1 S なら eflip 葉対、
  snd q ≤ なら msfx S = S で結論 = R 前提そのもの。fire 排除は C2 の ⟸ 向きで。
- mx'-パートナー実証 (mine_pe2): both-fire 全1133で rel(mx,mx') ∈ {einc 1042, eflip 91}、
  eq ゼロ、mx' は常に mx のパートナー (Q3=0)。projE_iii は全43で eflip (Q4)。
- **次キャンペーン**: nrmstep.thy に maxr1/msfx/vis 定義 + 純粋列補題（msfx append 法則
  ・msfx ≠ []・hd msfx の snd = maxr1）→ マスター補題を長さ強帰納で（C1+C2+C5 ＋
  必要なら C3 兄弟弱保存を連言に）。cnf_ST_PS の頭支配を nrm レベルに移送する箇所が核。
- ツール: tools/mine_pe2.py (パートナー対応), mine_fire{2,3,4,5}.py (判定式の探索),
  mine_master.py (最終検証スイート V1-V5)。

### ★★(2026-06-10 続23) E6_value 帰納の設計確定 — base対のみで閉じる
- **クラスの正解 = base 対のみ**: (u,S) = (snd pp, pp直後の隣接支配ラン＋右切詰任意)。
  mine_master3: base 8351対で C1/C2/C5 全て 0 違反。降下T対の標準単独 E6 は不成立
  （99/127 失敗）だが、それは閾値が NT T でなく NT S_full であるべき統計混入 —
  帰納では T 部の臨界は「閾値 NT S_full 上の violator」としてのみ扱うので不要。
  任意ピース（mid 森境界条件付き）は C1 のみ 0（吸収なしは広く成立）。
- **境界横断なし定理（実証 930/930）**: fire 時、j0 の全先祖のランは S 末尾まで延びる
  ⟹ NT(msfx S) = 最深先祖 c_d の arg = proj (snd c_d) (NT (run c_d)) =（IH・隣接base対）
  NT(msfx(run c_d)) = NT(S[j0:])。msfx S は単木 921 / 複木 9（どちらも値は同じ機構）。
- **G1 (membership)**: vis u S の先祖 row1 ≥ u 条件が Gterm の可視鎖にそのまま対応。
- **G2 (dominance)**: violator g は全て「クラス部分セグメントの NT 像」(G-カタログ)。
  hd 添字 < m なら即 olt。= m なら S[j0:] の右切詰 prefix との比較
  ⟹ **内部位置版 snoc 単調性が必要 = ST_snocokS_gen / STS_A / nrm_snoc の post 一般化**
  （現行は host 末尾 q 限定。premise を pre@C@[q]@post ∈ ST_PS に広げる外科手術）。
- **G3 (completeness)**: fire ⟹ criterion。violator 存在 ⟹ その由来セグメントの
  hd row1 ≥ ... ⟹ msfx ≠ S ∧ vis ∧ olt。G2 と同じカタログで。
- **次の手順**: (1) snoc 機構の post 一般化（機械的見込み、STS_A の
  translate_block_append 部のみ要注意）(2) G-カタログ補題 (3) E6_value 長さ帰納本体。
- ツール: tools/mine_master2.py (ピース族), mine_master3.py (降下閉包), mine_nbc.py (境界横断なし)。

### ★★(2026-06-10 続24) C1層完成 — NT_dom が NT_tie（SIB核）1点に縮小
- **drop=0 定理（実証1455/1455 → 純粋証明完了）**: fbseg 閉包で和-隣接ペアは常に同レベル。
  理由: blockok ステップ≤+1 ⟹ 支配ランの最初の列 = fst pp + 1、森境界条件で
  piece 先頭も fst pp+1 に固定、c1 は支配で挟み撃ち ⟹ **fst c1 = fst c**〔fbseg_hd_level 緑〕。
- **C1層の依存鎖（全て緑）**: NT_tie(sorry) → NT_dom → NT_shape（長さ帰納+ins展開）→
  NT_hd / NT_tail_lt（和尾部厳密増大; ABeq ケースは IH再帰）。
  部品: NT_noabsorb（吸収⟹サイズ矛盾）、fbseg_pair_host（ホスト隣接抽出）、
  NT_dom_sub_eq（STS_A直結の添字バウンド）、stepsok 群を前方移動。
- **NT_tie**: fbseg ∧ T=c1#rest1 ∧ snd c1 = snd c ⟹ ¬ olt (proj (snd c) (NT K)) (proj (snd c1) (NT K1))。
  タイ1037件で違反0。= K1/SIB の正規形。攻め筋: E6で proj=NT(msfx)化 → セグメント比較
  → snoc単調(nrm_snoc_int)+host cnf。STS_B hdarg 節と同核なので一方が閉じれば両方閉じる。
- 現 sorry: nrmstep = NT_tie/E6_value/E6_qcut_last/E6_iii_singleton/E6_seam/STS_B (6)、
  nrm = nrm_order_pres (1)。ツール: tools/mine_ntdom.py。

- (続24補) **E6_value dominance の純粋半分が完成（全て緑・クラス前提なし）**:
  subs連鎖 Gterm_subs/proj_subs/ins_subs/nrm_subs/NT_subs + ins_neZ/ins_hdsub/NT_neZ/NT_hd_ge
  ⟹ **NT_msfx_hdsub**: hdsub (NT (msfx S)) = maxr1 S（吸収があっても頭添字は上がるだけ、
  subs で上から押さえる — fbseg 不要！）⟹ Gterm_NT_hdsub_le（臨界の頭添字 ≤ maxr1）
  + olt_msfx_lowsub（頭添字 < maxr1 ⟹ 即 olt NT(msfx)）。
  **DOM の残り = 頭添字 = maxr1 のタイのみ**（カタログ + 最初max優先の組合せ論）。
  MEM（NT(msfx S) ∈ Gterm の可視鎖）が次の骨格。

- (続24補2) **E6_value 本体証明完了（コンビネータ化・緑）**: proj_once + maxo_ub +
  E6_mem(sorry: msfx像∈Gterm∧violator) + E6_dom_tie(sorry: 添字タイ violator ≤ msfx像)
  + 低添字側は olt_msfx_lowsub で純粋に閉じる。
  sorry 前線 = 全て配列レベルの葉クラス事実 7点: NT_tie / E6_mem / E6_dom_tie /
  E6_qcut_last / E6_iii_singleton / E6_seam / STS_B（+ nrm_order_pres）。
  構造コンビネータ（E6_value・NT_dom→NT_shape 鎖・ST_snocokS_gen 配線）は全て証明済。

### (2026-06-10 続25) 残7 sorry の収束構造 — HDOM/GCAT 設計
- **NT_prefix_lt 緑**（nrm_snoc_int の連鎖、C@D@post∈ST_PS ⟹ NT C <o NT(C@D)）。
- 残る組合せ核の還元図:
  - **GCAT（G-カタログ）**: class S の臨界 = 可視ノード n の arg 群、arg(n) =
    proj (snd n) (NT (run_n∩S)) =（E6/IH）NT(run_n) or NT(msfx(run_n)) — 常に
    「S の連続部分セグメントの NT 像」+ Z。帰納で機械的の見込み。
  - **DOM-tie（E6_dom_tie）**: タイ violator g = NT(piece)、hdsub=maxr1=m ⟹
    piece は m-列開始、開始位置 l ≥ j0（j0=global first max）。
    l = j0: piece は msfx S の prefix ⟹ **NT_prefix_lt で閉じる**。
    l > j0: 再帰的 first-max 優先（msfx S の arg との比較に降下）。
  - **HDOM（頭max支配）**: maxr1 R = snd (hd R)（先頭が max）⟹ 全臨界 g: olt g (NT R)。
    = C2 の no-fire 向き = E6_mem の j0=0 ケース排除 = タイ比較の底。
    NT_tie / STS_B hdarg 節も同じ底に合流。
  - **E6_mem**: fire ⟹（HDOM 対偶で）msfx S ≠ S、先祖鎖（nbc 930/930）で
    NT(msfx S) = 最深可視先祖の arg ∈ Gterm（E6/IH を run で使う再帰）。
- 帰納の正しい束: 長さ強帰納で {HDOM, GCAT, E6_mem, E6_dom_tie}（E6_value は証明済
  コンビネータ）。NT_tie は HDOM+E6 値の系になる見込み。E6_seam/qcut/iii は行レベル。

- (続25補) **GCAT 緑（G-カタログ・u一様・130行帰納が一発）**: fbseg閉包 S の臨界は
  Z または「S の連続部分片 C の NT 像で hdsub g = snd (hd C)」。
  鍵: NT_shape の結論が u 非依存 → GCAT を ∃v.fbseg v S で述べる / msfx-片の再帰は
  proj_fire_in + Gterm_mono(u≤y0) + Gterm_trans で K-再帰に吸収（msfx片の fbseg 不成立を回避）。
  補助: proj_fire_in / fbseg_K_dseg / Gterm_mono 緑。
  ⚠️ 注意: GCAT は E6_value（sorry依存コンビネータ）を K(短い)に使用。最終組立時は
  {GCAT, E6_mem, E6_dom_tie, E6_value} を長さ同時帰納に**インライン統合**が必要
  （同長で GCAT(n)→mem/dom(n)→value(n) の層順・短い側だけ value を呼ぶ⟹非循環）。

- (続25補2) **E6_dom_tie_resolved 緑**: GCAT で violator g = NT(Cp)（Cp は S の連続片、
  頭が m-列）に分解 → 開始位置 l ≥ j0（takeWhile_nth 論法）→
  l = j0: msfx S = Cp@post' で NT_prefix_lt（post'≠[]）/ refl（=[]）→ 閉じる。
  l > j0: E6_dom_deep（新 sorry、first-max 優先の再帰核）。
- **補題レベル循環の顕在化と扱い**: NT_prefix_lt → ST_snocokS_gen → E6_value →
  E6_dom_tie が循環。長さで層化すると 値(n-1) → snocok(n) → prefix_lt(n) →
  dom_tie(n) → 値(n) の層順で非循環 ⟹ 最終組立は1本の同時長さ帰納にインライン。
  当面: E6_dom_tie は sorry スタブのまま、resolved 版を NT_prefix_lt 後方に配置。
- デバッグ: metis(hd_Cons_tl/set_takeWhileD) が 1800s 暴走 → 明示 obtain/blast 化。
  unfolding の順序で msfx S の書き換え不発 → calc 連鎖（drop j0 経由）。

- (続25補3) **E6_hdom 緑（排除コアの統合）**: 頭最大クラスセグメントは無発火。
  GCAT分解 → 低添字: NT_hd の P m 形と添字比較で即 olt / タイ+prefix: NT_prefix_lt /
  タイ+後続片: **E6_lpl**（新 sorry: 後続同添字ピースは全体に負ける = first-max優先の対偶側）。
  E6_dom_tie_resolved と同パターン。実効コアは {E6_lpl, E6_dom_deep, E6_mem連鎖, NT_tie}
  + 行レベル {qcut, iii, seam} + STS_B に整理された。
  E6_lpl と E6_dom_deep は双対（前者: 全体vs後続片、後者: msfx vs後続片）— 統一可能性あり。

- (続25補4) **健全性キャッチ＆修正（重要）**: E6_lpl / E6_dom_deep の旧文面
  （任意の m-頭ピース C）は**偽** — 実ホスト dseg 頭最大対で逆転2163件
  （例: S=(3,1)(4,0)(5,1)(6,1), C=(5,1)(6,1)。C は u=1 では Gterm 不可視 =
  GCAT 到達不能片）。**可視性前提 NT C ∈ Gterm u (NT S) を両補題に追加**して修正
  （hdom/dom_tie の呼び出し側は G をそのまま供給）。教訓: sorry クラス事実は
  文面確定時に必ず「使用側が供給できる前提だけで」最弱化マイニングする。
  弱クラス LPL は等値も475件（吸収で NT C = NT S）→ hdom 側はサイズ論法で排除済。

- (続25補5) **E6_mem_resolved 緑（3コンビネータ完成）**: 頭max → E6_hdom 排除 /
  m-in-K → E6_nbcK(sorry: T=[]∧可視∧K発火) + E6_value(K) + 純粋部品で完全組立 /
  m-in-T → E6_memT(sorry: 尾部への membership/violator 移送) + msfx_tail。
  Max_mono 系は nonempty を use で明示供給（xs ファクト混入で auto 迷走する）。
  imageE 系 obtain は force。最終 show は meq/sub を介して m1/m2 に分解。
  実効 sorry コア: E6_lpl / E6_dom_deep / E6_nbcK / E6_memT / NT_tie（+行レベル3+STS_B）。
  全コンビネータ・カタログ・排除パターンが証明済みなので、残コアは全て
  「スパイン/ラン上の first-max 優先」という単一テーマの変種。

- (続25補6) **E6_nbcK の文面確定（診断マイニング3本で締め直し・緑）**:
  m-in-K fire 930件の構造 = (i) 全て u ≤ snd c0（u > y0 なら根 row1 非増加で
  Gterm 空 = 純粋に証明可能な見込み）(ii) u≤y0 ∧ m-in-K ∧ T≠[] の配置は **0件**
  （T=[] は自動）(iii) K発火は 219/930 のみ、無発火 711 件は**全て msfx K = K**
  ⟹ 第3連言を「pfire ∨ msfx K = K」に弱め、Aval は case 分割（無発火側は
  proj_nofire で自明）。E6_mem_resolved 再緑。
  旧形（K発火必須）は偽だった — sorry 文面の使用前検証ルールがまた効いた。

- (続25補7) **Gterm_NT_high 緑**（u > 頭row1 ⟹ 臨界空；根row1非増加=NT_dom由来）
  ⟹ **E6_nbcK の可視性連言（u ≤ snd c0）が証明済に**。E6_nbcK = nbcK_T(sorry:
  u≤y0∧m-in-K⟹T=[]、配置0件の行レベル事実) + nbcK_K(sorry: K発火∨msfx K=K) に分解。

### (2026-06-11 続26) r1ok 発見 — row1 規律（行レベル事実群の土台）
- **実証 14,558 列で 0 違反**: 標準 M の fst>0 の全列 j に row0-親
  （最後の k<j で fst k = fst j - 1、間に fst < fst j - 1 なし）が存在し、
  **snd (M!j) ≤ snd(親) + 1**。差分分布 {-3:3, -2:313, -1:3306, 0:5754, +1:5182}。
- r1ok は blockok_ST_PS と同様に ST_PS 生成帰納で証明する（未実装）。
  これで nbcK_T / E6_qcut_last / E6_iii_singleton / E6_seam の行レベル4点を
  arithmetic 化する計画。残りの再帰束 {E6_lpl, E6_dom_deep, E6_memT, NT_tie,
  nbcK_K} は GRAND 同時帰納（スパイン歩き＋閾値付き MEM/DOM）で締める。

- (続26補) r1ok キャンペーン開始: 定義＋生成帰納骨格＋diag ケース＋
  r1ok_take/r1ok_butlast 緑（oper 保存のみ sorry）。
  **oper 構造の重要事実**: idx1 ∈ {0,1} なので **d1 = 0 恒等**（row1 は常に正確コピー、
  d1 増分は発生しない）。bad分岐 = take j0 M @ concat(copies)、copy k は
  [j0..<j1] を (row0 +k*d0, row1 そのまま) でシフト。i1=0 なら d0=1（row0親）、
  i1=1 なら d0 = e0 j1 - e0 j0 任意。r1ok_oper の親対応: プレフィクス内✓(take)、
  コピー内＝元の親関係の平行移動、コピー境界＝climb補題（blockok: j0→j1 の
  ≤+1 ステップで中間レベル全訪問）で前コピー内の d0-1 レベル列が親。

- (続26補2) **r1ok_oper_bad の証明レシピ確定（マイニング2本・全数一致）**:
  親所在は3種のみ {same-copy 18665, prev-copy 2187, prefix}（other 0/26155）。
  コピー列 (k,q) の証人選択:
  - k=0: 恒等領域（take j1 M = M の接頭辞そのまま）→ r1ok M の証人 ✓純粋
  - k≥1 ∧ 元親 p ≥ j0: same-copy 平行移動 ✓純粋（行0シフト・行1不変）
  - k≥1 ∧ p < j0: tgt = e0(q)+d0-1, cands = {r<L. e0(j0+r) ≤ tgt}:
    - cands={}（d0=0のみ可能）: 証人 = p（コピー全段 ≥ e0(q) で no-dip）✓純粋
    - cands≠{}: 証人 = copy k-1 の max-cands 位置。検証: e0=tgt 丁度 2187/2187・
      no-dip 構成的・**row1バウンド e1(q) ≤ e1(r')+1 が 2187/2187**（r'≥q 常成立、
      r'=q 1203 / r'>q 984）→ この row1 バウンドだけ新クラス事実 **r1ok_climb**。
  - 簿記部品: concat(map blk [0..<n]) の nth/length 補題（k*L+q アクセス）が必要。
  - i1=0 ⟹ d0=0（正確コピー）/ i1=1 ⟹ d0任意≥1, le0_interval_gt でブロック内 > e0 j0。

- (続26補3) **r1ok_oper_bad 主証明緑（一発）**: i<j0 転送 / k=0 恒等領域 /
  k≥1∧¬PM（同コピー平行移動、p≥j0 は no-dip と ¬PM の矛盾から）の3ケース純粋完了。
  残 = r1ok_copy_witness（k≥1∧PM: max-cands 証人、行1バウンド=r1ok_climb 相当）1点。
  div/mod 分解は less_mult_imp_div_less + mult.commute。k=0 の idl は ldec subst。

- (続26補4) **r1ok_copy_witness 緑** — r1ok_ST_PS は r1ok_climb 1点に収束。
  cands空(d0=0)=prefix親転送・純粋 / cands非空= Max証人: rexact（o2: Max+1段step、
  r'=L-1端は PM(r=0含む q=0は自明) + nextrel0/1 の e0関係で閉）・no-dip（above+PM）・
  f1（mult_eq_if で k分配）全て純粋。行1バウンドのみ r1ok_climb。
  デバッグ: nat減算の e0=0退化（pos供給）、∀インスタンス化の Suc正規形（blast）、
  乗法キャンセル（ccontr+mult_le_mono1）。

- (続26補5) **r1ok_climb の機構マイニング**: PM∧cands≠{} 全729配置で
  **e1(q) - e1(r') ∈ {-3,-2,-1,0}** — 正側ゼロ（必要な ≤+1 より強く e1(q) ≤ e1(r')）。
  last-visit 連鎖 w_ℓ（レベルℓの最終訪問列）は w_{ℓ+1} > w_ℓ かつ
  w_{ℓ+1} の r1親 = w_ℓ（純粋: w_ℓ 後は全列 > ℓ ＋ step≤+1 で ℓ+1 訪問存在）— ただし
  r1ok は上界のみ与え e1 の下界（落ちない側）は別機構（maxsub/cnf 系 = nfinv の
  subscript 単調降下?）が必要。r1ok_climb は scoped sorry として残し translate 側から攻める。
- **q-cut の r1ok 帰結（E6_qcut_last 攻略の鍵）**: snd q > maxr1 S ⟹ r1ok で
  snd q ≤ snd(親)+1 ≤ maxr1+1 ⟹ **snd q = maxr1 S + 1 ∧ q の r1親は m-行1列**。

### ★★(2026-06-11 続27) SIB_prefix 発見 — NT_tie の配列レベル還元
- **実証（fbseg閉包の隣接同レベル兄弟対）**: snd-タイ（snd c1 = snd c）では
  **K1 = K（1418）∨ K1 ⊏ K（真接頭辞・650）のみ。K⊏K1 と other は 0/2068**。
  （タイなし全体では K-prefix-of-K1 482 / other 30 もあり — タイが形を強制する）
- **NT_tie 導出経路**: SIB_prefix(新クラス事実) ⟹
  K1=K: proj 同値で ¬olt ✓ / K1⊏K: 4象限 {proj=NT or NT∘msfx}×2 を
  NT_prefix_lt（K1 は K の接頭辞＝ホスト内連続）+ msfx-prefix 関係 + fire 整合で比較。
  proj_submono 経由なら Gterm-部分集合が要るが、E6_value 直比較なら不要の見込み。
- これで STS_B hdarg 節も同経路。SIB_prefix 自体は oper のコピー構造から
  生成帰納で出る見込み（コピー＝同一素材の反復、兄弟ラン＝コピー切り詰め）。

- (続27補) **NT_tie_resolved 緑**: SIB_prefix（equal/prefix+両無発火）から
  equal→irrefl / prefix→proj恒等+NT_prefix_lt / K1=[]→not_olt_Z で完全導出。
  **SIB核は順序論ゼロの配列形状事実 SIB_prefix に還元**（生成不変量として
  r1ok_oper と同パターンで証明可能見込み）。STS_B hdarg 節も同経路で閉じる見込み。

- (続27補2) **E6_seam の構造確定（796件）**: INV側 fst q - fst(hd msfx S) ∈ {0..9}
  （常に ≥0 ✓）、INV2側 msfx S の森 = 単木 790 / 同レベル複木 6 / **other 0**
  ⟹ E6_seam ⟸ (s1) fst(hd msfx S) ≤ fst q ＋ (s2) hd が最小レベル（fire構造帰結）。
- 次キャンペーン最優先 = **SIB_prefix の生成不変量化**（r1ok_oper と同パターン:
  diag では兄弟ランなし/全同形、oper コピーは同一素材反復＝prefix 切詰のみ生成）。
  閉じると NT_tie 完了・STS_B hdarg 節も同経路。次いで nbcK_T/K・memT・lpl/dom_deep
  （これらは fire-cascade 系で GRAND 同時帰納の本丸）。

- (続27補3) **SIB_prefix → SIB_shape 還元完了（緑）**: 無発火連言は導出可能
  （prefix-タイ対は両ラン頭最大 650/650 → E6_hdom 経由で無発火）。
  SIB_shape = 「タイ兄弟ラン K1 ∈ {K, 真prefix} ∧ prefix時両頭最大」の
  純粋配列形状事実のみ。NT_tie_resolved は E6_hdom+NT_prefix_lt+proj_nofire で再証明。
  教訓: obtain した ⟶ は [OF] 不可（blast で）。

- (続27補4) **次の構造リフト課題（STS_B 攻略の前提）**: C1鎖（NT_shape/NT_dom等）は
  fbseg（被支配文脈）上に構築したが、ST_snocokS_gen の入口 C = p#rest は
  **トップレベル（fst p = 0、支配 pp なし）があり得る** → fbseg 不成立。
  対処案: fbseg を深さパラメータ付きに一般化（仮想ルート d=-1 相当;
  blockok の hd=0 と steps から「根は全てレベル0」が fbseg_hd_level の類似で出る）
  → C1鎖をパラメトリックに再証明（ほぼ機械的な premise 差し替え見込み）。
  これで STS_B の hdsub 節 = NT_hd、hdarg 節 = NT_tie_resolved 同経路が開通する。

- (続27補5) **トップレベル訂正（重要）**: レベル0の兄弟木対（全根 (0,0)、474対）では
  SIB_shape 不成立 — equal 276 / prefix 171 / **other 27**（例: K=(1,0)(2,0) vs
  K1=(1,0)(1,0)、row0 デクリメント形）。トップ木は copy-切詰めでなく
  「展開段階」列なので、STS_B の hdarg 節はトップでは cnf 降下の nrm 移送
  （レベル0限定の弱保存）が必要。被支配レベル（fbseg）では SIB_shape 経路有効。
  ⟹ STS_B = fbseg 側（SIB経路）+ トップ側（別機構）の2層。27例の正確な形
  （suffix の段階降下?）は次セッションでマイニング。

- (続27補6) **TOP_desc 確定**: トップレベル隣接 (0,0)-木対は NT_tie 成立 0/474 違反、
  other 27例も含め **ole (NT K1) (NT K) が nrm レベルで直接成立（27/27）**。
  ⟹ トップ層の統一クラス事実 = TOP_desc（隣接トップ木の nrm 弱降下、474対0違反）。
  STS_B 完成形 = NT_hd のトップ版（C1 リフト）+ TOP_desc + 被支配層 SIB_shape 経路。
  TOP_desc は展開段階構造（m_step/oper 機構）から攻める。

- (続27補7) **fbsegD 追加（緑・追加的変更のみ）**: 深さ統一クラス
  「fbsegD S = ホスト埋め込み ∧ mid/S とも fst (hd S) が下界」。
  fbseg_fbsegD（blockok step で fst hd S = pp+1 を内部導出）と
  fbsegD_hd_level（レベル固定が定義から自由）✓。
  次段（C1鎖の premise を fbsegD に差し替え + NT_tieD = SIB_shape/TOP_desc 2層）は
  次セッションで（既存は無変更のまま緑維持）。

### ★(2026-06-11 続28) SIBM 確定 — SIB_shape の生成不変量（実装準備完了）
- **SIBM（Mレベル・実証2964対）**: 標準 M の隣接タイ兄弟対（level>0）は
  run equal（2405）/真prefix（559）/other **0**、かつ**全ケースで両ラン頭最大**
  （equal でも 2964/2964）⟹ ピース切詰め安定性が完全（truncated K1 は
  prefix-of-K のまま、頭同じで max は下がるだけ → 頭最大保存）。
- **SIB_shape ⟸ SIBM + 純粋切詰め簿記**。SIBM の oper 保存:
  d1=0（row1正確コピー）で頭最大保存✓、d0>0 ならコピー境界に新タイ対なし
  （レベル不一致）、d0=0 なら境界対は equal ✓、j1-cut の prefix 切詰めも閉形。
  r1ok_oper と同じ簿記パターンで実装可能（diag: 兄弟ランなし）。
- 実装順: SIBM def → SIBM_diag → SIBM_oper（コピー簿記・oper_bad_nth 流用）→
  SIBM_ST_PS → SIB_shape を SIBM+切詰めから導出 → NT_tie 完全閉鎖。

- (続28補) sibm 骨格緑（def+diag+ST_PS帰納、残 sibm_oper のみ）。
  デバッグ: diagSeq 記号下で simp の moreover/ultimately 連鎖がスタック溢れ
  （Interrupt_Breakdown）→ e1/e2 を rule で取り unfolding で消してから simp。
  次: sibm_oper（oper_bad_nth 流用のコピー簿記）→ SIB_shape を sibm+切詰めから導出。

- (続28補2) **SIB_shape 完全証明（sibm 導出・緑）**: ホスト位置簿記
  （ic/b の nth_append_length・drop=append_eq_conv_conj・mrun=takeWhile_append1/2 分岐）
  + 切詰め安定（K=mrun ic 完全一致＝c1 が止める／K1 は mrun b の prefix、
  頭最大は Max_mono で継承）。SIB系: sibm_oper(sorry) → sibm_ST_PS → SIB_shape
  → NT_tie_resolved の鎖が完成。sibm_oper は r1ok_oper と同型のコピー簿記。

- (続28補3) sibm_take/sibm_butlast（切詰め安定・takeWhile_take_comm 自作）+
  sibm_oper ケース骨格 緑。SIB鎖の残 = **sibm_oper_bad**（コピー簿記、
  r1ok_oper_bad と同型: 同コピー内対=平行移動・コピー境界対=d0>0ならレベル不一致で
  対なし/d0=0なら equal・j1-cut切詰め= sibm_take 流用）のみ。
  ⚠️ 変数 P は three コンストラクタと衝突（Q を使う）。

- (続28補4) **sibm_oper_bad の証明地図（対カテゴリ実証）**: タイ対は4族のみ
  {PP 1472, PC 482, CC同コピー 5655, CC隣接コピー 2475}、CC+2 以遠 **0**。
  - PP: 両者 prefix 内。a のランは prefix 内で閉じる（b<j0）＝ M と同一。
    b のランはコピー域へ延び得る → copy0 = M ブロック恒等 + j1-cut/次コピー接続の場合分け。
  - PC: a の ランが j0 を跨ぐ（最富ケース）。
  - CC同: M 対の平行移動（レベル同シフト・row1 不変、ブロック端切詰めは sibm_take 流）。
  - CC隣: d0>0 でも存在（e0(qb) = e0(qa) - d0 の組合せ）。
  規模 300行級・新セッション推奨。部品は oper_bad_nth/concat簿記/sibm_take 全て流用可。

### ★★(2026-06-11 続29) 【重大訂正】sibm は ST_PS 上で偽 — 修正版 sibm2 (4族) 確定
- **反例**: M=(0,0)(1,1)(2,0)(3,0)(4,0)(2,0)(3,0)(4,0)∈ST_PS, X=oper(M,2)
  =...(2,0)(3,0)(3,0)。X の対 (a=2,b=5)=(2,0)タイ: K=(3,0)(4,0), K1=(3,0)(3,0)
  — equal でも prefix でもない。**SIB_shape も同データで偽**（X 自身を host,
  pp=(1,1), mid=[] の fbseg 窓で前提成立）。続27-28 の SIB 解体は偽前提だった。
- **原因＝閉包境界アーティファクト**: 旧マイニングは enum_ST の集合内の M しか
  検査せず、最終ラウンドの M に oper を当てた X を見ていなかった。違反は閉包の
  1歩先で初出。**教訓: マイナーは必ず「閉包+1段」（全 M×全 n の oper(M,n) を
  検査対象に追加）で回す**。他の 0違反実証（fire-cascade 系・TOP_desc 等）も
  閉包+1 で再検証が必要（→続29補で実施）。
- **修正版 sibm2（0/26235対, 閉包+1, mine_sibm5.py）**: 隣接タイ兄弟対の
  K=mrun a, K1=mrun b は次の4族のみ＋両ラン頭最大:
  (E) K1=K / (P) K1 真接頭辞 / (F1) 第一差分 t=0: fst同・snd K[0]>snd K1[0]
  / (F2) 第一差分 t≥1: fst K[t]>fst K1[t]。
  逆向き（K が K1 の真接頭辞・第一差分上昇）は 0。
  = **K1 ≤ K の列 lex 弱降下**（柱3 seqlex と同じ向き）。
  F1/F2 は **b のランが open（M終端切詰め）のときのみ** 発生（closed では E/P のみ）。
  F1 は常に t=0（両頭は fst c+1 で同レベルだから）、F2 は常に t≥1。
- **NT_tie は生存**: 全 fbseg 窓×閉包+1 で 0/1486 (mine_sibm4.py)。値側機構:
  全 F1/F2 ケースで olt(NT K1, NT K) **厳密**成立・両者無発火（頭最大⟹msfx=self）。
  修正導出: (E) 同項 irrefl / (P) NT_prefix_lt / (F1) 頭添字 y>y1 の P項直接比較
  / (F2) **NT_firstdiff_lt（新値補題: 共通接頭辞+レベル降下第一差分 ⟹ 厳密 olt）**。
- 残作業更新: sibm→sibm2 へ Isabelle 改修（def/diag/take/oper骨格/oper_bad sorry
  ステート修正・SIB_shape→SIB_shape2 4族版・NT_tie_resolved 4ケース化）、
  NT_firstdiff_lt 新設、sibm2_oper_bad 手術（真の文面になった）。

- (続29補) **Isabelle 改修完了（緑20s・コミット 60e581c）**: sibrel（E∨P∨hm²∧lexdiff{F1,F2}）
  + sibm2 + hm_take/sibrel_trunc（切詰め安定が一般補題化、旧版の E→P-hm欠落問題は
  「P に hm を要求しない」設計で消滅）+ sibm2_take/butlast/oper骨格/ST_PS +
  SIB_shape2（結論=sibrel・旧 hm 簿記は sibrel_trunc に吸収され簡素化）+
  fbseg_run_hd_level（ラン頭レベル= fst c + 1・stepsok簿記）+
  NT_tie_resolved 3ケース版。新 sorry: sibm2_oper_bad（真文面）/
  E6_tie_nofire0/1（¬hm タイランは無発火・実証3027窓全無発火）/
  NT_lexdiff_lt（dseg²+hm²+頭レベル同+LF1∨LF2 ⟹ 厳密 olt・実証116万対0失敗）。
  計17 sorry（nrmstep 16+nrm 1）、全て実証済文面。
- (続29補2) 検証ツール: mine_sibm2/3/4/5.py（run地理・窓カタログ・M レベル4族）、
  mine_lexdiff.py（合成クラスは cnf 規律欠落で広すぎ偽→実 dseg 対で真）、
  audit_plus1.py（既存マイナーの enum_ST を閉包+1 にパッチして一括再監査）。
  PC対は b=copy0頭のみ・CC+1 は d0=0 頭々のみ・CC+2 以遠ゼロ（oper_bad 設計用）。

- (続29補3) **正確文面の閉包+1監査完了（audit_exact.py）**:
  E6_lpl 0/150929 ✓ / E6_dom_deep 0/182584 ✓ / E6_nbcK_T 0/27729 ✓ /
  E6_nbcK_K 0/20942 ✓ / r1ok_climb 0/3513 ✓ / 旧マイナー群（seam/nbc/fire5/
  master V1V2V4V5/ntdom）も閉包+1 全0 ✓（audit_plus1.log）。
  **STS_B は前提不足で偽（22524/49490違反）→ INV (fst p ≤ fst q)・
  INV2 (∀x∈rest. fst p ≤ fst x) を前提追加で 0/26322 ✓**（使用箇所は両方常在、
  呼び出しも修正、緑）。
  **E6_memT は前提がクラス上空**（dseg+T≠[] で max-in-tail は 0/14638、fire 不要）
  — 空虚に真。後で「maxr1(c0#K) = maxr1 S (T≠[]時)」の純粋事実から前提矛盾で討伐可。

- (続29補4) **sibm2_oper_bad = n帰納×シーム補題 sibm2_snoc_copy に再構成（緑）**。
  シーム（Y = take j0 M @ copies[0..<m] → Y @ C, C = copy m）の対分類と討伐地図:
  - **I-closed**: 対(a,b)が Y 内・mrun Y b 閉 → run は append で不変
    （takeWhile_append1）→ IH sibm2 Y から sibrel そのまま。純粋・易。
  - **I-open**: mrun Y b 開（Y終端まで）→ Y' で E = takeWhile(>lev b) C だけ延長。
    sibrel K (K1@E) が必要 = **残る本丸（周期性/整列算術）**。
    家族の変化: E-open は延長空が必要（lev b ≥ hd C レベル）等、位置・レベル事実で処理。
  - **II-int**: 両端 C 内 → C = block の m·d0 シフト ＝ take j1 M の接尾辞と
    run 構造が同型（シフトは fst 比較を保存）→ sibm2_take[OF R] から転送。
    シフト対応簿記（mrun_shift 系小補題）が必要。
  - **II-cross**: a が Y 内・b が C 内 → b = C頭 (lenY) が強制
    （C頭はコピー内厳密最小: S1 = ブロック頭最小 ∀q∈(0,L). e0(j0+q) > e0(j0)、
    le0 連鎖 or le0_interval_gt から）。3亜種:
    (i) m=0 (PC): M の対 (a,j0) の sibrel + mrun M j0 = blocktail@[M!j1] の
        切詰め = **sibrel_trunc で即閉** ✓
    (ii) m≥1, d0=0: a = 最終コピー頭が強制（手前だと先に止まる）→ K=K1=blocktail
        = E族 ✓ 自明
    (iii) m≥1, d0>0: e0(j0+qa)=e0(j1)・尾部クリア・e1(j0+qa)=e1(j0) の同時成立を
        **CFGA_r1 で反駁**: 新Mレベル事実「CFG-A ⟹ e1(j0+qa) ≥ e1(j1)」
        （実証 265/265 で等号、e1(j1) > e1(j0) と合わせ ≠ e1(j0)）。
        j0+qa と j1 は同一 row0 親 w0 の隣接同レベル兄弟、w0 は le0鎖上で
        e1(w0) ≥ e1(j1) — r1ok_climb と同じ値側下界ファミリー。
  - S1 と mrun_shift と I-closed から先に実装、I-open と CFGA_r1 は sorry 小核に分離。

- (続29補5) **シーム手術ほぼ完了（緑）**: sibm2_snoc_copy の I-closed（mrun_append
  閉run不変）・II-int（shf/suffix 転送で sibm2_take から）・II-cross 3亜種
  （m=0: M対(a,j0)+sibrel_trunc / d0=0: a=最終コピー頭強制→K=K1 / d0>0:
  CFGA_r1 反駁＋nextrel1 矛盾）全て証明。sibm2_oper_bad = n帰納で閉。
  残核2点: **seam_I_open**（開タイrunのコピー跨ぎ延長、周期性算術）/
  **CFGA_r1**（e1(j1) ≤ e1(jq)・値側下界・265/265等号・r1ok_climb同族）。
  Isarデバッグ知見: unfolding は同時 fixpoint なので「mra→C_def」の順序依存は
  `unfolding mra mrb unfolding C_def` と2段に分ける / drop_append・mrun_suffix
  は length 形で当ててから lenpre/lentj0 で書換 / nat引き算境界は
  less_diff_conv2＋明示前提（linarith は m*L 非線形で死ぬ→lenYS 展開を渡す）/
  takeWhile_append2 の前提はメタ含意（rule 後 use..blast）。

- (続29補6) **seam_I_open 討伐（緑）**: 延長 E = takeWhile(>lev b) C は
  block_head_min により **空 or コピー丸ごと** の2値（部分切断なし・純粋証明済）。
  O1（C頭 ≤ lev b、E=[]・実証6642/6794）= IH sibm2 Y 直結で閉。
  O2（C頭 > lev b、E=C・150件）= **seam_open_core** に分離（sorry）。
  実証: E族はO2に到達しない(0/5652)・P族延長は P/F1/F2 に着地・hm保存 102/102。
  sibm2_oper_bad 鎖の残核 = seam_open_core + CFGA_r1 の2点のみ。
  seam_open_core の中身 = (i) E族O2の反駁（lev b ≥ C頭を示す） (ii) P族:
  D=K[|K1|..] とコピー C の第一差分が降下（周期性整列） (iii) hm保存
  （maxr1 blk ≤ snd hd K1）。次セッションで各個マイニング→証明。

- (続29補7) **CFGA_r1 討伐（緑）**: 新値補題は不要だった —
  jq と j1 は隣接同レベル和兄弟なので **NT_dom_sub_eq（証明済・STS_A依存のみ）**
  の fbseg 窓で閉じる: pp = w0 := Max{w < jq. e0(w) < e0(jq)}（j0 が証人で非空）、
  mid = (w0,jq)（Max性で全部 ≥ e0(jq)＝mid条件・支配OK）、c = M!jq、
  rest = M[jq+1..j1]（末尾クリアで dropWhile が [M!j1] に到達）→
  snd(M!j1) ≤ snd(M!jq) ✓。**r1ok_climb も同じ手が効く可能性大**（値側下界
  ファミリーの正体は NT_dom_sub_eq の窓選択かも）→ 次に検証。
  教訓: 暴走 metis 2箇所（Cons_nth_drop_Suc 系・in_set_conv_nth+length_take 系の
  詰め合わせ）→ 単発 in_set_conv_nth + nth_take/linarith 分解で即緑。
  isbman kill は分類器拒否 → 自分の Bash バックグラウンドタスクなら TaskStop で
  プロセスツリーごと正当に停止できる。

- (続29補8) **seam_open_core の完全地図（O2=150件の局在化）**: a は**常に prefix 内**、
  (family, b位置, d0) は4型のみ:
  (i) F1, b=copy0頭, d0>0 (60) — 分岐は既に K1 内 ⟹ family/hm 安定（純粋寄り）
  (ii) F2, b∈prefix, d0=0 (42) — 同上
  (iii) P, b∈prefix, d0=0 (28) — C vs D: C-pref-D か先頭即降下
  (iv) P, b=最終コピー頭, d0>0 (20) — 同
  P族 O2 の C vs D 比較は **t=0 で即降下 or C⊆D 接頭辞のみ**（深い分岐ゼロ、
  lenC=lenD は降下時のみ）。E族は O2 に到達しない（0/5652、b は常に高位置）。
  残証明義務: (1) E分岐 O2 反駁 (2) P分岐の C/D 三分律（prefix 整列の周期性核）
  (3) hm(K1@C) = maxr1 blk ≤ snd hd K1 (4) F分岐の純粋安定性。
  全て a∈prefix 局在なので M の prefix 構造＋ブロック構造の直接比較で攻められる。

- (続29補9) **sibrel 衝突代数（緑）+ seam_open_core 設計確定**:
  sibrel_nopref（K の真延長 K@E は sibrel 不可能）・sibrel_ascent
  （共通接頭辞後の第一差分上昇は不可能、任意分解位置で衝突）を純証明。
  **討伐方針 = R事実×SY事実の衝突**: M対 (a,b)（b<j0 のとき mrun M b =
  P0@blk@[M!j1] 形）の sibrel と Y対の sibrel K K1 を衝突させる:
  - E分岐 (K=K1): K1M ⊋ K（m≤1）→ nopref で False / 分岐位置の M!j1 vs blk!0
    上昇（m≥2）→ ascent で False ⟹ **E族O2は新事実なしで反駁可能**。
  - P分岐 m≥2 (d0=0): K!|W1| = blk!0 vs K1M の cj1 = 上昇 → ascent で False
    ⟹ m≥2 P族も自動反駁、**O2-P は m∈{0,1} に局在**（ミニングと一致）。
  - 残る実体: m∈{0,1} P族の C/D 整列（R事実の lexdiff/prefix 分岐から GOAL を
    組む、t=|W1| 分岐は prefix 即閉）・d0>0 の b=コピー頭ケースの持ち上げ
    （shf 対応で take j1 M 対へ）・hm(K1@C) の maxr1 blk ≤ snd hd K1。
  - K1M の開性: O2 ⟹ lev b < e0(j0) ≤ ブロック&j1 全部 ⟹ M run open ✓ 純粋。

- (続29補10) **seam_E_refute 討伐（緑）**: b<j0 の E族O2（K=K1）を反駁。
  機構 = M持ち上げ（mrun M a = K の closed-run 簿記 + mrun M b = P0@blk@[M!j1]
  の open 証明・levlow は m=0なら high・m≥1なら copy0頭で ob から）→
  sibm2 M インスタンス sibrel K K1M → m≤1 は nopref・m≥2 は分岐点
  cp1!0=(e0j0+d0,e1j0) vs M!j1=(e0j1,e1j1) の上昇（d0=0:fst上昇 / d0>0:fst同・
  snd上昇=nextrel1）で ascent 衝突。デバッグ: dropbM 双方向 simp ループ（自殺技）・
  append_take_drop_id[symmetric] 直当て・upt数値リテラルは Suc 1 形。
  残: seam_open_core 本体の組み立て（P/lexdiff 分岐・b≥j0 ケース）。
  P分岐 m=0 は R事実分岐から完全純粋で閉じる設計済（続29補9）。

- (続29補11) **b<j0 ケースの完全設計（実装待ち）— hm境界は無料だった**:
  - **snd集合論法**: コピーはsndを変えない（shf）ので snd-set(K1@C) ⊆
    snd-set(P0@blk) 。m≥1 なら K1 ⊇ P0@blk ⟹ maxr1(K1@C) = maxr1 K1 ⟹
    SY-lexdiff の hm K1 がそのまま hm(K1@C) に。m=0 は coreM-lexdiff が強制
    （分岐点 < |P0| では eq/pre 不可能）で hm K1M ⟹ maxr1 blk ≤ snd hd P0 ✓。
    **hm境界の新規マイニング事実は不要**。
  - **m三分律 (P族)**: m=0 → coreM の3分岐から純粋に閉じる（eq/pre は
    K1@C=P0@blk が K の接頭辞・lexdiff は butlast K1M=P0@blk で hm_take）/
    m≥2 → K⊇P0@blk@cp1 と K1M の分岐点で ascent 反駁（seam_E_refute と同じ手）/
    **m=1 のみ実体**: D vs [cj1] / cp1 比較で d0=0 のとき snd等式 e1(j0)=0 が
    必要（i1=0 ⟹ e1(j1)=0 は無料）— 28実例・要マイニング＆討伐。
  - lexdiff族: 全 m で純粋（分岐点は |K1| 内・snd集合論法で hm 継承）。
  - 残実体 = (s1) m=1 P族の e1(j0)=0 問題（d0=0・b<j0）
            (s2) b≥j0 コピー頭ケース（d0>0・F1 b=C0頭 60 + P b=Clast頭 20）
    (s2) は shf 持ち上げ＋同型の衝突が効くはず（次セッション）。

- (続29補12) **seam_open_blift 討伐（緑）・seam_open_core 配線完了**:
  b<j0 ケース完全証明 — E族= seam_E_refute / P族 m=0 = coreM 3分岐
  （eq/pre→接頭辞・lexdiff→butlast_append+hm_take）/ P族 m≥2 = ascent反駁 /
  lexdiff族 = snd集合論法（m≥1: blk⊆K1 / m=0: sibrel_diverge で coreM の
  hm K1M を強制取得）。sibrel_diverge（分岐強制補題）新設。
  残 sorry = **seam_open_m1**（m=1 P族・D vs cp1 比較・e1(j0)=0 問題）と
  **seam_open_copyhead**（b≥j0・d0>0・F1@C0頭60+P@Clast頭20）の2点
  + 既存の値側群。sibm2_oper_bad 鎖はこの2点で完結。

- (続29補13) **seam_open_m1 の実態（マイニング確定）**: 全14件が
  m=1・d0=0・**L=1**・D=[cj1]・e1(j0)=0・e1(j1)=0 の単一形。
  目標は F2分岐: x=cj1=(e0j1,0) vs x1=blk!0=(e0j0,e1j0)、必要事実は
  (f1) e1(j0)=0 (f2) hm K=P0@blk@[cj1] (f3) hm K1@C。いずれも対(a,b)の
  共起構造から来る生成機構が未解明（裸の i1=0 ブロックでは e1(j0)≠0 可）。
  m≥2 は 0件（ascent反駁の実証一致）。b<j0-P-O2 は m∈{0,1} のみ ✓。
  次の攻め: (a,b) 対の存在が M の自己相似構造（prefix が P0@blk@[cj1] を含む
  ＝前世代の oper 痕跡）を強制する点を使う or seam_open_m1 を閉包+2 で
  最弱前提化してから生成帰納。

- (続29補14) **seam_open_copyhead 討伐（緑）**: b=j0 ケース完全証明
  （b>j0 は copyhead_deep に分離・実証0件）。機構: b=j0 ⟹ d0>0 強制
  （d0=0 なら high が即矛盾）⟹ i1=1 ⟹ e1j0<e1j1 で全 snd 比較無料。
  M対 (a,j0)・mrun M j0 = blktail@[cj1]・E/P-m≥2 は xx=(e0j1,e1j0) vs
  cj1=(e0j1,e1j1) の snd 上昇 ascent 反駁・lexdiff は snd 集合論法
  （m≥2: cp1⊆K1 / m=1: sibrel_diverge で hm K1M 強制・e1j0<e1j1≤maxr1）。
  sibm2_oper_bad 鎖の残 sorry 3点: **seam_open_m1**（b<j0・m=1・14件・
  e1j0=0機構）/ **seam_copyhead_m1**（b=j0・m=1・20件・全部 L=1）/
  **seam_copyhead_deep**（b>j0・実証0件）。
  暴走犯また metis（Cons_nth_drop_Suc+drop0 詰め合わせ）→ cases blk で即緑。

- (続29補15) **E6_tie_nofire0/1 討伐（緑）**: 新純粋補題 Gterm_empty_lowhead
  （fbseg 窓で snd hd S < u ⟹ Gterm u (NT S) = ∅。長さ帰納: NT_shape + fbseg_T_desc
  + fbseg_hd_level（レベル同強制）+ NT_dom_sub_eq（頭添字非増加）で T 鎖を下る）。
  ¬hm タイランは実証で常に y=snd hd K < u=snd c（16/16）⟹ low ケースで即無発火。
  残 = E6_tie_nofire_high0/1（y ≥ u ∧ ¬hm・実証空クラス・縮小 sorry）。
  事故メモ: python str.replace は全置換 — 同一文面の補題が並ぶときは行範囲で編集。

### (2026-06-11 続30) Buchholz ψ との対応に関する Q&A 記録（P進bot ブログ照合）

ユーザー質問:「P a b c は既存の Buchholz ψ_a(b)+c とは対応しないけど大丈夫？」
（参照: P進大好きbot "Please Help me on study of Pair Sequence System" Googology
Wiki 2018、親ディレクトリに PDF）。回答＝**大丈夫、設計で織り込み済み**:

- ブログの論点: (a,b)→「深さ a の ψ_b」の素朴対応は本物の Buchholz OCF では
  壊れる。原因は正規形条件 β∈C_ν(β)（Maksudov コメント）: ψ₂(0)>ψ₁(ψ₂(0)) ゆえ
  ψ₀(ψ₁(ψ₂(0))) = ψ₀(ψ₂(0)) と値が潰れ、項構文と順序数値が一対一でない。
- 本証明は P a b c = ψ_a(b)+c という意味論対応を一切仮定しない:
  (i) olt は全項上で非整礎（t_k/x_k 鎖）→ 整礎性は wf3 クラスに制限して自前証明
  （柱2 wf_olt_wf3）。wf3 の条件 ∀g∈Gterm u b. olt g b は β∈C_ν(β) の構文版。
  (ii) proj はこの潰れ等式 ψ_u(b)=ψ_u(g) を計算する装置そのもの。nrm∘translate
  ＝「正規形条件を尊重した正しい Buchholz 読み」。
  (iii) 旧 route A（NF→順序数値直接埋め込み）はまさにこの collapse で破棄
  （proof-ja.md 冒頭凡例・task.md 行51 に記録済）。
  (iv) 必要なのは ψ 値との一致ではなく、wf3 上 olt 整礎（済）＋ nrm_step_dec
  （攻略中）の2点のみ。otembed の oV も「wf3 上の何らかの厳密単調順序数値写像」
  でよく ψ と一致する必要なし。
- 標準形どうしは nrm 後も非衝突（valnorm.py 2,643,843 ペア衝突0・逆転0）。
  ブログの「1=3」例は非正規形 ψ 式の値同一視であり標準形の衝突ではない。

- (続30補) proof-ja.md/task.md から移設した経緯記録:
  - 旧 route A＝ZFC 順序数で ψ を構成する意味論的証明は、Buchholz ψ が
    PSS 標準形の対角を collapse するため破棄した（proof-ja.md 凡例から移設）。
  - 旧 K-dom ルート（wo/buchholz/embed）は absolute 変種・残 sorry あり・不使用。
    oV の「NF 直接埋め込み」は collapse で破棄し、wf3 上の埋め込みとして
    柱2（wf_olt_wf3）に再生した（task.md 行51 から移設）。
  - 運用ルール明文化: proof-ja.md は証明本文のみ（冒頭に注記追加）、
    task.md は進捗ツリーのみ、経緯・履歴・Q&A は memo.md へ。

### (2026-06-11 続31) seam_copyhead_m1 討伐（緑）— 閉包+1教訓の再演

- **seam_copyhead_m1 / _L2 完全証明**。構造: coreM = sibm2 M の対 (a, j0) から
  `sibrel K (blktail@[M!j1])`（mrun M j0 = blktail@[cj1] は block_head_min で全取り）。
  D の形 4 分岐: (E) D=[cj1] → blktail 全要素=cj1 なら hm 両側無料で F1 降下直証
  （実在114件は全部この E-const 形）/ (F1分岐) sibrel_diverge で hm K・hm K1M を
  強制取得 → hm(blktail@C1) を hmKM から Max 移送（snd(cp1)⊆{e1j0}∪snd(blktail)、
  e1j0<e1j1≤hd）→ F1 直証 / (F2-L1) blockok ステップ規律
  fst(M!Suc a)≤e0j0+1≤e0j1 で反駁 / 残差3点に分離。
- **閉包+1教訓の再演**: 旧マイニング「全20件 L=1」は文脈が狭かった。
  audit_copyhead_m1.py（新設・閉包+1・正確文面）で L=2 が18件実在と判明
  → _L2 を凍結せず直証する設計に変更。最終分類: E-const 114 / 他 0。
- 残差（全て閉包+1で0件・凍結）: **seam_copyhead_m1_P**（D=cj1#D'・一般L化済）/
  **_E2var**（L≥2・D=[cj1]・blktail 非定数）/ **_F2L2**（L≥2・F2上昇）。
  これらは open_m1 と同じ「生成機構」級（裸の局所制約では反駁不能、
  自己相似 or 世代帰納が要る）。
- sorry 数 19→21 だが質的には広義 copyhead_m1（実在114件クラス）が消え、
  実証空クラス3点に置換。次: seam_open_m1 / r1ok_climb（CFGA_r1窓手法）。

### (2026-06-11 続32) r1ok_climb 討伐（緑・残差なし）— 方向懸念の解消

- 鍵は3点の構造強制: (1) **q = 0 強制** — q≥1 だと level-min 前提（r=0 で
  e0(j0+q)≤e0j0）が block_head_min（e0j0 < e0(j0+q)）と矛盾。
  (2) **j0+r' = parent0(j1)** — r' は「レベル e0j0+d0-1 の最後のブロック列」
  ＝ nextrel0 M (j0+r') j1 が1ステップで成立（rlast がそのまま間隙条件）。
  (3) **nextrel1 の最小性条項が逆向き下界を無料で供給** —
  j0 = row1親 ⟹ ∀j. j0<j ∧ le0 M j j1 ⟶ e1 j ≥ e1j1。j := j0+r' で
  e1(j0+r') ≥ e1j1 > e1j0 ⟹ 結論 e1q ≤ Suc e1r'（実証: 差は常に ≤0、
  d0≥2 では < 0 — 主張より強い不変量が真因）。
- 「climb は前を後ろ+1で抑える＝CFGA_r1 と逆方向」という懸念（続29補7）は
  誤りで、窓手法ではなく **親子定義の最小性** が正しい武器だった。
- 細部: r'=0 は自明ケース。r'≥1 ⟹ d0≥2 ⟹ i1=1 が芋づる式。
  block_head_min は前方（r1ok 節の手前）へ移動。nat 減算は arith で処理。
- sorry 21→20。次: シーム残差 or 値側コア or fire-cascade。

### (2026-06-11 続33) E6_tie_nofire_high0/1 機構調査（未討伐・知見記録）

- 閉包+2 全タイラン分類: (y<u,hm)232 / (y=u,hm)272 / (y=u+1,hm)90 /
  **(y<u,¬hm)6 / (y≥u,¬hm)0**。high クラス空を再確認。y>u+1 は皆無。
- 新不変量候補 **T1: タイラン全要素の row1 ≤ u+1**（u=タイ添字）。全例成立。
  y=u+1 ケースは T1 だけで hm が出る（全≤u+1=y）。y=u ケースは
  **T3: y=u ⟹ 全要素 ≤ u** が要る（経験的に成立、T1 では不足）。
- y ≤ u+1 自体は r1ok 隣接親（hd K の row0 親 = c、blockok で level=v+1 強制）
  から出るはず。T1/T3 は生成機構級（コピー由来のタイ構造が必要）。
- ¬hm 実例は全て c=(v,1)・K=[(v+1,0),(v+2,1)]^k 反復・c1=(v,1) の単一形。
- 結論: high0/1 は T1/T3 を新クラス事実として凍結すれば閉じるが、bump の
  移動に過ぎないので、GRAND 同時帰納の設計時に統合するのが得策。

### (2026-06-11 続34) E6_nbcK_T 機構特定（閉包+1分類・未実装）

- dseg（u ≤ snd c0・K≠[]）の全分類: (T≠[],mK<mAll,c0≥m)8384 /
  (T≠[],mK=mAll,c0≥m)546 / (T=[],…)多数 / **(T≠[],c0<m) は mK= でも mK< でも 0件**。
- ⟹ 真の不変量候補 **INV-closure: dseg で c0 のランが窓内で閉じる（T≠[]）なら
  snd c0 = maxr1 S（c0 が窓の row1 max を達成）**。E6_nbcK_T はこの対偶で即閉じる
  （premise snd c0 < maxr1 ⟹ T=[]）。
- 構造ポイント: dseg の c0 は **pp の直後列**（blockok で fst c0 = fst pp + 1、
  r1ok で snd c0 ≤ u+1、premise u ≤ snd c0 と合わせ snd c0 ∈ {u, u+1}）。
  続33 の T1（タイラン ≤ u+1）と同族 — 「窓を閉じるランの row1 は開け口で抑える」
  という単一テーマ。host レベル一般では偽（y=u+1 タイ例）、pp 直後 c0 限定で真。
- 次: INV-closure を ST_PS 生成帰納（r1ok と同じ骨格）or fbseg ホスト転送で証明
  → nbcK_T 即落ち。qcut_last/iii_singleton/seam も同じ土台の見込み（続26計画）。

### (2026-06-11 続35) ginv キャンペーン開始 — E6_nbcK_T 討伐（緑）

- **ginv 定義**（閉鎖窓 row1 上界）: 任意の支配窓 pp#S（S=H[p+1..p+n+1]、
  全要素 fst > fst pp）で S 内に fst ≤ fst(hd S) の戻り列があるなら、
  S 全要素の snd ≤ max(snd pp, snd(hd S))。実証: 閉包+1 14638 / +2 42489 窓
  違反0（vis/dip 両方）。局所算術では h1 = s0+1 を排除できない**非因果的**
  制約（後の戻りが前の列を制限）なので r1ok 型の生成帰納が必須。
- 緑: ginv_diagSeq（diag は fst 狭義増加で閉鎖不能＝空虚）/ ginv_take /
  ginv_butlast / ginv_oper（ディスパッチ、r1ok_oper の複製）/ ginv_ST_PS /
  **ginv_dseg_bound**（dseg 橋渡し、インデックス算術）。
  凍結: **ginv_oper_bad**（コピー横断窓のシーム型保存・次の主戦）。
- **E6_nbcK_T 討伐**: 対偶一発 — closure（dropWhile≠[]）なら ginv_dseg_bound
  ＋可視性 u ≤ snd c0 で maxr1(c0#rest) ≤ snd c0、premise snd c0 < maxr1 と矛盾。
- fire-cascade 5点 → 残4点（E6_lpl/E6_dom_deep/E6_memT/E6_nbcK_K）。
- 適用候補メモ: E6_tie_nofire_high はタイランが窓内で头レベルに戻る形なら
  ginv(pp:=c) で hm 強制が出る（単一ブロック形は開窓で silent — 要追加機構）。
  qcut_last/iii_singleton/seam も ginv 土台の見込み（続26計画）。
- Isar 事故録: c0#rest@post の nth_append は head-Cons 正規化後に効かない
  → cases i / nth_mem は rule で / nat 減算 ki・iL は arith / 分岐含む dom は auto。

### (2026-06-11 続36) ginv_oper_bad 設計（ケース地図確定・実装前）

X = take j0 M @ copies。閉鎖窓 (P, c0=X!(P+1), 窓 [P+1..end), 閉鎖位置 clpos)。
マイニング（基底閉包・n∈{1,2,3}・全 'ok'）でケース地図確定:

- **A (窓⊆prefix)**: X!i = M!i 転送 → ginv M。容易。
- **B (窓⊆単一コピー k)**: shift不変（fst一律+kd0・snd不変）→ M のブロック窓
  [j0+qP+1..] へ転送。容易（ncopy 添字算術）。
- **C (pp∈prefix・横断・P < j0-1 または閉鎖が prefix 部)**: M窓 [P+1..j0+q_max]
  へ転送。閉鎖転送: clpos=(k,q_cl) なら e0(j0+q_cl) ≤ fst c0（c0 は prefix で
  無シフト）よりブロック位置 j0+q_cl が M側閉鎖。q_cl=0 でも位置 j0 > P+1
  （P<j0-1）なので有効。被覆: 窓がコピー0を完全被覆 or 窓内で q_max まで
  → M窓支配 OK。bound 要素: snd はブロック/ prefix の M 要素 ✓。
- **P=j0-1 ∧ d0>0 ∧ 閉鎖**: 不可能（閉鎖列のレベル e0(j0+q_cl)+kd0 ≤ e0j0 が
  block_head_min と衝突）→ 反駁で閉じる。
- **D (P=j0-1 ∧ d0=0)**: 閉鎖はコピー頭タイのみ・M側は開窓で ginv M 沈黙。
  新クラス事実 **GBLK0**: i1=0・j0=parent0(j1)・0<j0・fst(M!(j0-1))<e0j0 ⟹
  ブロック snd ≤ max(snd(M!(j0-1)), e1j0)。実証 1272/1272（≤e1j0 単独は32反例
  で max 形が必要）。凍結予定（生成機構級・GRAND 候補）。
- **E (pp∈コピー k・横断)**: qP 分布 {0: 624, 1: 147, 2: 24}。
  - qP=0: pp=コピー頭（snd=e1j0）。M窓 [j0+1..j1] が **全実例で支配+閉鎖**
    （domM∧clM 795/795）→ ginv M で q'≥1 要素 OK、コピー頭 q'=0 は
    snd=e1j0=snd pp ≤ B で直 ✓。L=1 は c0=次コピー頭の特例。
  - qP>0: コピー k+1 の q'≤qP 要素（M双子が pp_M より前）が M窓外。
    コピー頭は e1j0 < e1j1 ≤ B（i1=1 + M窓に j1 含む）で OK の見込み。
    0<q'<qP は「後ろの低列で前を抑える」r1ok_climb 風 — 機構未特定。
    → 残差 **ginv_oper_bad_qpos** として凍結（注意: 実例 171 件の
    LIVE クラス、空クラスではない。nextrel1 最小性 or ブロック内
    祖先鎖の窓手法を試す）。

実装順: A/B/C/反駁/E-qP=0 を本体に、D=GBLK0 と E-qpos を凍結 sorry に分離。

- (続36補) E-qpos の bound 源マイニング: q'<qP 要素 260/260 が
  snd ≤ snd(M!(j0+qP))・≤ B・**≤ e1j1** を全て満足。証明源候補 = e1j1 経由
  （M窓 [j0+qP+1..j1] は j1 を含むので e1j1 ≤ B が ginv M から無料；残るは
  「窓内 q'<qP ブロック列の snd ≤ e1j1」— 支配条件 e0(j0+q') > e0(j0+qP)-d0
  の高レベル列に対する上界。nextrel1 鎖 or NT_dom_sub_eq 窓を次に試す）。

### (2026-06-11 続37) ginv_oper_bad 討伐（緑）— 横断窓保存の完成

- **ginv_ob_pre 緑（一発）**: C1=窓⊆prefix+copy0 の同値転送 / Suc p=j0 では
  閉鎖が qc=0∧kc≥1 を強制し d0=0 が**導出**される（d0>0 反駁が不要に）→
  GBLK0 シームへ / C2=M窓 [p+1..j1-1] 転送（閉鎖はブロック双子位置で転送）。
- **ginv_ob_copy 緑**: EB=コピー内 shift 不変転送 / L=1 横断は閉鎖不能で反駁 /
  qP=0 横断は M窓 [j0+1..j1]（支配=block_head_min 無料、閉鎖証人は
  d0=1→j1 自身・d0≥2→qc≥2 強制（qc∈{0,1} は blockok+算術で反駁））/
  qP>0 → ginv_ob_qpos 凍結。
- **暴走犯の確定**: `thus ?thesis using NM1 by blast`（∃tm ゴール）— blast が
  0<NM と 1≤NM の橋渡しできず深さ反復でハング（1800s×2回）。教訓:
  **∃ ゴールは blast 任せにせず `by (intro exI[of _ w]) (use … in simp)`**。
  二分探索手順: ブロック sorry 化→復元を繰り返し 3 ビルドで特定。
  ついでに meson 連鎖/simp+trans 規則 4 箇所も明示 mult_le_mono1+arith 化。
- 残差: **ginv_GBLK0**（実証 1549/0、d0=0 世代機構）と **ginv_ob_qpos**
  （**live 171件**、q'<qP 要素は全て snd≤e1j1=B 内、nextrel1 最小性経由が
  候補 — r1ok_climb と同じ武器が効く可能性）。
- これで ginv_ST_PS は GBLK0/qpos を残して完全。E6_nbcK_T は既に ginv 経由で
  討伐済み。次: qcut_last/iii_singleton/seam への ginv 適用 or qpos 攻略。

- (続37補) qpos 機構マイニング: 全260サブ要素が (i) j1 の row0 祖先
  （一般ブロック列では祖先の27%が e1>e1j1 なのに qpos 文脈では全て ≤、
  nextrel1 最小性の ≥ と合わせ **e1 = e1j1 ピッタリ**）(ii) snd ≤ snd(M!(j0+qP))
  =pp直接。q'=0 は e1j0 < e1j1 ≤ B（M窓に j1 含む）で証明可能。q'≥1 は
  qP=2 窓のみで出現（q'=1）。「前のブロック列を後ろで抑える」型＝GBLK0 と
  同族の世代機構。GRAND 統合候補。

### (2026-06-11 続38) 戦略ノート — GRAND 統合の輪郭（次の主設計）

残 sorry の質的分類（nrmstep 21 = 値側数点 + 世代機構群 + 行レベル）:
- **世代機構群（強化不変量 ginv2 候補）**: ginv_GBLK0（d0=0 ブロック e1 上界）/
  ginv_ob_qpos（ブロック内後方上界・祖先 e1=e1j1 ピッタリ）/
  E6_tie_nofire_high の T1・T3（タイラン ≤ u+1, =u）/ seam_open_m1（e1j0=0機構）/
  copyhead 残差 P・E2var・F2L2。共通形＝「裸の局所制約では出ない、コピー由来
  の構造が後方・上方を縛る」。
- 統合案: **ginv2 M = ginv M ∧ gblk0 M ∧ (qpos-fact M) ∧ (tie-T1 M) ∧ …** を
  1本の ST_PS 生成帰納で同時保存（r1ok/ginv と同じ骨格、oper_bad で相互供給）。
  各成分は単独では帰納が閉じず、相互に前提を供給し合う（GRAND の正体）。
- 手順案: (1) 各成分を M レベル述語に正規化（パラメータ依存を「M の最終列の
  bad-branch 構成」に限定）(2) 閉包+1/+2 で各成分の正確文面監査
  (3) oper_bad 保存をシーム分解（ginv_oper_bad の地図を雛形に）。
- 値側（NT_lexdiff_lt / nbcK_K / E6_lpl / E6_dom_deep / qcut・iii・seam・STS_B）
  は別軸（fire-cascade）。GRAND-世代側が閉じると行レベルの前提が
  arithmetic 化される（続26計画の完成形）。

### (2026-06-11 続39) t1ok/t3ok 基盤＋E6_tie_nofire_high0 討伐（緑）

- **t1ok/t3ok 定義・生成帰納骨格 緑**（GRAND 成分 T1/T3 の Isabelle 化）:
  snd タイ停止のラン上界（≤ u+1 / 頭タイなら ≤ u）。緩和形（fst 停止は ≤ のみ）
  で閉包+1 13106/8097 件 0違反。diag=空虚（snd 単射）/ take=tie_take_pair
  （b<m が飽和を排除し mrun 同一）/ oper_bad ×2 凍結。
- **E6_tie_nofire_high0 討伐**: fbseg→host 抽出、mrun H' a = K（takeWhile
  分割+hd_dropWhile）、t1ok ⟹ y ≤ u+1、premise u ≤ y ⟹ y∈{u,u+1}、
  y=u は t3ok で全≤u ⟹ hm、y=u+1 は t1b で全≤y ⟹ hm — どちらも ¬hm premise
  と矛盾（前提偽クラスの discharge）。
- high1 は c1 のランの停止情報が premise に無く未着手（c1 ラン停止の
  snd タイ性 or 停止なしケースの別機構が要る — 次の調査対象）。
- sorry 22（t1ok/t3ok_oper_bad +2、high0 -1）。oper_bad 2点は GRAND シーム
  （ginv_oper_bad の地図を雛形に、新タイ=コピー境界タイの分析）。
- 事故録: cwd リセットで相対パス編集が2回空振り→以後ファイル編集は絶対パスで。

### (2026-06-11 続40) E6_tie_nofire_high1 討伐（緑）— タイ無発火コンプレックス完全制覇

- 新不変量 **t14ok**（T14: snd タイ停止列 c1 の自前ランは head-max。閉包+1 で
  705ラン 0違反、開ラン/閉ラン両方・¬hm 皆無・停止は常に snd タイ）。
  diag/take（hm_take 接頭辞遺伝）/butlast/dispatch 緑、oper_bad 凍結。
- **high1 討伐**: ホスト抽出→タイ対 (a,b) 確立→mrun H' b = takeWhile(rest1@post)
  → 窓ラン K1 は take |K1| (ホストラン)（takeWhile_append1/2 の2分岐）→
  t14ok で hm(ホストラン) → hm_take で hm K1 → ¬hm premise と矛盾。
- これで E6_tie_nofire0/1 + high0/high1 全滅 = **NT_tie_resolved の無発火系
  依存が全て緑**。
- 事故録: hm_take が t ブロックより後方定義で Undefined fact → 前方移動。
  b_def で畳んだ不等式は bH[unfolded b_def] で渡す（unfolding は goal のみ）。
- sorry 22（t14ok_oper_bad +1 / high1 -1）。GRAND シーム在庫:
  t1ok/t3ok/t14ok_oper_bad・GBLK0・qpos（全て同型のコピー境界タイ分析）。

### (2026-06-11 続41) GRAND シーム地図確定（t1ok/t3ok/t14ok_oper_bad の設計）

X = oper-bad のタイ対 (a,b) 分類（T1 違反 0 / 全 23396 対）:
- **P-P**: 両方 prefix → ラン共有・恒等転送（停止 < j0）。
- **C-same**: 同一コピー内 → shift 転送（EB と同型）。
- **P-C**: a∈prefix・b∈コピー → **b = (0,0) 強制**（証明: ランが copies に
  入ると copy-0 頭 e0j0 > fst a が必要だが停止 ≤ fst a、ゆえに copy-0 頭が
  最初の停止。kb≥1 は d0=0 でも copy-0 頭が先に停止するので不可能）
  → M 対 (a, j0) に恒等転送（値・ラン完全一致）✓。
- **C-cross-qa-0**: a=(ka,qa)・b=(kb,0) コピー頭のみ（rb>0 は皆無 — 同上の
  論法で頭強制）。新内容はここだけ:
  - kb=ka+1: ラン = コピー ka 尾。M ランは j1 で停止（e0j0+d0 ≤ e0(j0+qa) が
    停止条件から出る）が e1j1 ≠ e1j0（i1=1）でタイにならず M 不変量沈黙。
    必要事実 **BT1: 支配条件下のブロック尾 snd ≤ e1(j0+qa)+1**（t3/t14 用は
    =/hm 版）。
  - kb>ka+1: ラン = 尾 + フルコピー数回 + …: snds = 尾∪ブロック全体:
    **ブロック全体版 BT2** が要る（GBLK0 の max 形と同族）。
- ⟹ 世代シーム5点（t1/t3/t14_oper_bad・GBLK0・qpos）は全て
  **ブロック内 row1 上界の小族（BT 族）** に帰着。次: BT 族の正確文面
  マイニング → M 不変量からの導出可否判定 → 導出不能分のみ凍結して組立。

- (続41補) BT 族監査（閉包+1）: **BT1**（タイ前提 e1(j0+qa)=e1j0・停止条件
  e0j0+d0≤e0(j0+qa)・尾支配 ⟹ 尾 snd ≤ u+1）= 6370/6370 ✓。
  **BT1-T3**（尾頭タイなら ≤ u）= 1755/1755 ✓。BT2 は不要と判明 —
  停止条件下では中間コピー頭が支配できず **C-cross は kb=ka+1 に強制**
  （ラン = コピー ka の尾だけ）。**BT-hm は6違反で偽** — t14 シームは
  尾-hm では閉じず別ルート（d0>0 開ラン形の分析）が要る。
  M 転送は (j0+qa, j1) 対が d0>0 でタイにならないため BT1 は真に新規
  （凍結対象）。次: BT1/BT1-T3 を凍結して t1ok/t3ok_oper_bad を実装、
  t14ok_oper_bad は6違反例の精査後に設計。

- (続41補2) ginv_BT1 凍結（緑）。t1ok_oper_bad 実装メモ（次ティック用）:
  停止事実 fst(X!b) ≤ fst(X!a) は **nth_length_takeWhile**
  （|takeWhile| < |xs| ⟹ ¬P (xs ! |takeWhile|)）で導出（mrun_def 展開、
  drop の nth で X!b へ）。ケース: a<j0（b≤j0 強制: j0∈run と hm0/シフトで
  停止矛盾 → Xv0 恒等転送＋mrMa crib → t1ok M）/ a≥j0 同コピー
  （qa≥1 強制（qa=0 だと停止が hm0 矛盾）→ shift 転送 → t1ok M）/
  跨ぎ（b = j0+(ka+1)L 強制 → BT1）。

### (2026-06-11 続42) t1ok_oper_bad 討伐（緑）— GRAND シーム第1号

- 3ケース実装: **prefix**（b≤j0 強制: j0∈run と hm0 で停止矛盾 → 恒等転送 →
  t1ok M）/ **C-same**（qa≥1 強制 → KM define で shift 転送 → t1ok M）/
  **C-cross**（b = 次コピー頭 j0+(ka+1)L 強制 → tie/stop/dom 前提を抽出 →
  ginv_BT1）。停止事実は nth_length_takeWhile。
- 事故録3連:
  (1) 暴走 = 7補題 metis（in_set_conv_nth+length_take 詰め合わせ）→
  in_set_conv_nth 単独+明示化。
  (2) arith は積を原子扱い — (ka+1)*L と ka*L が無関係になる →
  事前に b - Suc a = L - Suc qa 形へ simp 正規化してから arith。
  (3) **unfolding 無限再帰**: dsplit の RHS が LHS 部分項
  （take … (drop (Suc am) M) が drop (Suc am) M を含む）を含むと
  unfolding がスタック溢れ（Interrupt_Breakdown）→ KM を define で
  不透明化してから dsplit。教訓: dsplit 系の分解は必ず define 越し。
- 残 GRAND シーム: t3ok_oper_bad（本補題のクローン+BT1-T3）/
  t14ok_oper_bad（BT-hm 偽のため要再設計）/ GBLK0 / qpos / BT1 本体。

- (続42補) **t3ok_oper_bad 討伐（緑）**: t1ok 本体のクローン＋T3 デルタ
  （ne/hd1 前提・Suc なし結論・prefix/C-same は t3ok M 転送＋hd 移送
  （h0 は calc 形 — unfolding で am_def が mrM パターンを先に壊す事故）・
  C-cross は headtie 抽出 → **ginv_BT1_T3** 凍結）。
  残 GRAND シーム: t14ok_oper_bad（BT-hm 偽・要再設計）/ GBLK0 / qpos /
  BT1・BT1_T3 本体（ブロック内世代事実・実証 6370/1755 全0違反）。

### (2026-06-11 続43) 🚨健全性キャッチ: t14ok が閉包+2で偽 → hi 前提付きへ弱化（緑）

- **発見経路**: BT-hm の6違反例（d0=0・qa=0・(v+1,0)(v+2,1)反復尾）を X に
  持ち上げると t14ok X の反例になる（コピー頭タイ対の停止ランが ¬hm）。
  閉包+1 監査（705ラン0違反）はこの形を含まず — **閉包境界教訓の再々演**。
  閉包+2 監査: (lo,¬hm) 36件実在 / **(hi,¬hm) 0/54,440** ⟹
  **t14ok' = hi 前提（snd(M!b) ≤ snd(hd(mrun M b))）付きなら真**。
- 修正: t14ok 定義に hi 前提追加・t14ok_take に hd 移送（hdeqb）・
  high1 呼び出しに hib 供給（high1 は元々 HI 前提を持つので無傷）。
- 事故録: hdeq1 の「自己参照等式 + cases-auto」がスタック溢れ
  （K1 = take (length K1) … の K1 が RHS 内に出現）→ hd_conv_nth calc 鎖へ。
  **教訓: |xs| を含む take/drop 等式は rewrite に使わず calc で nth 経由**。
- 教訓の制度化: 新凍結不変量は必ず閉包+2 で監査してから定義に固定する
  （t1ok/t3ok は閉包+1 のみ — 次ティックで +2 監査を回す）。

- (続43補) 凍結全量の閉包+2監査 ✓: t1ok 146108 / t3ok 34347 / BT1 18945 /
  BT1_T3 5251 / GBLK0 3580 — 全0違反。世代側凍結コアの土台は +2 で健全。

- (続43補2) t14ok_oper_bad シーム地図（hi 限定・全15クラス hm ✓）:
  a∈P: b∈{P, C0(=j0頭)} 強制。inM（ラン ⊆ 位置 < j0+L）は Xv0 同値転送
  （closed は完全転送 / open は n=1 で X-run = take(M-run)、t14ok M + hm_take）。
  **past クラス（(P,P,past,open) 87・(P,C0,past,open) 20）が新規内容**
  （prefix 頭がブロック snd 群を支配する GBLK0 族）。
  a∈Ck: 同コピー stop（shift 転送+末尾）/ 次コピー頭 stop（コピー尾ラン
  = BT-hm 族だが hi 付きで真の形）。実装は t1ok 級の本格戦 — 地図のみ
  確定し凍結維持。次の優先 = **BT1 本体の世代解析**（oper 結果の
  bad-params (j0',j1') と親 M の関係から block 内事実を帰納）。

### (2026-06-11 続44) X=oper M n の bad-params 族（BT1帰納の土台マイニング）

X の (j0',j1',i1',d0') と M の関係は4族（閉包・n∈{2,3}・noparams 72除く）:
- **P族**: j0'∈prefix・**LX = k·L**（新ブロック=フルコピー数個）・d0' 多様。
- **Cキ頭族**: j0'=コピー k の頭 (q=0)・**LX = L-1**（新ブロック=最終コピーの尾）。
- **Cキ末族**: j0'=コピー k の末 (q=L-1)・LX = L・d0'=0（新ブロック=次コピー丸ごと）。
- **C中間族**: j0'=コピー中間・LX 小（小さい尾片）。
⟹ X のブロック要素の snd は常に M ブロック要素の snd（コピーは snd 保存）。
BT1(X) の帰納ステップ = X-block 内の窓を M-block の対応窓に写し、
BT1(M)/T1/T3/ginv(M) で閉じるか新形を特定する作業（族ごと）。
次の手: 族ごとに BT1(X) インスタンスの M-side 還元先をマイニングで分類。

- (続44補) BT1(X) 還元分類: P族 {BT1(M)直 508 / 接頭辞アンカー 714（qa' が
  prefix 列 — GBLK0 族の接頭辞アンカー版が必要）} / Chead {BT1(M)直 1152 /
  FAIL 1046（前提どれが落ちるか要精査）} / Cmid {直 118 / FAIL 204} /
  Clast = インスタンス0（空虚）。⟹ BT1 の生成帰納は「BT1(M)直還元＋
  接頭辞アンカー新形＋FAIL 形の closing fact」の3部構成。次: FAIL の
  前提別分類と closing fact の特定。

- (続44補2) BT1M-FAIL 詳細（全て nowrap・結論は真）: Chead fail:dom 702
  （X ブロック = コピー尾は M ブロックより短い — M 側 dom が j1 まで要求され
  過剰）/ Chead fail:stop 344（d0X ≠ d0）/ Cmid fail:tie 176（中間アンカーは
  e1(j0X) とタイ、M の e1(j0) とは限らない）。
  ⟹ 一般化方針: **BT1-gen(α, ω, τ)** = ブロック窓 [α+1, ω) を e1(α)+1 で
  抑える窓付き不変量（現 BT1 = (qa, L, 0) 特殊形）。X→M の写像は (α,ω,τ) の
  シフトとして閉じる見込み。次: BT1-gen の正確文面設計＋閉包+1/+2 監査
  → 凍結を BT1-gen に置換 → 生成帰納の3部実装。

### (2026-06-11 続45) ★BT-WIN 発見 — ブロック内不変量の統一形（閉包+2 完全成立）

- **BT-WIN**: bad-branch M・α < ω ≤ L・
  dom: ∀q∈(α,ω): e0(j0+q) > e0(j0+α)・
  stop: e0(j0+ω) ≤ e0(j0+α)（j0+L は j1 と読む）⟹
  ∀q∈(α,ω): **e1(j0+q) ≤ e1(j0+α)+1**。
  頭タイ（e1(α+1)=e1(α)）付きなら **≤ e1(α)**（T3版）。
  閉包+2: 40,344 / 7,207 件 全0違反。
- 経緯: BT1-gen の V1（タイ+dom）/V2 は偽 → Chead の stop 像の計算で
  「stop = 窓の停止列 e0(j0+ω) ≤ e0(j0+α)」という**パラメータフリー形**を
  発見（ω=L で j1 に一致し元 BT1 を包含）→ V3 で成立 → タイ前提が冗長と
  判明（V3'）。
- 意義: (1) BT1/BT1_T3 を1本に統合（タイ前提も不要 — t1ok よりブロック内は
  **強い**規律: 停止の snd タイすら不要）。(2) X→M 帰納の FAIL 1426 件は
  全て BT1 の過特殊化が原因で、BT-WIN なら像が再び BT-WIN 形（窓パラメータ
  シフト）に落ちる見込み。(3) GBLK0・qpos も BT-WIN の系になる可能性。
- 次: (a) P族（フルコピー塊ブロック）の wrap 窓の像分析 (b) BT-WIN を
  Isabelle 凍結し BT1/BT1_T3 を置換 (c) GBLK0/qpos の BT-WIN 還元検証。

- (続45補) **BT-WRAP 確定**: 頭タイ（e1(α)=e1j0）＋全尾支配・stop なし形は
  **d0=0 でちょうど真**（閉包+2: 18,144/0；d0>0 は 2,319 違反 — α=0 で破綻）。
  T3版（頭隣接タイ）は d0 制約なしで 5,251/0。
  ⟹ ブロック内不変量の最終形 = **{BT-WIN（全d0・窓停止 e0(ω)≤e0(α)・タイ不要）,
  BT-WRAP（d0=0・頭タイ・全尾）}**＋各 T3 版。BT1/BT1_T3 は BT-WIN(ω=L) と
  BT-WRAP の系（d0>0/d0=0 で振り分け）。GBLK0 は anchor が prefix 列で別物
  （max 形が本質）— 凍結維持。
  次: Isabelle で ginv_BTWIN/ginv_BTWRAP を凍結し ginv_BT1/ginv_BT1_T3 を
  そこから導出（呼び出し側無傷）、X→M 帰納の像分析を BT-WIN 形で再走。

- (続45補2) **凍結スワップ完了（緑）**: ginv_BTWIN / ginv_BTWIN_T3 /
  ginv_BTWRAP / ginv_BTWRAP_T3 を凍結（全て閉包+2 監査済）、
  ginv_BT1 = d0 場合分け（d0>0: BTWIN(ω=L)+d0ex / d0=0: BTWRAP）、
  ginv_BT1_T3 = BTWRAP_T3 直系。事故録: str.replace が挿入直後の
  同一文面（BTWRAP 自身の末尾）を先に置換 → **領域スライス後に置換**が鉄則。
  sorry 24（±: BT1/BT1_T3 が導出に、BTWIN系4点凍結追加）。

### (2026-06-11 続46) ★★BTFULL 発見 — 世代コアの最終統一形と帰納閉鎖の確定

- **BTFULL**: bad-branch ホスト M・**任意アンカー a < j1**（prefix/block 不問）・
  窓 [a+1, ω)（ω ≤ j1）・dom: ∀q∈(a,ω): e0(q) > e0(a)・stop: e0(ω) ≤ e0(a) ⟹
  ∀q∈(a,ω): **e1(q) ≤ e1(a)+1**（タイ不要）。閉包+2: **63,999 / 0 違反**。
  BTWIN・BT1・接頭辞アンカー類を全て包含。
- **X→M 帰納の完全還元マップ**（oper-bad X の BTFULL インスタンス全数）:
  - アンカー prefix: BTFULL(M) 直 2,136/2,136 ✓（窓は prefix〜copy0 内で像が同一窓）
  - アンカー block・nowrap: BTFULL(M) 直（Chead 3,898 / Cmid 56 / P-in-block）✓
  - P-in-block・d0=0・stop@コピー頭: **BTWRAP(M)** 1,458/1,458 ✓（tie/domfull 全成立）
  - wrap 窓は実在 0（支配と停止が両立しない）✓
- ⟹ **BTFULL_oper_bad は {BTFULL(M), BTWRAP(M)} 供給で完全に閉じる**。
  残検証: BTWRAP(X)→M の像（次）と T3 版2本の同地図。閉じれば世代コアは
  {BTFULL, BTWRAP}±T3 の相互帰納1本（diag 空虚・take/butlast 制限・
  oper_bad = 上記マップ）に集約され、BTWIN/BT1/GBLK0?/qpos? が全て系になる。

- (続46補) BTWRAP(X)→M 像は不均一（tie/domfull 直還元 2,122 のほか
  NOtie 176・dompart 656・d0>0 434・prefix-anchor 714 が BTWRAP(M) 形に
  落ちない）。⟹ BTWRAP の oper_bad は M 窓還元でなく **X ブロック内容の
  直接展開**で証明する設計（X-block = M-block の snd 反復コピーなので、
  claim は「M-block snd の特定部分集合 ≤ e1(像アンカー)+1」という純 M 内容
  命題に等価 — その供給源（BTFULL(M) の別窓 or 新形）の特定が次の作業）。
  BTFULL 側の帰納は完全閉鎖済みなので、世代コアの残ピースは BTWRAP 閉鎖のみ。

- (続46補2) **BTWRAPGEN-d0=0 無条件成立**（閉包+2: 49,609/0）: bad-branch・
  d0=0・τ ≤ α・e1(α) = e1(τ)（τ は任意のブロック内タイ先！）・全尾支配 ⟹
  e1(尾) ≤ e1(α)+1。側条件（e0関係・τ支配）一切不要。d0>0 は (e0τ≤e0α ∧
  τ支配) に3,654違反で不均一 — d0=0 限定が真の境界。
  ⟹ BTWRAP 凍結を BTWRAPGEN-d0=0（τ 量化形）に置換すれば NOtie 像クラスを
  吸収できる見込み。dompart/prefix 像クラスの供給源特定が残タスク。

### (2026-06-11 続47) 世代コアの凍結階層 確立（緑）

- 凍結スワップ第2弾完了: **ginv_BTFULL**（ホスト全域形・63,999/0）凍結 →
  ginv_BTWIN を系へ（添字翻訳証明）。**ginv_BTWRAPG(+T3)**（τ量化 d0=0・
  49,609/10,179 全0違反）凍結 → ginv_BTWRAP を系へ。
- 現在の世代コア凍結（GRAND 最深層）:
  **{ginv_BTFULL, ginv_BTWIN_T3, ginv_BTWRAPG, ginv_BTWRAPG_T3, ginv_BTWRAP_T3,
  ginv_GBLK0, ginv_ob_qpos, t14ok_oper_bad}** ＋ sibm2 系シーム空クラス。
  BTFULL の oper_bad 帰納は {BTFULL(M), BTWRAPG(M)} 供給で完全閉鎖
  （続46 マップ）— 残るは BTWRAPG 自身の閉鎖（直接展開設計、続46補）と
  BTFULL_T3 の監査・帰納、そして相互帰納の Isabelle 実装。
- sorry 25。質的構造: 値側（NT_lexdiff_lt・fire-cascade 4・行レベル3・STS_B・
  スタブ3）/ 世代側（上記8+シーム空6）/ TOP_desc 未ステート。

- (続47補) **ginv_BTFULL_T3 凍結（39,939/0）・ginv_BTWIN_T3 系化（緑）**。
  世代コアの凍結最深層が {BTFULL±T3, BTWRAPG±T3, BTWRAP_T3, GBLK0, qpos,
  t14ok_oper_bad} に確定。BT 系の窓族は BTFULL±T3 と BTWRAPG±T3 の
  4本だけが真の凍結（他は全て系）。

- (続47補2) BTWRAPG(X) 供給源分類: anchor-copy 全 8,483 件が **contentOK**
  （被覆 M オフセット集合の e1 ≤ e1(像アンカー)+1 が直接成立；
  BTWRAPG(M) 直は 4,141、残りも内容では成立）＋ prefix-anchor 714。
  ⟹ BTWRAPG 帰納の供給源 = 内容レベルの **BWMAX 候補**:
  「（X-dom から誘導される M 条件下で）ブロック e1 群 ≤ e1(aM)+1」
  ＝アンカーがブロック row1 最大-1 以上に座る事実。最小前提の定式化が
  次の作業（wrap 被覆は全オフセットに及ぶため block-max との関係で書く）。
  prefix-anchor 714 は GBLK0 と同根（接頭辞アンカーの内容上界）。

- (続47補3) BWMAX 素朴形（強支配(aM,L)＋弱支配[0,aM)+d0 ± 任意タイ）は偽
  （4,614違反）。X インスタンスは d0X=0 という X の bad-params 構造
  （= X 最終列とその親のレベルタイ）を背負っており、その M 像（続44 の
  4族データ: j0X の像オフセット・族種別）が本質的前提。
  ⟹ BWMAX は**族別**（Clast: j0X=コピー末→次コピー丸ごと等）に定式化する。
  続44 の族写像と組み合わせ、各族で「X の d0X=0 構造 ⟹ M 側の具体条件」を
  抽出してから上界を述べる — 次セッションの主設計タスク。

- (続47補4) Clast 族 BTWRAPG(X) の M プロファイル: 全344件が d0M>0・
  (e0τ≤e0α ∧ τ支配) = BTWRAPGEN-d0>0 の違反プロファイル内で成立 ⟹
  識別子は **τM がブロック最終列 (L-1) 系**（j0X=コピー末の像）。
  族別事実 CLAST-BT（タイ先=最終列チェーン＋尾支配 ⟹ +1上界）の
  定式化・監査が次。残り族（Chead/Cmid/P/prefix-anchor）も同様の
  族別識別子抽出を続ける。

- (続47補5) CLAST-BT 素朴形（タイ先=L-1＋内部支配）も600違反。Clast 族は
  d0X=0 の M 像 **e0(L-1) = e0(L-2) + d0** などブロック端条件を持つ（j1X が
  次コピーの L-2 位置のため）。教訓: 族別事実の抽出は当て推量マイニングでなく
  **実例の M 条件全ダンプ → 違反例との差分で最小前提を機械的に特定**する
  手順で行う（次セッションの方法論）。BTWRAPG 閉鎖の作業在庫:
  Clast(344)/Chead系/Cmid系/P系/prefix-anchor(714) の族別最小前提抽出。

### (2026-06-11 続48) ★★★ユニバーサル BTFULL — 全ホスト不変量化（実装障壁の崩壊）

- **btfullok**: 任意の ST_PS ホスト M・任意の a < om < length M・
  dom: ∀k∈(a,om): fst(M!k) > fst(M!a)・stop: fst(M!om) ≤ fst(M!a) ⟹
  ∀l∈(a,om): snd(M!l) ≤ snd(M!a)+1。**bad-branch 前提一切不要**。
  閉包+2: 65,178/0。T3 版（snd(M!(a+1))=snd(M!a) ⟹ ≤ snd(M!a)）41,100/0。
  （以前の armchair 反例 (1,1)(2,5)(1,0) は r1ok の +1 規律で host に
  存在し得ない — 思い込みで棄却していた。マイニング第一の教訓再演）
- ⟹ **実装テンプレートが標準形に**: diag=空虚（fst 増加で stop なし）/
  take・butlast=窓の遺伝で自明 / oper_bad=続46 の閉鎖マップ
  （btfullok(M) 直 + BTWRAPG(M)）。bad-params 写像（oper4族・butlast5類）
  の分析は不要になった。
- 実装計画: btfullok±T3 定義 → 標準テンプレート（oper_bad 凍結）→
  ginv_BTFULL±T3 をそこから導出 → 続46 マップで btfullok_oper_bad 実装
  （t1ok_oper_bad の地図流用）。真の凍結残 = btfullok_oper_bad（マップ済）
  と BTWRAPG±T3 本体（族別）のみ。

- (続48補) **btfullok/btfullok3 実装完了（緑）**: 定義＋diag（fst増加で停止
  不能の空虚）＋take（窓遺伝）＋butlast＋dispatcher＋btfullok_ST_PS。
  oper_bad ×2 凍結（続46 マップで実装可能・地図済）。ginv_BTFULL±T3 は
  btfullok_ST_PS の instantiation に。BT 窓族の真の凍結 =
  **{btfullok_oper_bad, btfullok3_oper_bad, BTWRAPG, BTWRAPG_T3}** の4点
  ＋ BTWRAP_T3（d0自由 τ=0形）。

### (2026-06-11 続49) BTWRAPU 発見 — 世代窓族の最終縮約

- **BTWRAPU**: bad-branch・d0=0・e0j0 ≤ e0(j0+qa)・尾支配 ⟹ 尾 ≤ e1(qa)+1
  （**タイ不要**）。閉包+2: 21,537/0。BTWRAP（タイ形）の真の正体は
  「e0j0 ≤ e0(qa) 条件があればタイ不要」だった。
- btfullok_oper_bad の最終ケース地図（タイ依存なし）:
  A: om < j0+L → Xv0 転送 btfullok(M) / B: a<j0 反駁（j0∈内部 vs stop）/
  B: コピー内 om → shift 転送 btfullok(M) / B: om=次コピー頭 →
  d0>0: btfullok(M) om_M=j1（e0j1=e0j0+d0 転送）・d0=0: **BTWRAPU(M)** /
  B: om>次コピー頭 反駁。⟹ 真の凍結 = {btfullok(3)_oper_bad, BTWRAPU(3)}。
  さらに ginv_BT1 の d0=0 ケースも BTWRAPU で再導出可能（タイ未使用）→
  BTWRAPG±T3 は冗長化予定。

### (2026-06-11 続50) btfullok_oper_bad 討伐（緑）— ユニバーサル窓シーム閉鎖

- 続49 地図どおりの5ケース実装が一発系で通過: A=om<j0+L の Xv0 同値転送 /
  prefix アンカー反駁（j0∈内部 vs 停止レベル）/ 同コピー shift 転送
  （ko=ka を mult_le_mono1 ペアで強制）/ om=次コピー頭: d0>0 は
  e0j1=e0j0+d0 転送で btfullok(M) at om_M=j1・d0=0 は **ginv_BTWRAPU** /
  om>頭 反駁（star/stop の d0 算術衝突）。
- 事故録: 積原子の正規化は hN（h = j0+(L+ka*L)）と algebra_simps 正規形
  （(ka+2)*d0 → d0+d0+ka*d0）を事前定義してから arith。
  `show False if True` は不可 — `have False ... thus ?thesis ..`。
- 残: btfullok3_oper_bad（T3クローン）→ ginv_BTWIN系完全冗長化 →
  t14ok_oper_bad の btfullok 経由再設計の検討。

- (続50補) **btfullok3_oper_bad 一発クローン成功（緑）**。
  ユニバーサル不変量連鎖 btfullok±T3 が完全証明（残凍結 = BTWRAPU±U3 のみ）。
  BT 階層（BTFULL±T3 → BTWIN±T3 → BT1±T3）は全て {BTWRAPU, BTWRAPU3} の
  2点に立脚。BTWRAPG±T3/BTWRAP_T3 は冗長化候補（次の整理で再導出 or 削除）。
  世代窓族の本質的残課題 = **BTWRAPU±U3 の証明**（d0=0 正確コピーの
  ラップ上界 — 真の非因果核、コピー由来タイの世代帰納）。

- (続50補2) BTWRAPU(X) 供給源分類: U直 2,060 / btfullok@j1 90 /
  other 1,366 / prefix 714 — **ラップ核は M 窓還元で閉じない真の非因果核**
  と確定（コピー構築自体が事実を生成）。攻め筋候補:
  (a) X 構築の内容直接展開（X-block = M データ明示、ペア別 e0-e1 規律の抽出）
  (b) r1ok の row1 親チェーン経由（e1(o) ≤ e1(親)+1 鎖がアンカー近傍を通る
  構造の利用）(c) 強化同時帰納（btwrapu を ginv/t1ok 級の述語化して
  oper_bad 内で相互供給）。次セッションの主戦。

- (続50補3) **ginv_GBLK0 討伐（緑）**: 場合分け（≤e1j0 は自明 / >e1j0 は
  新凍結 **ginv_GAP**（246/0: 超過要素は snd(M!(j0-1)) が抑える））で分解。
  凍結規模 3,580→246 に縮小。qpos は btfullok の停止角度が合わず直系化
  不可（pp 停止と c0 停止の不一致）— 据え置き。

- (続50補4) **ginv_BTWRAPG±T3 を BTWRAPU±U3 から導出（緑）**: e0 条件は
  block_head_min で自動（qa=0 等号 / qa>0 真不等号）、τ タイは不使用と判明。
  世代窓族の真の凍結が **{BTWRAPU, BTWRAPU3}** の2点へ最終確定
  （＋BTWRAP_T3 は d0 自由 τ=0 形で別系統、BT1_T3 用に存続）。

### (2026-06-11 続51) 次セッション・バトルプラン（BTWRAPU 攻略）

状況: 世代側 GRAND の残凍結 = **{BTWRAPU, BTWRAPU3}**（d0=0 非因果核・
21,537/5,867 全0違反）+ GAP(246) + qpos(171 live) + t14ok_oper_bad(15クラス地図済)
+ BTWRAP_T3(d0自由 τ=0) + sibm2系シーム空6種 + 値側（NT_lexdiff_lt・
fire-cascade 4・行レベル3・STS_B・スタブ3・TOP_desc）。

BTWRAPU 攻略の3ルート（優先順）:
1. **r1 親チェーン×コピー周期**: d0=0 ⟹ ブロックレベル集合が完全周期。
   列 j0+q の r1ok witness 鎖はレベル毎に -1 し、tail-dom 下では
   level e0(qa) の witness が j0+qa 以前に着地。鎖の各段 +1 を
   コピー周期の「同型段」で相殺する補題（同レベル列の e1 同値性 —
   sibm2/STS_A 系）と組む。まず: instance dump で witness 鎖の着地点と
   e1 蓄積を表にする。
2. **内容直接展開**: btwrapu_oper_bad 型で X-block = M データ明示。
   X 側 d0X=0 と各位置の e0/e1 を M の (o, k) で書き、必要  peer 事実を
   差分最小化で抽出（方法論: 続47補5）。
3. **強化同時帰納**: btwrapu を述語化し btfullok と相互供給
   （oper_bad では btfullok_oper_bad の地図に乗せ、不足分を相互参照）。
教訓リマインダ: ∃ゴールは exI 明示 / metis・meson 多弾は禁止 / 積原子は
事前正規化 / dsplit は define 越し / 編集は絶対パス＋領域スライス / 
新凍結は閉包+2 監査後に固定。

- (続51補) ルート1 初回ダンプ（閉包+1・d0=0）: BTWRAPU 尾要素の r1 witness 鎖は
  **全件 j0+qa に着地**（left/inside ゼロ、chain1: 6,539 / chain2: 3,012、
  exc ≤ 1 全件）。⟹ 証明形: **LAND**（支配＋gap-clear から鎖がアンカーに
  着地 — 構造的に証明可能見込み、凍結不要）＋ chain1 は r1ok で即 ≤+1 ＋
  **chain2 のスラック**（2段で +1 に収まる — コピー双子段の e1 等値性が
  候補、要差分マイニング）のみが残る新事実。BTWRAPU 攻略は
  LAND + SLACK2 の2部品に縮約。

- (続51補2) SLACK2 段分布（閉包+1・chain2 全件 w1∈tail）:
  (d1,d2) ∈ {(0,0):1819, (0,-1):1156, (+1,0):25, (+1,-1):12} —
  **第2段 d2 = e1(w1)-e1(qa) ≤ 0 が無条件成立**（+1 皆無）。
  ⟹ BTWRAPU 証明 = **LAND**（鎖のアンカー着地・構造証明）+
  chain1: r1ok 1段 ≤+1 直 + chain2: 第1段 r1ok ≤+1・第2段 **SLACK2'**
  （アンカーを witness とする level+1 列で「上に子を持つ」ものは
  e1 ≤ e1(アンカー)— 子持ち条件が chain1(+1可) との分水嶺、次に正確文面
  マイニング）。非因果核がついに有限部品に分解された。

- (続51補3) ⚠閉包+2 精密化: HEIGHT≤2 は非絶対（h=3 が15件）、
  SLACK2'-child 形は **7違反で偽**。+1 プロファイル（chain≤2・着地全件）は
  サンプル狭隘 — 閉包境界教訓の再演。ラップ核の正体は「アンカー着地鎖に
  沿った exc ≤ 1」という鎖不変量そのもの（= BTWRAPU と同値）で、
  局所スラックでは分解しきれない。次セッション: 例外22件
  （h=3:15・child-viol:7）の実例精査から鎖不変量の正しい帰納形
  （鎖長帰納 or 強化同時帰納ルート3）を設計。LAND は依然有効部品。

### (2026-06-11 続52) ★ラップ核の最終分解 — BTWRAPU = LAND + 鎖帰納(r1ok+CT)

- **CT 成立（閉包+2: 7/7、違反0）**: アンカー着地鎖上のタイト節点
  （e1 = e1(アンカー)+1）の子は e1 ≤ e1(アンカー)（予算は鎖全体で1回）。
  child-viol の正体は「予算を第2段でなく第1段で使う」ケースで、鎖全体では
  常に ≤ +1 — チェーン不変量が正しい対象だった。
- **LAND は完全に構造的と確認**: 窓内要素 > e0a なので level-(e0a+1) 節点の
  witness（gap-clear 必須）はアンカーを飛び越せず必ずアンカー自身に着地;
  level の高い節点の witness も gap がアンカーで破れるため窓内に留まる。
  r1ok の witness 存在と合わせ、LAND は凍結不要の補題。
- **BTWRAPU 証明計画**: (1) LAND 補題（dom+gap の構造証明）
  (2) 鎖長帰納: 基底 = アンカー直子は r1ok で ≤+1 / 帰納段 = 親が非タイトなら
  r1ok、タイトなら CT で降下 (3) **凍結は CT 1点のみ（7件クラス）**。
  BTWRAPU3 も同型（headtie で基底が ≤0 になり、以後同帰納）— U3 用 CT 変種の
  監査を実装時に。
- 世代側 GRAND の残凍結見込み: **{CT, GAP(246), qpos(171), t14ok_oper_bad}**
  ＋シーム空6種 — BTWRAPU±U3 が落ちれば窓族は完全終結。

### (2026-06-11 続53) 🎉ginv_BTWRAPU 討伐（緑）— 非因果核の陥落

- 実装 = 設計どおり: **LAND**（witness はギャップでアンカーを飛び越せない —
  kanch: k < j0+qa なら gap が j0+qa（低レベル）を含み矛盾、k=anchor は
  r1ok 直、k>anchor は窓内で IH）＋ **位置 less_induct 強帰納**（witness
  k < x が測度）＋ 分岐: 親 e1 ≤ アンカー → r1ok 段 / 親タイト → **ginv_CT**。
  r1ok_ST_PS（証明済）を witness 供給に使用 — r1ok 基盤の完成が effectively
  ここで効いた。
- 凍結は **ginv_CT（7件クラス）のみ**。BTWRAPU の 21,537 件級が 7 件級へ。
- 残: ginv_BTWRAPU3（T3 版 — headtie 基底の同型鎖帰納、CT3 変種の
  監査が必要）→ 落ちれば窓族完結。

- (続53補) **🎉ginv_BTWRAPU3 討伐（緑）— BT 窓族完全終結**:
  BTWRAPU(≤+1) ＋ 新凍結 **ginv_NT3**（headtie 下の +1 到達は空クラス、
  16,783 件中 0）の2行組立。
  **窓族の最終凍結 = {ginv_CT(7件), ginv_NT3(空), ginv_GAP(246件)}**
  ＋ BTWRAP_T3（d0自由 τ=0・5,251/0）。btfullok±T3・BTWIN±T3・BT1±T3・
  BTWRAPG±T3・BTWRAPU±U3・GBLK0 は全て導出/証明済み。
  世代側 GRAND 残: CT/NT3/GAP/BTWRAP_T3/qpos/t14ok_oper_bad ＋ シーム空6種
  — 全て微小クラスか地図済み。

### (2026-06-11 続54) 本日総括＋次セッション開幕指針（compact 引継ぎ）

**本日の戦果（19討伐・★6発見・健全性キャッチ2件）**:
seam_copyhead_m1(+L2) / r1ok_climb / E6_nbcK_T / E6_tie_nofire_high0+high1 /
ginv_ob_pre+ob_copy / t1ok+t3ok_oper_bad / BT1+BT1_T3系化 / BTWIN系化 /
BTWRAPG系化 / GBLK0 / btfullok+btfullok3_oper_bad / BTWRAPU+BTWRAPU3。
新基盤: ginv・t1ok/t3ok/t14ok・btfullok±T3（全て標準テンプレート緑）。
健全性: t14ok を hi 前提付きに弱化（閉包+2 反例36）/BTWRAPG_T3 は無事。

**nrmstep.thy sorry 23 の内訳**:
- 世代側微小: ginv_CT(7件) / ginv_NT3(空) / ginv_GAP(246件) /
  ginv_BTWRAP_T3(d0自由τ=0・5251/0) / ginv_ob_qpos(171 live・e1j1経由候補) /
  t14ok_oper_bad(15クラス地図済・続43補2)
- シーム空: seam_open_m1 / copyhead P・E2var・F2L2 / copyhead_deep（実証0）
- 値側（次の主戦線）: NT_lexdiff_lt(0/116万) / E6_lpl / E6_dom_deep /
  E6_memT(前提空) / E6_nbcK_K / E6_qcut_last / E6_iii_singleton / E6_seam /
  STS_B(0/26322) / スタブ NT_tie・E6_mem・E6_dom_tie（resolved 版あり・
  最終組立=1本の同時長さ帰納）。nrm.thy: nrm_order_pres。TOP_desc 未ステート。

**次セッションの優先**: (1) 値側戦線の再開 — E6_qcut_last/iii_singleton/seam
を btfullok/t1ok 新兵器で攻める（続26計画の完成形）(2) CT/GAP の世代帰納
（微小クラス・同テンプレート）(3) qpos は e1j1 経由（M窓に j1 含む形・
続37補）。教訓集は続51。ビルド: isbman build -m MSG
-d /home/koteitan/afp-dl/afp-2026-06-05/thys -d /home/koteitan/proofs/ya-pss/git PSI。

### (2026-06-11 続55) 値側戦線プローブ開始 — E6_iii_singleton

- 実例43件: 全て |S|=1 ✓、形一様（q は単一列 c に対し fst>・snd>）。
  証明形候補 = 対偶「|S|≥2 ⟹ (fire(S@[q]) ⟹ fire(S))」: snoc 橋
  （nrm_snoc_seg・ins_olt_mono 等の緑部品）で q の寄与する新違反者を
  S 側に移送する論法。次: |S|≥2 ∧ ¬fire(S) ∧ fire(S@[q]) の「あと一歩」
  反例ダンプ（fire の違反者 g の所在を S/q 寄与で分類）。

- (続55補) iii 対偶監査 ✓: **|S|≥2 ∧ fire(S@[q]) ⟹ fire(S)**（閉包+1:
  2,267/0）。E6_iii_singleton = この fire-butlast 安定性（FBS）1点に帰着。
  FBS の証明 = 違反者 g の snoc 移送（Gterm の snoc 分解と NT(S@[q]) vs
  NT(S) の olt 橋 — nrm_snoc_seg/ins_olt_mono の緑部品圏）。次セッションで
  FBS を凍結 or 直証して iii を落とす。qcut_last/seam も同じ fire-snoc
  移送圏の見込み。

### (2026-06-11 続56) E6_iii_singleton 討伐（緑）— 値側行レベル初討伐

- **E6_FBS 凍結**（fire の butlast 安定性・一般 q 形・閉包+2: 5,370/0）→
  iii は対偶2行で落ちた。FBS は次に qcut_last/seam でも主部品の見込み。
  値側討伐は本日20点目。

- (続56補) qcut_last/seam 閉包+2 再確認（12/0・5,358/0）。qcut は実例12件の
  微小クラス。両者の証明は fire/msfx 機構設計（FBS と同圏だが msfx の
  位置情報が要る — FBS だけでは落ちない）。次セッション: qcut の12実例
  ダンプから msfx=last の機構特定 → seam は head-min を btfullok 系で。

- (続56補2) qcut 12実例ダンプ: **全て厳密増加対角**（S=(v+1,u+1)(v+2,u+2)…・
  q 続き）。snd 厳密増 ⟹ msfx=[last] 自明。⟹ 縮約凍結候補 **QDIAG**:
  「qcut 前提（両 fire ∧ maxr1 S < snd q）⟹ S の snd は厳密増加」—
  これさえあれば qcut_last は純リスト論証。次セッションで QDIAG 監査→
  qcut 討伐。

### (2026-06-11 続57) E6_qcut_last 討伐（緑）

- **E6_QDIAG 凍結**（qcut 前提〔segprov・S≠[]・両 fire・maxr1 S < snd q〕
  ⟹ snd(S!i) < snd(S!Suc i)。閉包+2: 12/0、実例12件は全て厳密増加対角）。
- qcut_last 本体は純リスト論証で完落ち: QDIAG → 位置単調帰納
  （∀i≤j. snd(S!i) ≤ snd(S!j)）→ maxr1 S = snd(last S)（Max_eqI）→
  butlast 全要素 < maxr1 → msfx S = dropWhile … (butlast S @ [last S])
  = [last S]（dropWhile_append2）。ビルド36秒緑。
- 値側行レベル残り = **E6_seam**（5,358/0・msfx の head-min 不変量を
  btfullok/FBS 機構で設計）。sorry 数 23（qcut の sorry が QDIAG 凍結に
  置換・正味同数だが監査済み微小クラス化）。

### (2026-06-11 続58) E6_seam 分割 — q 脱結合凍結核（緑）

- 採掘結果（mine_seam2〜6）: msfx は最大45列で qcut 型の縮小は不可。
  fire 前提なしでは反例（INV2: 70件）→ fire が本質。FDIAG（fst 非減少）は
  135件で不成立 → 結論の単調化も不可。
- **前提最小化が当たり**: same-cut 窓では fire(S) ⟺ fire(S@[q])（実例集合が
  完全一致）で、fire(S) 単独で両結論が出る。さらに q 条件を外した一般形が
  成立:
  - **seam_MIN**: segprov 区間が fire ⟹ hd(msfx S) は msfx S の fst 最小
    （閉包+2: **458,980/0**。q 自由・カット条件不要）
  - **seam_INV**: ＋same-cut（snd q ≤ maxr1 S）⟹ fst(hd(msfx S)) ≤ fst q
    （閉包+2: **426,489/0**）
- E6_seam 本体は2行導出に。監査基盤 5,358 → 458,980 へ86倍強化、
  both-fire 結合が前提から消えた（世代帰納時の負担減）。sorry 数 24
  （seam 1個 → 凍結核 2個、正味+1だが圧倒的に強い凍結）。
- 値側行レベルは全て凍結核化完了。残る値側 = NT_lexdiff_lt（116万ペア/0・
  深い値機構）、fire カスケード（E6_lpl/dom_deep/memT/nbcK_K）、STS_B、
  nrm_order_pres、最終組立。

### (2026-06-12 続59) 最終組立の SCC 完全地図 — 組立は端末フェーズに延期

- 引用グラフ機械抽出の結果、スタブ循環の SCC は予想より深い:
  **NT_shape が NT_dom（→NT_tie スタブ）を直接引用**しており、
  NT_shape/NT_hd/Gterm_NT_high/GCAT/E6_nbcK など NT 構造層が全て循環に参加。
  さらに mem(n)→nbcK(n)→Gterm_NT_high(n)→NT_shape(n)→NT_tie(n)→(resolved
  本体)→hdom(<n) と「同長で呼ぶ」鎖が多数 → 同長で呼ばれる補題は全て束行き。
- 完全束 = {NT_tie, NT_dom, NT_shape, NT_hd, Gterm_NT_high, GCAT, E6_nbcK,
  E6_mem, E6_dom_tie, E6_value, E6_hdom, NT_prefix_lt, ST_snocokS_gen,
  ST_snoc_C, ST_snocok_gen, (nrm_snoc_mid inline), + ヘルパ
  （Gterm_NT_hdsub_le/olt_msfx_lowsub/NT_msfx_hdsub 等 NT_shape 引用組）
  + 凍結葉 conjunct（lpl/dom_deep/memT/nbcK_K）} ≈ 20+ メンバー・2,500行級。
- 層化は ≤n 形 IH で健全（NT_tie(n)→hdom(≤n-2) 等、全て小さい側に降りる）。
  ステップ内順序: tie→dom→shape→hd→high→GCAT→PL→hdom→dom_tie→nbcK→mem→
  value→SGS→SC→SG。
- **判断**: 凍結葉の将来証明は束メンバー化する見込みが高く、9メンバー部分
  組立（mem/dom_tie の2 sorry 削減のみ）は端末で作り直しになる無駄足。
  ⟹ 組立は全葉討伐後に一度だけ実施。当面は凍結葉の討伐を継続。
- 次の標的: E6_lpl（head-max 全体 vs 後続同添字可視片、可視性前提付きで
  0違反/続25補4）。採掘で実例構造（C の形・位置）を特定し、縮約 or 直証。

### (2026-06-12 続60) G6 統一支配核 — dom_tie/dom_deep/lpl の3点を1凍結に統合（緑）

- 採掘経過（mine_lpl2/lpl3/g6/g6u/g6f/g6f2/g6h）:
  - lpl の弱窓（非隣接支配・u自由）監査は可視性込みでも反例 110,273 —
    **u は隣接 pp の snd でないと偽**。正確な dseg では 0/103,565 ✓。
  - 統一仮説 **G6**: dseg u S ⟹ 可視 g（hdsub g = maxr1 S）⟹
    ole g (NT(msfx S))。**fire・head-max・violator 前提すべて不要**。
    閉包+1: 0/128,657、**閉包+2: 0/711,342**（窓 460,931）— 本計画最強の監査。
  - 一般化限界の地図: u=0 一様化 ✗（84,795）、fbseg（mid-gap、真の定義の
    mid≥hd 条件込み）✗（10,586）、head-min fbseg ✗（90,681）。
    exact dseg（stepsok による fst(hd S)=fst pp+1 強制＋到達可能性）が本質。
    T側降下は self-msfx 比較では偽 — memT 型の「全体閾値渡し」が必要
    （将来の G6 本体証明の設計指針）。
- 帰結（ビルド31秒緑）:
  - **E6_dom_tie スタブ = G6 の直接系**（2行）— スタブ討伐。
  - **E6_lpl = G6 + head-max ⟹ msfx S = S + Gterm_size 厳密化**
    （前提を snd(hd C) → hdsub(NT C) 形に差替、hdom 呼び出し側は w(4) で供給）。
  - **E6_dom_deep・E6_dom_tie_resolved は削除**（G6 が包摂）。
  - sorry 24 → 22。値側の支配系は E6_G6 1点に立脚。
- 残値側: E6_G6 本体・seam_MIN/INV・FBS・QDIAG・STS_B・NT_lexdiff_lt・
  E6_memT・E6_nbcK_K・E6_mem スタブ（mem_resolved あり・組立待ち）・
  NT_tie スタブ（resolved あり・組立待ち）・nrm_order_pres。

### (2026-06-12 続60補) QDIAG 前提弱化（緑）

- mine_qdiag2: q-cut 配置で fire(S@[q]) 単独 ⟹ snd 厳密増（閉包+2:
  **0/32,491**、both-fire 形の6倍基盤）。fire なしは 20,819 違反で fire が
  本質。E6_QDIAG の前提から fire(S) を削除（qcut_last 呼び出し側は
  assms(1,2,4,5) に調整）。

- (続61補) CT 剛性採掘の結果（閉包+2・i1=0 ブロック 15,279件）:
  - **i1>0∧d0=0 の bad ブロックは完全空（n1=0）** — i1=1 ⟹ d0≠0 は
    nextrel1 の構造から証明できる見込み（CT の i1>0 ケースはブロック
    レベルで真空化可能）。
  - **B7v=0**: 内部アンカー（qa≥1）の CT 窓は空 — CT は qa=0（アンカー=j0）
    のみ。B5a（j0+1 バンプ ≤ Suc(snd j0)）も 0違反。
  - B5'（j0+1 以降 snd=0）は 305 違反、B6（j0+1 以降 ≤ snd j0）も 260 違反
    — snd(j0)=0 でも深い振動 (7,1)(7,0)(8,1)(7,0)(8,1)… が存在。
  - 振動例の検証: tight w は深い位置にも立つが、**gap-clear 子 x が
    振動の低列に遮られて存在しない**（CT は子条件で真空化）。
    ⟹ CT の本質 =「gap-clear 子の存在 ⟹ w=j0+1 強制」型の振動勘定で、
    BTWRAPU 級の専用窓設計が必要。実例7件は全て w=1/x=2/ブロック長3。
  - 当面 CT は凍結のまま。次: E6_memT / STS_B の前提最小化採掘へ。

### (2026-06-12 続62) E6_memT 空クラス再確認 / STS_B 分解地図

- E6_memT: exact dseg 窓では前提（max が T 側に厳密集中）が実現せず
  **n=0**（既知の前提空を mine_memt.py で再確認）。空クラス凍結のまま。
- **STS_B 分解採掘（mine_stsb.py, 19,865 配置）**:
  - part1（vs NT T）: 0違反 — NT_shape 展開で **NT_dom と同内容**
    （hdsub(NT T)=snd c1・hdarg=proj(snd c1)(NT K1)）。
  - part2 nojoin（q がhd T のランに合流しない）: **hdarg(NT(T@[q])) =
    hdarg(NT T) が全件成立（Q2=0）** — takeWhile_append1/2 の純リスト
    論証で part1 に転送可能。
  - part2 join（rest1 全上昇 ∧ fst c1 < fst q）: 5,624件・0違反 —
    **真の凍結残差はこの join ケースのみ**。
  - ただし part1 の導出には fbsegD 版 C1 層（pair_host/SIB_shape2/
    NT_dom 鎖 = NT_tie 含む）が必要 — NT_tie スタブ解消（最終組立）後に
    実施が適切。STS_B は当面凍結のまま、この地図を将来の討伐設計に使う。

### (2026-06-12 続63) TOP_desc ステート（緑）— 未ステート問題解消

- mine_topdesc/topdesc2: 隣接トップ木対（fst=0 根）の弱降下
  ole (NT K1) (NT K)。K1 は**次木の任意非空先頭部分**でよい（prefix 弱化・
  post 条件不要）。閉包+1: 0/678、**閉包+2: 0/967**。
- nrmstep.thy の nrm_step_dec_pred 直前に凍結ステート（ビルド緑）。
  これで「TOP_desc 未ステート」リスクが消え、**全 sorry が監査済み文面**に。
- nrm_order_pres はクリティカルパス外と確認（続63補）: PSS_terminates_nrm
  は nrm_step_dec のみ必要で、nrmstep の直接証明が閉じれば order_pres は
  削除可能（wf_Rnf_nrm 経路は冗長な強い版）。

- (続63補) **ginv_GAP 偵察**: 286実例（閉包+2）が**完全剛性** —
  全件 (i1=0, snd pp=1, snd j0=0, 超過列 snd=1)、ホストは CT の B6-fail と
  同じ深振動ブロック (7,1)(7,0)(8,1)(7,0)(8,1)…。
  ⟹ **CT と GAP は同じ振動規律の双子**（d0=0 ブロックの interior bump は
  ちょうど s0+1・bump 存在 ⟹ 支配前任 snd ≥ s0+1・tight 子は gap-clear
  不能 or 降下）。次の世代側戦役 =「振動規律 OSC」一本で CT+GAP 同時討伐。

### (2026-06-12 続64) 次セッション開幕指針

- **sorry 現況**: nrmstep.thy 23（全て閉包+2監査済み文面）+ nrm.thy
  nrm_order_pres 1（クリティカルパス外・直接証明が閉じれば削除）。
- 値側凍結核: E6_G6（711,342/0・dom_tie/lpl は系）/ seam_MIN（458,980/0）/
  seam_INV（426,489/0）/ E6_FBS（5,370/0）/ E6_QDIAG（拡張fire単独
  32,491/0）/ STS_B（残差=join 5,624件のみ・地図続62）/ NT_lexdiff_lt
  （116万/0）/ E6_memT（空）/ E6_nbcK_K / TOP_desc（967/0）。
- スタブ: NT_tie / E6_mem（resolved あり・最終組立待ち・SCC地図続59）。
- 世代側凍結核: CT(7)+GAP(286)=振動規律双子（続61/63補）/ NT3(空) /
  qpos(171・e1j1経由=続37補) / t14ok_oper_bad(15クラス地図=続43補2) /
  BTWRAP_T3 / シーム空クラス（open_m1 14件・copyhead残差 P/E2var/F2L2 空・
  copyhead_deep 空）。
- **優先順位案**: (1) 振動規律 OSC の設計（CT+GAP 同時・B7v/i1>0空/B5a は
  監査済み部品）(2) G6 本体の再帰設計（T側は全体閾値渡し・seam_MIN が
  K側で合成可能・wf3 OT3 部品あり=続60採掘）(3) qpos/t14ok の既地図実行
  (4) 最終組立（全葉後・メガ束）。
- 方法論リマインド: 前提最小化採掘が強力（fire 片側だけ等）。新凍結は
  閉包+2 必須。教訓 = 続51。

### (2026-06-12 続65) OSC 再構成（緑）— CT/GAP を純ブロック凍結核3点に還元

- **nextrel1_e0_lt 証明**（rtran_nextrel0_e0 + tranclpD 分解）:
  nextrel1 の le0 真先祖鎖は e0 厳密増 ⟹ **i1>0 ∧ d0=0 は矛盾**
  （CT/GAP の i1=1 ケースは完全証明で真空化、凍結不要）。
- **OSC 凍結核3点**（i1=0 ブロック・純ブロック事実・窓配管なし）:
  - ginv_O1: 内部 row1 ≤ Suc(head)（閉包+2: **15,279 ブロック/0**）
  - ginv_O2: バンプ存在 ∧ 頭が直前列に支配 ⟹ 直前列 ≥ Suc(head)（158/0）
  - ginv_GCD: 正 row1 内部列の gap-clear level+1 子は row1 厳密降下（7/0）
- **ginv_GAP = O1+O2 の純算術導出**（O1 で超過=ちょうど+1 に固定→O2）、
  **ginv_CT = GCD 単独の導出**（tight ⟹ 親正・アンカー解析完全不要！）。
- sorry 22→24 だが（CT/GAP 2 → O1/O2/GCD 3 + α）、凍結核は全て生成帰納
  しやすい純ブロック形・監査基盤は 246/7 → 15,279 ブロック級に強化。
  ビルド32秒緑。

- (続65補) **ginv_O1 討伐（緑）**: O1 は**証明済み ginv_BTWRAPU の qa=0
  インスタンス**だった！ dom 前提は nextrel0 の gap 条件（∀j∈(j0,j1):
  e0(j)≥e0(j1)>e0(j0)）から導出。ファイル順序の障害（O1 が BTWRAPU より
  前）は GCD→CT→NT3→BTWRAPU→BTWRAPU3 ブロック（依存 = r1ok/CT のみと
  機械抽出で確認）を OSC の上に移動して解決。sorry 24→23。
  OSC 残凍結 = O2(158/0)・GCD(7/0) の2点のみ。

- (続65補2) **ginv_BTWRAP_T3 分割（緑）**: i1=0 主部（閉包+2: 20,699件・
  e0c 違反0）は **BTWRAPU3 + nextrel0-gap 導出**で証明。残差凍結 =
  ginv_BTWRAP_T3_pos（0<i1 上昇枝・**6件/0**）。世代側残凍結 =
  O2(158)/GCD(7)/NT3(空)/BTWRAP_T3_pos(6)/qpos(171)/t14ok_oper_bad(地図済)
  ＋シーム空クラス。

### (2026-06-12 続66) seam_open_m1 偵察 — first-diff 一様クラスと閉事実3点

- mine_openm1: 開ランシーム実例 **202件**（閉包+1・旧メモの14件は別数え）が
  **完全一様**: 全件 (i1=0, d0=0)、D≠B だが sibrel は**第3分岐
  （first-difference 降下）で全件成立**:
  - F1: fst(hd D) = fst(hd B) + 1 = e0(j0)+1、snd(hd D) = 0
  - F2: e1(j0) = 0（「e1j0=0 機構」の正体 — hd B = (e0(j0), 0) と snd タイ）
  - F3: K・K1 = tail@B とも頭最大（snd 全0系）
  ⟹ 共通接頭辞 = tail、分岐点 = len(tail)、fst 1降下＋snd タイで
  sibrel 第3分岐。証明 = F1/F2/F3 の世代事実 + 位置代数（copyhead_m1 の
  テンプレート流用可）。i1=1 は実例0。
- 実装は次セッション: F1〜F3 を凍結 or 直証（F2 は d0=0/i1=0 ブロックの
  head snd — O 族と同根の可能性）、sibrel 組み立てはリスト代数。

### ★★(2026-06-12 続67) 重大健全性キャッチ — sibm2/sibrel は閉包+3 で偽

- **発見経路**: seam_open_m1 の再構成採掘で closure+2 監査が 18反例を検出
  （F1〜F3 一様性は closure+1 の錯覚 — +2すり抜けの4例目）。さらに反例
  ホストの M[2]（closure+3 圏）で **sibm2 自体が偽**:
  M = (0,0)(1,1)(2,0)(3,1)(4,0)(5,1)(3,1)(4,0)(5,1)(3,1)(4,0)(5,1)（到達可能）
  の M[2] で対 (a=6,b=9): K=[(4,0),(5,1)] vs K1=[(4,0),(5,0)] —
  first-diff 降下形だが **K の頭が max でない**（hd=(4,0) snd0 < maxr1=1）
  ⟹ sibrel 第3分岐の head-max 条件が偽 ⟹ sibm2(M[2]) = False。
- **sibm2_ST_PS は偽**（証明は偽凍結 seam_open_m1 経由で「通って」いた）。
  続29 の修復 sibrel もまだ強すぎた。
- **被害評価（緊急検証済み）**:
  - 最終減少 olt(NT(M[n]), NT(M)) は反例ホスト全てで**成立** ✓（本丸無傷）
  - **NT_tie 結論も反例対で成立** ✓（projK = D0(D1) vs projK1 = D0(D0)、
    ¬olt ✓）⟹ 偽なのは sibrel 抽象だけ。修復 = sibrel 第4分岐
    （head-max なし first-diff・尾は climb 形）追加 + sibm2_oper_bad 再戦
    + NT_tie_resolved の第4分岐ケース（新値補題）。
- **方法論更新（最重要）**: コピーシーム系の凍結は closure+2 でも不足
  （本件は closure+3 で初出）。**全凍結文面の closure+3 再監査が必須**。
  以後、シーム/sibm2 系freeze は +3 を標準とする。

- (続67補) **sibrel 修復設計確定**: 違反162対は完全一様 —
  「**K 末尾での fst 等値 snd 降下**」（K = p@[x], K1 = p@x1#r1,
  fst x1 = fst x, snd x1 < snd x、head-max 不要）。
  **sibrel4 = 旧3分岐 + 第4分岐（末尾 snd 降下）: 0/729,131 対
  （closure+3 95,182 ホスト全タイ対）**で監査クリア。
- 修復実装計画:
  1. sibrel 定義に第4分岐追加（nrmstep.thy）
  2. sibrel を「供給」する側（sibm2_diagSeq/oper_bad シーム群）は disjunct
     追加なので既存証明は原則無傷（弱化方向）。偽だった seam_open_m1 系の
     残差クラスは第4分岐で再分類（要再採掘）
  3. sibrel を「消費」する側に第4ケース追加: sibrel_trunc（打切吸収）と
     SIB_shape2→NT_tie_resolved。NT_tie の第4分岐ケース = 末尾 snd 降下対の
     proj 比較 — **新値補題（NT_enddrop）の採掘・凍結が必要**
     （反例対で projK=D0(D1) vs projK1=D0(D0)、¬olt 成立確認済み）
  4. 全シーム系凍結の closure+3 再監査（実行中: /tmp/c3_all.out）

- (続67補2) **closure+3 全凍結再監査 — sibm2 系以外は全てクリア**:
  G6 **0/3,447,851**（窓1.99M）/ seam_MIN 0/2,707,846 / seam_INV
  0/2,556,336 / QDIAG(P2形) 0/151,510 / O1 0/56,565ブロック / O2 0/489 /
  GCD 0/61 / BTWRAP_T3(i1=0 e0c) 0/83,606・_pos 0/60。
  クラスは成長（GCD 7→61 等）したが違反ゼロ。偽は sibrel/sibm2 系のみと
  確定（修復中）。TOP_desc/STS_B/FBS/lexdiff の +3 は次バッチ。

### (2026-06-12 続68) sibrel4 修復キャンペーン — WIP（ビルド赤・修復続行中）

- 完了: sibrel 定義第4分岐 / sibrel_trunc 全面書換（consider 4分岐・緑見込）/
  NT_enddrop 凍結（branch-4 対 NT 厳密降下・closure+3到達 2,403/0）/
  NT_tie_resolved 第4ケース（nfK/nfK1 は head-max 不要なので proj は
  そのまま消え、NT_enddrop で閉じる）。
- ★スタック原因特定: **elimination 型 consider（旧3形列挙）** が
  4分岐定義に対し blast 発散。ビルドは isbman kill 不可（classifier）→
  TaskStop で自分の bash ごと停止する運用。
- **残修復ワークリスト**（elimination サイト12箇所）:
  1. sibrel_nopref (6284): 第4ケース = nth 衝突で機械的クローン
  2. sibrel_ascent (6313): 同・lx ケースの p'位置場合分けクローン（r'=[]）
  3. **sibrel_diverge (6373): 結論の弱化が必要** —
     「(降下∧両hm) ∨ (r=[] ∧ fst等値 ∧ snd降下)」へ。
     呼び出し側 7298/7598/8000/8455 に新ケース伝播
  4. shf_sibrel (6500前後): branch-4 は shift で形保存・機械的
  5. seam_open_copyhead (7930/8046 + diverge 呼び出し)
  6. seam_open_blift (8309〜8497 多数 + diverge 呼び出し)
  7. sibm2_snoc_copy (9146)
- 修復方針: nopref/ascent/shf は機械クローン→先に処理。diverge は弱化＋
  伝播（呼び出し側の新ケースでは構築目標も branch-4 で供給できるはず —
  コピー転送は形を保存するため）。

- (続68補) 修復進捗: sibrel_nopref/ascent/shf_sibrel に第4(ed)ケース追加
  （機械クローン・nth衝突/シフト保存）。**sibrel_diverge を弱化**:
  結論 = (降下∧両hm) ∨ **(r=[] ∧ fst等値 ∧ snd降下)**、ed ケースは
  位置一致 p'=p（append_eq_append_conv）から r=[] を導出。
- 残り = diverge 呼び出し4箇所の新ケース（各ローカルゴール対応）:
  - 7354圏（seam_E系）: div を conjunction で受けている → 場合分けに変更、
    end側: D 単集合・fst(M!j1)=fst(hd D)・snd降下 の下でローカル反駁/構築
  - 7654圏: dK = []@M!(Suc a)#tl K — end側: tl K = [] (K 単集合)
  - 8056圏 (blift m=1): hmM のみ消費 — end側では hmM が無い → 別経路
  - 8511圏 (blift m=0): 同上
  + seam_open_copyhead (7930/8046 elim) / seam_open_blift (8309-8497 elim) /
    sibm2_snoc_copy (9146 elim) の consider 4分岐化。

- (続68補2) 呼び出し側修復 1/2 完了:
  - **site1 seam_copyhead_m1_L2**: div を弱形に・3-way consider
    （F1/F2 に hm を運搬・note で再束縛）・ED = branch-4 直接構築
    （K=blktail@[hd D]・C1頭 (e0j1,e1j0) と fst等値・snd降下は
    e1j+ED(3) を linarith 連鎖）。
  - **site2 seam_copyhead_m1**: 同型・ED = K=[M!(Suc a)] 単集合 vs [xx]
    の branch-4（desc は F1 と同じ Mj1f/Mj1s/e1j 導出）。
  - **site3/4（seam_open_copyhead 8093 / seam_open_blift 8548）は保留**:
    diverge 消費が hmKC 補助（bigle）の内部にあり、ED では hmKC 自体が
    偽になり得る ⟹ micro-patch 不可、**lxf ケースレベルで branch-4 脱出**
    （M側 core が branch-4 形なら Y側転送対も branch-4 形で目標 sibrel を
    直接構築）に再設計が必要。seam_open 複合体（copyhead/blift/m1凍結）の
    一体再設計として次に実施。残 elim: copyhead/blift 内 consider 群・
    sibm2_snoc_copy (9146圏)。

### (2026-06-13 続69) sibrel4 修復 — ビルド緑チェックポイント到達

- ビルド緑（19秒）。修復完了分: sibrel 定義第4分岐 / trunc 4分岐書換 /
  NT_enddrop 凍結(2,403/0) / NT_tie_resolved 第4ケース / nopref・ascent・
  shf_sibrel 機械対応 / diverge 弱化(ed: r=[]) / 呼び出し site1
  (copyhead_m1_L2)・site2 (copyhead_m1) = ED は branch-4 直接構築。
- **一時凍結**: seam_open_copyhead / seam_open_blift（旧緑証明は git 履歴・
  lxf 内 diverge 消費に branch-4 脱出が必要 = 再設計対象。statement は
  sibm2 closure+3 監査 0/729,131 の傘下で真）。
- sorry 26（+NT_enddrop+copyhead+blift の一時分）。
- 次: (1) seam_open 複合体の branch-4 再設計（一時凍結2点の復旧・
  edf ケースは Y側 K1@C 拡張で自明、M側 ed2 は |p| vs |P0@blk| 場合分け
  の純リスト代数 — 設計済み続68補2）(2) sibm2 系シーム凍結
  （open_m1/copyhead 残差/deep）の closure+3 再監査と文面再採掘
  (3) 健全性総点検: 全 sorry 文面の sibrel4 下での意味再確認。

### (2026-06-13 続70) sibrel4 修復キャンペーン完全完了（緑・一時凍結ゼロ）

- **seam_open_copyhead / seam_open_blift を本復旧**（一時凍結解消）:
  - lxf ケースを m 分岐外側に再構成: 通常側（copyhead: 1<m / blift: Suc）は
    旧 hm 論理、diverge 側（m=1 / m=0）は弱化 diverge の hOK/hED 分岐 —
    **hED は K=p@[x]（r=[]強制）+ K1@C 拡張で branch-4 即構築**。
  - SYf consider に edf（Y側 branch-4）追加 — K1@C = p@x1#(r1@C) で自明。
  - blift pref/m0 の coreM consider に ed2 追加 — r1=[] は butlast/last で
    branch-2、r1≠[] は butlast 代数で branch-4。metis→blast。
- sorry 24 = 修復前 23 + NT_enddrop（branch-4 値降下・closure+3到達 2,403/0）。
  **健全性事件（続67）は文面・証明とも完全解決**。ビルド28秒緑。
- 残 TODO（次セッション）: (1) sibm2 系シーム凍結（seam_open_m1/copyhead
  残差 P・E2var・F2L2/copyhead_deep/STS_B 等）の文面を sibrel4 下で
  closure+3 再採掘（open_m1 は sibrel4 で 202/0 確認済・+3 再確認要）
  (2) 全 sorry 文面の sibrel4 意味総点検 (3) その後通常戦線へ復帰
  （続64 優先順位）。

### ★(2026-06-13 続71) sibrel4 も closure+4 で破れる — sibrel 設計の根本問題

- audit_seam_c3（+3・sibrel4 下）: open_m1 結論 **69違反/5,447**・copyhead P
  クラス **空でなく261件**・E2var/F2L2 空維持・deep 45件0違反。
- 違反解剖: M[2]（+4圏）で K=[(6,1),(7,0)] vs K1=[(6,1),(6,1)] —
  divergence は K 末尾だが **fst降下+snd上昇**（branch-4 は fst等値要求で
  不適合）。つまり sibrel の有限分岐リストは**コピー力学で閉じず**、
  リング毎に新形状が湧く。
- **価値レベルは安定**: NT_tie 結論 ✓（D1(D0) vs D1+D1 ¬olt）・最終減少 ✓。
- 仮説 **SIB5**: 末尾分岐は無条件（∃p x x1 r1. K=p@[x] ∧ K1=p@x1#r1 のみ、
  x1 制約なし）∨ 旧1/2 ∨ 中間分岐は head-max 第3分岐。closure+4 で
  分岐位置統計を採掘中。SIB5 が閉じれば: sibrel5 改定 + NT_enddrop を
  「末尾任意分岐」の値補題 NT_endany に一般化（要採掘）。閉じなければ
  **sibm2 層を捨て NT レベル不変量（NTTIE2 M）へ全面再設計**。
- 現状: ビルド緑だが seam_open_m1 文面は再び偽認定（+3 69違反）。
  sibrel5/NT 設計決定後に文面改定。

- (続71補) **SIB5 確証 + sibrel5 設計確定**:
  - closure+4 全タイ対 **0/3,533,164** が S1∨S2∨S3∨SE。SE は **lex 降下形に
    締まる**（fst上昇・feq-srise は皆無; 内訳 fdrop-seq 24,303 / feq-sdrop
    11,646 / fdrop-sdrop 153 / fdrop-srise 54）。
  - **sibrel5** = S1 ∨ S2 ∨ S3(head-max中間) ∨ SE-lex
    （∃p x x1 r1. K=p@[x] ∧ K1=p@x1#r1 ∧ (fst x1 < fst x ∨ (fst= ∧ snd<)))。
  - **値補題 NT_endlex**（NT_enddrop の一般化）: SE 対で
    olt(NT K1)(NT K) 厳密 — closure+4 **0/2,292**（NT_tie 結論も 0違反）。
  - **sibrel_ascent は SE で偽** ⟹ 結論を False から
    「r=[] ∧ lex降下」へ弱化。呼び出し側は r≠[]（blift Suc-km は D≠[] 等）
    か lex 反駁（d0>0: snd 逆・d0=0: fst 逆）で閉じられる見込み。
  - diverge の ed 結論も lex 形へ。closure+5 確認ジョブ実行中（/tmp/sib5_c5.out）。

### ★(2026-06-13 続72) SIBREL6 確定 — 3分岐への大幅単純化（決定）

- SIB5 は +5 で破れ（414対 = **中間位置 feq-sdrop・hm なし**）。形状進化の
  収束先を直接検証: **SIBREL6 = K1=K ∨ (K=K1@D, D≠[]) ∨
  first-diff lex降下（x1 <lex x、hm・位置制約なし）**。
- closure+5（1,273,013 ホスト・first-diff 対 10,500 dedup）:
  - V1（lex形）: **0違反** — sibrel6 抽象成立
  - V2（olt(NT K1)(NT K) 厳密・**hm 前提なし**）: **0違反**
  - V3（NT_tie 結論 proj レベル）: **0違反**
- **隣接タイ対の特殊性が本質**（任意 dseg 対では hm なし lex は偽 —
  弱窓 lpl 採掘の教訓）⟹ 値凍結は NT_tie 文脈で:
  **NT_tie_fdlex**（fbseg タイ対・共有接頭辞・lex 降下 ⟹ proj 比較 ¬olt、
  10,500/0@+5）。
- リファクタ計画（全てが縮む方向）:
  1. sibrel 定義 → 3分岐（オリジナルより単純）
  2. 消費側の hm 簿記全廃（copyhead/blift の hmKC/bigle 機械が不要に！）
  3. ascent は asc:=¬lex で False 結論復活・diverge 結論 = lex のみ
  4. NT_tie_resolved = eq/prefix/fdlex の3ケース
     （nfK/nofire は prefix ケースのみ・hdom/tie_nofire 依存が消える）
  5. **NT_lexdiff_lt・NT_enddrop 削除**（fdlex に統合・sorry -2）
  6. シーム凍結文面の sibrel6 再監査（open_m1 の69違反は SE⊆6 で解消見込み）
  7. +6 検証ジョブをバックグラウンド長期実行（V1 形のみ）

- (続72補) sibrel6 実装手順（実行中・python 同期済み・+6 V1 ジョブ実行中）:
  1. sibrel def → 3分岐（S1/S2/FD-lex）
  2. 代数書換: trunc（diff ケースの hm 機械削除・lex 転送のみ）/
     nopref（3ケース）/ ascent（asc := ¬lex で False 復活・呼び出し3箇所の
     neasc に lex 反駁を追加: d0=0 は fst 逆・d0>0 は snd 逆）/
     diverge（結論 = lex のみ）/ shf（lex はシフト保存）
  3. NT_tie_resolved → eq/prefix/fdlex 3ケース・
     **NT_tie_fdlex 凍結**（proj レベル・fbseg タイ対・10,500/0@+5）・
     **NT_lexdiff_lt と NT_enddrop を削除**（正味 sorry -1）
  4. seam 供給側: copyhead/blift の lxf は branch-3'直接構築で
     **bigle/hmKC/diverge 機械が丸ごと不要**（数行に縮む）。site1/2 の
     div ケース分析も縮小（E2var/F2L2 残差呼び出しの場合分けだけ残る）
  5. audit_seam_c3 を sibrel6 で再実行 → open_m1/P 残差の文面浄化
  6. +6 V1 確認（/tmp/sib6_c6.out）

- (続72補2) **closure+6 確証: SIBREL6 0/1,156,797 first-diff 対（4,665,170
  ホスト）** — lex first-diff 形は6リング目も完全成立。構造的確信度が
  これまでで最高（lex 降下は自然な整礎関係・値核も hm なしで安定）。

### (2026-06-13 続73) SIBREL6 リファクタ完結（緑・sorry 22）

- 実装完了（ビルド18秒緑）:
  - sibrel = **3分岐**（S1/S2/first-diff lex降下）— closure+6 0/1,156,797
  - 代数全面書換: trunc（hm機械削除）/nopref/ascent（asc:=¬lex で False
    復活）/diverge（= ascent の対偶1行）/shf — 全て短縮
  - **NT_tie_fdlex 凍結**（proj レベル・10,500/0@+5）が唯一のタイ比較核。
    NT_lexdiff_lt（116万監査）と NT_enddrop を**削除**
  - copyhead/blift の lxf = 4行構築（bigle/hmKC/M側diverge 機械全廃）、
    blift lx2 の hmP 削除、site1/2 の div 消費 = lex 2分岐に崩し
  - **seam_copyhead_m1_F2L2 孤立化→削除**（lex 構築が直接カバー）
  - neasc 3箇所を lex 反駁形に
- sorry 24→22。タイ機構の凍結は NT_tie_fdlex 1点+残差（open_m1/P/E2var/
  deep — 文面再監査が次）。**hm（頭最大）概念がタイ機構から完全消滅**。
- 次: audit_seam_c3 を sibrel6 で再実行（python 同期済）→ open_m1（+3で
  69違反だった）と P 残差（261件）の文面浄化 → 健全性総点検完了へ。

- (続73補) **健全性総点検完了**: audit_seam_c3 を sibrel6 で再実行 —
  open_m1 **0/5,447**（sibrel4 時の69違反が解消）/ P クラス結論 **0/261**
  （空クラスでなく実在261件の正当凍結に昇格）/ E2var 空 / deep 0/45。
  **全 sorry 文面が sibrel6 下で閉包+3 監査済みの真文面に復帰**。
  sibrel 健全性危機（続67〜73）はこれで完全終結。
  通常戦線（続64 優先順位）へ復帰可能。

### (2026-06-13 続74) セッション総括ロールアップ（続55〜73）— 次セッション開幕はここから

**討伐・導出（sorry 実質前進）**: E6_qcut_last（QDIAG凍結+リスト論証）/
E6_iii_singleton（FBS）/ E6_seam 分割（seam_MIN 458k/0 + INV 426k/0）/
**G6統一支配核**（E6_G6 凍結→E6_dom_tie・E6_lpl 討伐、dom_deep/
dom_tie_resolved 削除）/ ginv_O1（証明済BTWRAPUのqa=0系と発見し完全証明）/
BTWRAP_T3 分割（主部20,699証明・残差6件）/ OSC再構成（CT/GAP→O2+GCD 導出・
i1>0真空性証明）/ TOP_desc ステート（967/0）/ QDIAG弱前提化。

**★sibrel 健全性危機と終結（続67〜73・本セッション最大の事件）**:
続29版 sibrel が閉包+3で偽（最終減少・NT_tie 結論は無傷）→ sibrel4(+4で偽)
→ SIB5(+5で偽) → **SIBREL6 = first-diff lex 降下・3分岐**が閉包+6で
0/1,156,797 対。値核 NT_tie_fdlex（proj比較 10,500/0）単一凍結に統合、
hm 概念全廃（-747行）、NT_lexdiff_lt(116万監査)/NT_enddrop/F2L2 削除。
全シーム文面 sibrel6 下で再監査済（open_m1 5,447/0・P 261/0・deep 45/0）。
**教訓: 有限形状分類はコピー力学で閉じない。lex 降下が真の不変量。
シーム系の監査は閉包+3以上必須（+1/+2 は4回すり抜けた）。**

**現況**: sorry 22（nrmstep）+ nrm_order_pres（パス外）。ビルド緑 ~20秒。
全凍結が監査済み真文面。

**次セッションの優先順位**:
1. **qpos**（171・続37補地図: q'=0 は e1j0<e1j1≤B で直証可能・q'≥1 は
   qP=2 窓のみ — ginv_ob_copy の窓代数をテンプレートに分割実装）
2. **t14ok_oper_bad**（続43補2 の15クラス地図実行・past クラスが新規内容）
3. **OSC 核 O2/GCD**（振動規律: GCD の機構候補 =「正親の等値子は
   nextrel1 一意性で禁止」— 要採掘。chains: バンプは0親のみ）
4. **G6 本体**（T側閾値渡し再帰・seam_MIN を K側合成・wf3 OT3 部品）
5. 最終組立（メガ束・続59 地図・全葉後）

### ★★(2026-06-13 続75) ginv が closure+3 で偽 — qpos 攻略中に検出（5例目・中央不変量）

- qpos 分解採掘で qpos 結論の30違反（+2）を検出 → 呼び出し側を精査すると
  caller は ginv_def の量化変数をそのまま渡しており、違反配置は
  **ginv 自体の反例**: M=(0,0)(1,1)(2,2)(3,1)(4,1)(4,1)(4,1)（+2圏）の
  X=M[2]（+3圏・到達可能）で窓 p=3（(3,1)）・dom 全成立・stop t=1
  （X!5=(4,1) fst≤4）・**l=8: X!8=(6,2) snd 2 > bound max(1,1)=1**。
  手検証済み。ginv の 42,489/0 は closure+2 監査で X が +3 のため
  すり抜け（シーム+3必須教訓の再確認）。
- 機構: level-Suc-p の stop（return）後も窓は dom を保ったまま**次コピーで
  再上昇**できる（コピーシームの климб）。M 窓では起きず X 窓で発生。
- **修正候補 ginv'**: bound を **l ≤ Suc p + t（最初の stop まで）** に制限
  した形。要監査（+3）と、消費側 ginv_dseg_bound（E6_nbcK_T の橋）が
  必要とする l 範囲の確認。
- 影響: ginv 族（GBLK0/GAP/O1/O2/qpos/ob_pre/ob_copy/oper_bad/ST_PS）の
  全文面と証明の再点検が必要。sibrel6 と同じ手順（真形特定→재監査→
  リファクタ）で対処。qpos の30違反はこの ginv 偽の系（同一配置）。

- (続75補) **修正候補 ginv'（l ≤ Suc p + t 制限）: 0違反 @ closure+3** ✓。
  影響連鎖の地図:
  - **ginv_dseg_bound の結論も同反例で偽**（停止 ir の後の x が上界を
    破れる — X!8=(6,2) vs max(1,1)）。restated 版 = 「x が最初の停止以前」
    に制限 or 結論変更。消費側 E6_nbcK_T（緑）の使用箇所の必要範囲を
    確認して合わせる。
  - ginv 族リファクタ手順: (1) ginv_def に l ≤ Suc p + t を追加
    (2) ginv_diagSeq/take/butlast/oper/oper_bad（ob_pre/ob_copy/ob_qpos）
    の保存証明を再導出 — **制限により qpos の30違反配置は照会されなくなり、
    qpos 残差は縮小or消滅の見込み**（crossing と停止制限の両立を再採掘）
    (3) dseg_bound' → nbcK_T 修理 (4) 全 ginv 族文面の +3 再監査
  - O1/O2/GCD/GAP/GBLK0/BTWRAP 族は M-block 事実として独立 +3 監査済み
    （0違反）— ginv 偽の影響は ginv_def 量化形の系（ob 転送と dseg_bound）
    に限定される見込み。

- (続75補2) **修復設計完結**:
  - **nbcK_T 文面は真**（0/3,725,540 @ +3）。証明も生存: max-in-K 前提の
    K = takeWhile は**最初の停止以前**の要素のみ ⟹ ginv'（停止までの上界）
    で同じ背理が回る。
  - **dseg_bound' 再ステート**: 結論を x ∈ set (c0 # K)（頭+ラン）に制限、
    証明は t := Suc(length K)（最初の停止）で ginv' を適用。
  - ginv 保存連鎖: 結論に l ≤ Suc p + t が加わる = 証明は楽になる方向
    （転送は位置線形で制限も運ばれる）。**qpos は制限下で再採掘**
    （crossing 後の停止がある配置のみ残る — 縮小/消滅見込み）。
  - 実装順: (1) ginv_def 編集 (2) ビルドで保存証明の破損特定→修理
    (3) dseg_bound'+nbcK_T (4) qpos 再採掘・restate (5) +3 再監査。

- (続75補3) ginv' def 編集の単独投入はビルドハング（ginv 族のどこかの
  blast/auto が発散・26分）→ **リバートして次セッションへ引き継ぎ**。
  現リポジトリ状態 = ginv は既知偽（続75の反例・コピーシーム再上昇）の
  まま緑ビルド。修復は設計済み（続75補〜補2）で、実装は
  「def編集 + 全 G[unfolded ginv_def, rule_format] サイトの lmm
  （l ≤ Suc pm + N）→ lmm'（l ≤ Suc pm + t）化 + 目標方向の保存証明の
  premise 追加」を**一括同時適用**してからビルドすべき（単独 def 編集は
  rule_format 適用の構造ミスマッチで発散する）。
  次セッション最優先 = この ginv' 一括修復。

### ★★(2026-06-10 続9) olt on NF = 数列の列 lex（249500対 全一致）＋Trans 対角の正体
- **実測: 標準形 M,N について olt(translate M, translate N) ⟺ seqlex(M,N)**（列 (r0,r1) の
  辞書式・prefix 小、500 форм 全対 249500 で相違 0）。
  ⟹ translate は (ST_PS, seqlex) ≅ (NF, olt) の順序同型（構文的に証明可能な見込み・要 Isabelle 化）。
  ⟹ wfE ⟺ 「標準形の seqlex 無限降下列が無い」（BMS ネイティブな形）。
- P進 Trans の対角値（content.md 6142）: Trans((u,u)…(v,v)) = **D_u(D_v 0)**（昇順タワー→2段）。
  Trans(標準形) ∈ OT_B は P進が証明済（6124）⟹ 橋の像は wf_olt_wf3 のクラス内。
- 較正実験: oper n ↔ OT bracket z の対応はケース依存（(0,0)(1,1) は n-2、対角3 は n-1）⟹
  経験的 Trans には I–VI の完全実装が必要（pss-proof python に Trans は無い、buchholz.py に
  OT/bracket/in_OT あり流用可）。
- (β1) の最終形: 「seqlex M N ⟹ Trans M <_OT Trans N」（P進 機構のみで閉じる新定理）
  ＋ olt=seqlex（自前）＋ wf_olt_wf3（自前・済）⟹ wfE 完結、ya-pss 前半は丸ごと存続。
- 次手候補: (1) olt=seqlex を Isabelle 化（独立価値・確実）、(2) Trans の Python 実装で
  seqlex-単調性を実測、(3) ユーザーと α/β 最終確認。

### (2026-06-12 続61) ginv_CT 偵察 — i1=0 クラスの特定

- 閉包+2 実例7件の完全ダンプ（mine_ct.py）: **全件同型** qa=0/w=1/x=2、
  ブロック=(v,0)(v+1,1)(v+2,0)、アンカー snd=0・tight snd=1・子 snd=0。
- **全件 i1=0 ブランチ**（M!j1 の snd=0 → d0=0 は規約値、レベル等値ではない。
  e0(j1)=e0(j0)+1 の row-0 親）。i1>0∧d0=0 の CT 部分クラスは実例0（空）。
- ユニバーサル化の試み: dom+stop（btfullok 窓）+tight+gap-clear 子 ⟹
  snd 降下（UCT）は **実例0で不発**（CT 窓には stop がない: ブロック終端
  e0(j1)=e0(j0)+1 はアンカーレベルを上回る）。対角線反例も確認
  （stop なしでは偽）— CT の本質は btfullok 族でなく **t1ok 型 row-1
  予算勘定**（d0=0/i1=0 ブロックで +1 予算は一度きり、消費後の
  gap-clear 子は厳密降下）。
- 次の設計方針: (i) i1=0 に制限した CT'（7実例）+ 空クラス CT''（i1>0）に
  分割し、CT' は row-0 連鎖ブロックの t14ok/t1ok 系窓で生成帰納、
  または (ii) 7実例が全て「ブロック長3・固定形」なので、ブロック長で
  剛性補題（bad ブロック d0=0/i1=0 ⟹ ブロック構造の完全特徴付け）を先に
  立てる。次セッションで (ii) の特徴付け採掘から。

- (続75補4) ginv 一括修復の精密スコープ（サイト読解済み）:
  - 機械的（lN 文面変更のみ）: ginv_def / diagSeq(2130) / take(2149) /
    oper_bad(3127) / ob_pre・ob_qpos・ob_copy の lN premise。
    供給 discharge は lN そのまま・XM 系転送には tN を追加
    （l ≤ Suc p+t ≤ Suc p+N 連鎖）。例: 2635 `using XM pl lN by simp` →
    `using XM pl lN tN by simp`。
  - **非機械的（停止位置論証が必要）**: 2752/2764（ob_pre C2 圏・M側窓
    (p,NM,tm) へ転送する箇所）は lM/lm が NM 上界しかなく、新 def は
    l ≤ Suc p + tm を要求。EXcl で得る停止 tm の位置が j0 以降
    （ブロック端）であることを使い l < j0 ≤ Suc p + tm を導く必要
    （EXcl 構成 ~2700-2742 を精読して tm の位置下界補題化）。
    2908/3097 も同様に各停止の位置 vs l の論証を確認。
  - dseg_bound 再ステート（x ∈ c0#K・t := Suc(length K)）と nbcK_T の
    bnd 適用範囲縮小は設計済み（続75補2）。

- (続75補5) ob_pre C2 圏の精密分析（EXcl 精読済み・2719-2743）:
  - EXcl の停止 tm は2ケース: (A) X停止が prefix 内（Suc p+t < j0）→
    tm = t・位置 < j0 / (B) コピー内 → Suc p + tm = j0 + qc。
    **EXcl の statement を「tm = t ∨ j0 ≤ Suc p + tm」付きに強化**すれば:
  - 2752（l < j0 照会）: (A) 新lN（l ≤ Suc p+t = Suc p+tm）✓
    (B) l < j0 ≤ Suc p+tm ✓ — **両ケース閉じる**。
  - 2764（l = j0+(kl·L+ql) 照会・M側 j0+ql）: (B) で ql ≤ qc が必要だが
    新lN は kl·L+ql ≤ kc·L+qc しか与えず **kl < kc ∧ ql > qc の配置で
    M停止超え照会**が残る — ここだけ新副論証が必要
    （候補: M側の別の停止（j1端 fst=e0(j0)+d0' ≤ fst(M!Suc p)?）での
    再適用、または O1/ブロック事実で直接 bound）。まず該当配置を採掘して
    実在性と bound 機構を確認するのが先（空なら場合分けで vacuous 化）。
  - 2908（ob_qpos 呼び圏=oper_bad 本体）/3097 は ob_qpos/copy の同型問題 —
    qpos は凍結なので statement 変更のみ、copy は同様の停止位置確認。

- (続75補6) kl<kc∧ql>qc 配置は**非空**（112,320 @ +2・例: 振動ブロック
  (4,0)(5,0)... の prefix アンカー窓）→ 2764 副論証は実在する未解決部。
  候補ルート（次セッションで採掘から）:
  (a) M側の別停止 q* ≥ ql の存在（コピー(kl+1)頭の X 写像が停止か等）
  (b) ブロック内部 snd を prefix アンカー対 max(snd p, snd Suc p) で直接
      bound する新ブロック事実（GAP/GBLK0 族の prefix-アンカー版）—
      まず「この配置で snd(M!(j0+ql)) ≤ max(...) が成立するか」自体を
      監査し、成立形を凍結（ginv 修復のための新凍結はやむなし）。
  - ginv 修復の全体像はこれで完全に地図化（続75〜補6）。実装は
    機械的部分（def/diagSeq/take/oper_bad/ob statement 群 + EXcl 強化 +
    2752）を先に当て、2764 圏は (b) の監査結果で凍結 or 証明。

- (続75補7) **ルート(b) 監査クリア: 0/491,080 @ closure+3** —
  2764 配置の M側 bound「snd(M!(j0+ql)) ≤ max(snd(M!p), snd(M!Suc p))」は
  全配置で成立。**新凍結 ginv_ob_gpre**（ob_pre C2 前提 + p<j0 + X停止
  (kc,qc) + 照会 (kl,ql)・kl<kc・ql>qc ⟹ 上記 bound）として据える。
  これで ginv 修復は完全実行可能:
  - 2764 = case split ql≤qc（停止内・restricted-G 直）/ ql>qc（gpre 凍結）
  - case A（prefix 停止）×ブロック照会は新 lN と矛盾で真空
  - 2908（copy 圏 1:1 転送）は位置線形で機械的 ✓
  - 3097（copy qP=0 横断）は同型の停止位置分析を実装時に確認
  実装はこの地図で一括適用 → ビルド反復。

### (2026-06-13 続76) ginv 修復キャンペーン完結（緑・sorry 22・qpos 削除）

- **実装完了（ビルド19秒緑）**:
  - ginv_def を真形（l ≤ Suc p + t・closure+3 0違反）に制限
  - 保存連鎖修理: diagSeq/take（ln 文面）/oper_bad（lN）/ob_pre
    （EXcl を停止位置2ケース付き強化・C2 prefix 照会は新 lN で閉）/
    1:1転送（slt/slN 分離）
  - **新凍結 ginv_ob_cross**（制限窓 + j0 ≤ l の X側 bound・+3 監査の
    制限 ginv に含意される・prefix 部分集合は直接 0/491,080）
  - **ginv_ob_qpos は ob_cross に包摂され削除**（旧 l>p≥j0 ⟹ lj0 ✓）—
    長年の凍結核1点消滅
  - dseg_bound' 再ステート（x ∈ c0#K・t := Suc|K|）+ nbcK_T 修理
- ハング解析の教訓追加: **fork 並列のため ML エラー二分探索は
  fork 中の発散を素通しする（unsound）**。真犯人 = dseg_bound の多弾
  metis（Klt 5弾等）と EXcl の ∃+disjunction blast — 全て決定的化
  （arg_cong/dropWhile_eq_drop/exI 明示）で解消。
- 健全性事件6例目（ginv）はこれで完全解決。sorry 22 内訳の変化:
  -qpos +ob_cross（相殺）で同数だが、ob_cross は +3 監査済みの真文面。

### (2026-06-13 続77) 全凍結 closure+3 検証完了マイルストーン

- 最終バッチ: **FBS 0/445,239**（+2 の83倍基盤）/ **STS_B 0/395,044
  全パート**（Q2 hdarg 不変も維持）/ NT3 空維持 / memT 空維持。
- **これで現存 22 sorry の全文面が closure+3 以上で検証済み**:
  G6(+3 3.4M)・seam_MIN/INV(+3 2.7M/2.6M)・QDIAG(+3 151k)・FBS(+3 445k)・
  STS_B(+3 395k)・NT_tie_fdlex(+5 10.5k/+6形状1.16M)・TOP_desc(+3 1,931)・
  O1系証明済・O2(+3 489)・GCD(+3 61)・NT3/memT/E2var(空@+3)・
  BTWRAP_T3_pos(+3 60)・ob_cross(+3含意)・open_m1(5,447)・P(261)・deep(45)・
  copyhead_deep 系・nbcK_K（未+3 — 次回）・t14ok_oper_bad（地図済・未+3）。
- 健全性事件6例（sibm2系5+ginv）全解決後の初の全面クリーン状態。

- (続77補) nbcK_K +3 監査クリア: **0/445,422** — これで全凍結の closure+3
  検証が名実ともに完了（未了ゼロ）。

### ★★★(2026-06-13 続78) 健全性事件【第7例・最重大】— 値側アーキテクチャの基盤 E6_value が closure+5/+6 で偽

**経緯**: OSC 振動コア（O2/GCD）の討伐設計のため普遍核を採掘中、深層
（closure+5）監査 audit_osc_c56.py で O2/O1P が偽と判明。掘り下げた結果、
**「窓内 row-1 を開き口アンカーの max で抑える」形の補題が系統的に全て偽**で
あることが確定（第1〜6事件と同根だが、今回は**値側コンビネータ基盤**まで波及）。

**反例（到達可能・BFS確認済み）**:
- 種 M=(0,0)(1,1)(2,2)(3,0)(4,1)(5,2)(6,0)(7,1)(8,2)(8,0)（closure+5）
- X=M[2]=(0,0)(1,1)(2,2)(3,0)(4,1)(5,2)(6,0)(7,1)(8,2)(7,1)(8,2)（closure+6）
- 機構: **row-1 上昇鎖**（連続レベル昇順で snd も昇順 (6,0)(7,1)(8,2)、
  snd は r1ok の「snd ≤ Suc(親 snd)」だけで縛られ climb 可）が支配窓に入ると、
  ある列の snd が**開き口2アンカーの max を超える**。コピーシーム再上昇が
  深層で初めて顕在化。

**偽と確定した文面（到達可能ホストで反例・モデルは浅層0違反で検証済）**:
| 文面 | 種別 | 深さ | 違反 |
|---|---|---|---|
| ginv_O2（bad-block） | sorry | +5 | 9 |
| ginv_O1P（≤head・本セッション導入） | sorry | +5 | 9 |
| ginv_GCDV/O2V（普遍核・本セッション） | sorry | +3/+4 | 18+ |
| ginv_GAP/GBLK0（O2 から導出） | 証明 | +5 | 多数 |
| 制限版 ginv（l ≤ Suc p+t・続75-76の「修復」） | def | +6 | 有 |
| ginv_dseg_bound（消費橋） | 証明 | +6 | 有 |
| E6_nbcK_T（「max がKにあれば return せず」） | 証明 | +6 | 190/deep |
| E6_mem_resolved の **Gterm 帰属部分** | 証明 | +6 | 190/deep |
| **E6_mem**（msfx∈Gterm・基盤 sorry） | sorry | +6 | 有 |
| **E6_value（proj u (NT S)=NT(msfx S)）** | 証明 | +5/+6 | 190/deep |
| ginv_ob_cross/ob_pre/ob_copy（→ginv_ST_PS） | sorry | +6 | 含意で偽 |

**モデル検証**: 私の Python（msfx=Isabelle定義一致・proj/NT/G）は E6_value を
+0/+1/+2/+3 で **0違反**（445,422インスタンス）= memo の「empirically exact
15302位置」を完全再現。深層の190違反は本物。

**健全（深層でも真・検証済）**:
- 最終減少 olt(NT(M[n]), NT(M))：反例ホスト全て True ✓（本丸無傷）
- **NT_tie_resolved / NT_tie_fdlex：deep family 0違反** ✓（値側タイ比較は真）
- E6_mem_resolved の **¬olt 部分：0違反** ✓
- ginv_GCD（last-anchored・j1基準）：+5 0違反 / ginv_O1（Suc形・BTWRAPU証明済）

**含意（最重要）**:
1. **「全 sorry を closure+3 で検証完了」（続77）は ginv/OSC/nbcK/E6_value
   族について偽**。+3 で清浄でも +5/+6 で破れる（再上昇は監査深度+1で初出）。
2. **方法論の系統的破綻**: 「有限閉包で経験的に検証した文面を凍結」戦略は、
   コピー再上昇に対し原理的に収束しない。アンカー max 型の窓 row-1 上界は
   **形が間違っている**（正しいのは r1ok 親鎖上界で、これ自身が climb する
   ので2アンカーに潰せない）。7回連続の偽凍結は全てこの同じ誤形。
3. **しかし定理は真**: 最終減少も NT_tie も真。つまり「証明戦略が誤りだが
   命題は正しい」。値側の比較は ¬olt（NT_tie_resolved 型）だけで足りるはずで、
   proj=msfx-NF や msfx∈Gterm という**強い構造同一性は不要かつ偽**。

**本セッションの対応**:
- 本セッション導入の OSC 再構成（GCDV/O2V/O1P 凍結、da4e988）は誤解を招く
  ため nrmstep.thy を da4e988^ に復元（sorry 22 維持）。採掘/監査スクリプトは
  証拠として残置（audit_osc_c56.py, audit_value_deep.py, mine_oscu/oscv/o2h/
  o1p_c3.py, mine_gcdv_pres.py）。
- task.md に🚨健全性第7事件を記載。

**次の方針（要・方針相談）**: 値側アーキテクチャ（E6 の proj=msfx-NF /
msfx∈Gterm / ginv anchor-max / nbcK 連鎖）が基盤レベルで偽。選択肢:
  (A) E6_value/E6_mem を捨て、NT_tie_resolved（真）を直接土台に値側比較を
      ¬olt のみで再構築（msfx 同一性に依存しない比較論証）。
  (B) proj の真の値を記述する正しい補題を発見（msfx ではなく実際の射影核）
      し、E6_value を真文面に置換 → 連鎖を貼り直す。
  (C) r1ok 親鎖上界（climb する真の不変量）で ginv を置換し、nbcK を r1ok
      ベースで再証明。
  いずれも大規模な再設計。最終減少が真である以上ルートは存在する。

### ★★★(2026-06-13 続79) 戦略転換決定 — dichOK 戦略へ（lean-yapss/Lean を青写真に）

**ユーザー指示**: ya-pss Isabelle を進める。Lean 版を参考・同戦略への乗り換え可。
（「Route A」等の私の選択肢ラベルは今後不使用＝混乱回避）

**lean-yapss 調査結論**:
- lean-yapss/**Isabelle** 版（isabelle/ord/nrmstep.thy・sorry 12）は ya-pss と
  **同じ偽 E6_value（proj=NT msfx）+ E6_mem(sorry) 架構**＝同じ袋小路。
- lean-yapss/**Lean** 版（lean/YAPSS/Nrmstep.lean・**sorry 0**）は **E6_value/
  E6_mem/ginv/nbcK/GBLK0/O2/dom_deep/lpl を一切持たない**（grep ゼロ）。健全。
  抜け穴なし（axiom/native_decide/unsafe/sorry なし、Nrm の nrm_order_pres と
  Wfsum の wf_ArgsA のみ別 sorry）。
- **私の第7事件発見は正しい**（Lean は健全ゆえ偽の E6_value を使えず別路線に）。

**Lean の健全な土台 = dichOK（辺二分律）**:
  `dichOK M ⟺ ∀p q t. nextrel1 M p t → le0 M p q → q<t → 0<snd(M!q) →
              (le0 M q t ∨ M!q = M!t)`
  ＝行0/行1 祖先の**接続性二分律**（値bound でない）。ginv のアンカーmax（偽）の
  健全な代替。マイニング 28054/28054 一致。Lean 証明済（dichOK_ST_PS、copy 義務
  copyDichOK_of も 0 sorry）。土台補題群: le0/nextrel0 合同（_congr/_shift）・
  rootsplit・copyExp・cross_dichOK・dichOK_{diagSeq,take,Pred,ST_PS}。
  併せて **NT_tie_of**（健全な tie コンビネータ）も Lean に存在。

**重要**: dichOK はまだ nrm_order_pres に未接続（Lean でも Nrm/Proofs で未使用）。
  ⟹ 値側最終減少は**両プロジェクト未完**。Lean は健全土台＋方向のみ確立。

**ya-pss 移植計画（続79〜）**:
  Phase1: dichOK 定義 + 保存補題群（diagSeq/take/Pred/ST_PS + copyExp/le0合同/
    rootsplit/cross_dichOK）を Lean→Isabelle 翻訳（0 sorry の健全部分）。
    def.thy に nextrel0/le0/nextrel1/nextR 既存・流用可。
  Phase2: 偽族（ginv/E6_value/E6_mem/nbcK/O2/GBLK0/GAP/dseg_bound/ob_*）を撤去。
  Phase3: dichOK + NT_tie で nrm 値側減少を完成（Lean 未完＝新規設計）。
  対角の m_step_decreases（translate 減少）は健全・流用。

### ★★(2026-06-13 続80) 訂正 — dichOK も d0=0 完全コピーで偽・lean-yapss は crux 未解決

**続79 の「Lean が値側を健全に解いた青写真」評価は誤り**だった。精査結果:
- ya-pss モデルで **dichOK は closure+4 で 130,392 違反**。反例 M=(0,0)(1,1)
  (2,1)(3,1)(4,0)(5,1)(6,1)(7,0)(8,1)(9,1)(8,1)(9,0)... の p=7,q=9,t=10:
  **t=10 列 (8,1) は位置8 (8,1) の完全コピー再上昇**（d0=0 exact-copy re-entry）
  = E6_value を壊したのと同じ再上昇機構。M は到達可能・r1ok 成立。
- Lean 側の対応: `copyDichOK_of` は **hd0: 0<d0（シフトコピー）のみ証明**。
  完全コピー d0=0 分岐は未証明。`dichOK_ST_PS`（hbad 義務付き）は **Nrmstep 内で
  一度も適用されず**、dichOK は **Nrm/Proofs で未使用**＝**停止性に未接続**。
  値側最終減少 `nrm_order_pres` は依然 sorry。
- ⟹ **dichOK は d0=0 で偽**で、Lean は d0>0 だけ証明し crux を未接続のまま放置。
  Nrmstep.lean が「0 sorry」なのは、crux を **未充足の仮説 hbad に退避**し
  dichOK をゴールに繋いでいないため。**lean-yapss も値側 crux は未解決**。

**真の hard core 確定**: **d0=0 完全コピーの再上昇**。msfx-anchor（E6_value）も
  辺二分律（dichOK）も、この再上昇でいずれも偽。最終減少は真（検証済）なので
  論証は存在するが、両姉妹プロジェクトとも未達。dichOK への単純乗り換えでは
  crux を回避できない。

### (2026-06-13 続81) 再発防止の考察（健全性7事件 post-mortem）

ユーザー要請で考察。詳細はメモリ [[freeze-soundness-lessons]] に恒久保存。要旨:
- **なぜ偽が生まれたか**: (1)「有限閉包で経験的検証→凍結」は反証しかできず証明
  不能 (2) 反例 X=M[2] は監査深度+1 で出る構造的盲点（+3 clean/+5,+6 偽は必然）
  (3) 不変量の**形**が誤り＝窓 row-1 を有限アンカーで抑える上界（真は r1ok 親鎖で
  climb・有限アンカーに潰せない）＝族全体が原理的に偽 (4)「N件0違反」への確証バイアス。
- **行けなかった思考/行動**: +3=真の暗黙等式／同じ機構の反復をメタパターンと認識せず
  局所修理を反復（sibrel→…→SIBREL6, ginv→…）／sorry を「証明済」扱い（続77 幻の
  マイルストーン）／確証>反証の労力配分／本丸が真ゆえの油断／危うく権威（Lean
  0-sorry）に従いかけた。
- **再発防止**（[[freeze-soundness-lessons]] 厳守）: 凍結は closure+5以上＋oper 1段
  をかけて監査／紙スケッチ必須（再上昇ケースの欠落を検知）／「row1≤有限アンカー」型は
  構造的に疑う／同機構2回falsifyで形・方法論を再検討／sorry=負債（マイルストーン
  にしない・kernel 0-sorry だけが証明）／クロスチェックは権威でなく中身を掘る。

### (2026-06-13 続82) d0=0 値側減少の構造解析 + proj 単調性（E6_value の健全な置換候補）

ユーザー一任で d0=0 完全コピーの値側減少を**理解フェーズから**着手（凍結前に紙
スケッチ・教訓厳守）。

**d0=0 減少の構造**（study_d0zero.py で確認）:
- bad-branch d0=0/i1=0 では **M = G @ B @ [lp]**（G=take j0, B=block[j0,j1),
  lp=M[j1]＝最終列）、**M[n] = G @ B^n**（lp を落とし B を n 個・完全コピー）。
- **NT(M[1]) <o NT(M) は NT_prefix_lt そのもの**（C=M[1]=G@B, D=[lp]・既証明・真）。
  ＝lp が総和に1項追加する切り詰め。
- n≥2 は G@B 共有後に分岐。実証（13,224 d0=0 例 0 fail）: **lead(NT M[n]) =
  lead(NT M)** が常に成立し、減少は subscript-first lex で **hdarg で決まる**
  （hdarg(NT M[n]) ≤o hdarg(NT M)）。
- NT_shape より **hdarg(NT(c0#rest)) = proj(snd c0)(NT K)**（K=takeWhile）。
  ⟹ 減少は **proj の単調性** `a ≤o b ⟹ proj u a ≤o proj u b` に帰着。

**proj 単調性の検証**:
- NT-像（標準セグメント）上: **+4 broad 149,428 ペア 0 違反**、**深層再上昇
  ファミリー 1,195,095 ペア 0 違反**（E6_value が190違反で死んだ同じ集合で生存！）。
  ⟹ **order だけ保てばよい proj 単調性は再上昇に耐える**（value を主張する
  E6_value と本質的に違う）＝**E6_value の健全な置換**。
- ただし**任意 wf3 項では偽**（26,808 違反・lead 相違 D0(D1(..)) vs D1(..)）。
  sameLead/bothLeadGEu 制約でも残る（2,463 違反）。⟹ **純項レベルでなく
  NT-像クラス特有**＝標準性構造に依存。形式化には NT-像の特徴づけが必要。

**次フェーズ（形式化設計）**:
- 値側減少を NT_shape（真）+ proj 単調性（NT-像上・要形式化）+ NT_prefix_lt（真・
  base）+ lead 一致 で再帰的に組む。E6_value/E6_mem/msfx は全廃。
- proj 単調性 on NT-像 を Isabelle でどう証明するか（NT-像の不変条件を伴う帰納）が
  次の核心。**凍結前に +5/+6 broad 監査**（教訓）＋紙スケッチ。
- d0>0 ケースは別途（lean-yapss の copyExp/le0 合同が健全な道具として流用可）。

- (続82補) proj 単調性 broad +5 監査クリア: **+5 新フロンティアsample 319,200ペア
  0違反**（classes u=0..3）。深層再上昇ファミリー120万＋broad+4 15万と合わせ
  **proj 単調性 on NT-像は深層で頑健に真**＝凍結前監査ゲート通過。次は Isabelle で
  「proj 単調性 on NT-像」をどう証明するか（NT-像の不変条件付き帰納・任意wf3では
  偽なので標準性が要る）の形式化設計。既存 proj 補題（proj_once/nofire/fire_in/
  proj_submono）を土台に検討。

- (続82補2) proj_submono は既証明（`Gterm u x ⊆ Gterm u y ∧ ole x y ∧ fire条件 ⟹
  ole(proj u x)(proj u y)`）。だが d0=0 再帰の**素朴 top-split**（c0=M[0] の takeWhile
  対）では **Gterm 包含が 0/348 で不成立**（ole は 348/348 成立）。proj 単調性自体は
  NT-像で真なのに proj_submono の包含ルートで閉じない。⟹ **正しい分解（M と M[n] の
  ブロック差が局所化する位置）を見つける**のが次の核心。素朴 top-split は run が
  M/M[n] で全く違うため不適。NT_shape の tail 降下で block 領域（M=…[lp] /
  M[n]=…B^(n-1)）まで降りた所で包含が回復するか、を次に検証する設計。

### (2026-06-13 続83) d0=0 値側減少の精密分解 — proj_emb_mono(純項・確定) と残ギャップ(sum-vs-nest)

並行 NT_shape 再帰で d0=0 減少（13,224件・168,832階層）を解析:
- **proj は再帰の全 proj 比較対で単調**（monotone_fail=0）。発火は1,624のみ（9割超は
  proj=恒等）。c0 は全階層で共有（cdiff=0）＝lead 常に一致。
- **純項レベルの清潔な補題を発見・検証**（任意 wf3 項で 0 違反）:
  - **proj_emb_mono**: `x ⊑ y ⟹ ole (proj u x) (proj u y)`（60,609/0）
  - **emb_imp_ole**: `x ⊑ y ⟹ ole x y`（emb but not ≤o: 0）
  - ⊑ = 階層的初期部分項埋め込み（principal 列を componentwise: 同 subscript・
    引数も ⊑・和は長さ prefix）。**標準性に依らず構造帰納で証明可＝深層監査不要**。
- **だが ⊑ は不十分**: 
  - top-level `NT(M[n]) ⊑ NT(M)` は不成立（3,306/13,224 のみ・和の深引数で項増加）。
  - 再帰 K-level でも `NT K_n ⊑ NT K_M` は 39,066/168,832 で不成立。失敗核 =
    **sum-vs-nest**: M[n] が同レベル継続で**和**(D0(0)+D0(0))・M が climb で
    **入れ子**(D0(D0(0)))＝NT 構造が別物だが olt は成立（nest >o sum）。
- proj 単調性 on NT-像 は真（再上昇でも・続82）だが**任意 wf3 では偽**（26,808違反・
  sameLead でも 2,463・「埋もれた高 subscript」D0(D2(0)) 等）。⟹ NF(cnf)＋標準性
  特有で、清潔な term-level 特徴づけは未確定。

**確定した証明部品（健全・形式化価値あり）**:
  NT_shape(真)・NT_prefix_lt(真・base)・**proj_emb_mono / emb_imp_ole(純項・要形式化)**・
  proj_submono(既証明・但し Gterm包含は本件で不成立で不適)。

**残る核心ギャップ**: sum-vs-nest を含む lex 比較。⊑ で閉じる部分（多数）は
  proj_emb_mono で、閉じない部分（sum↔nest 切替）は別途。これが E6_value(偽)が
  雑に潰そうとし dichOK(偽)も捉えられなかった真の hard core。次は **NT_shape による
  term-size 強帰納で proj 発火/sum-vs-nest を場合分けする値比較の正面再構築**
  （proj_emb_mono を主道具に）。

- (続83補) crux 局所化完了: 並行再帰で **nofire 階層 167,208 全て proj=恒等で自明**
  （ole そのまま再帰）。**fire 階層 1,624 のうち ⊑ を満たすのは 406 のみ**、
  残 **1,218 は fire かつ sum-vs-nest**（最深で M[n]=和 D1(0)+D1(0) vs M=入れ子
  D1(D0(0))・(8,1)(8,1) 反復 vs (8,1)(9,0) climb）。ここで proj_emb_mono 不適。
  proj 単調性はこの 1,218 でも真だが ⊑ で説明できない＝**fire×sum-vs-nest が
  真の irreducible crux**（E6_value も dichOK も捉え損ねた核心）。
  - 確定ツール: proj_emb_mono（fire 406 + nofire 全部をカバー）。
  - 残: fire×sum-vs-nest の proj 比較。proj 単調性 on NF-class の清潔な
    term-level 特徴づけ（任意 wf3 では偽・「埋もれた高 subscript」が原因・
    標準性=r1ok が subscript を制御している筈）が次の鍵。
  - 次の設計案: (i) NF-class を「in_OT＋r1ok 由来の subscript-深さ条件」で
    特徴づけ proj 単調性を証明 / (ii) fire×sum-vs-nest を NT_shape 再帰で
    直接場合分け（proj 発火時の sum↔nest 切替の値比較を個別に）。
    いずれも腰を据えた設計。次セッションは (i) の NF 特徴づけ採掘から。

### (2026-06-13 続84) Buchholz Hydra + UBI 検討 / NF-class 特徴づけ(slip)失敗 → 自己相似再帰へ

- **Buchholz 1987 Hydra 論文 精読**: 項構造 T = three と構文同型。停止性 Theorem I を
  §1(無限整礎木 ‖A‖∈T_0・‖A(n)‖=‖A‖(n)) と §2(W_0=T_0・ID_ω・Lemma 2.4 和閉包/
  2.5 D_v閉包の項長帰納) の2通りで証明。§3 の **step-down 関係 ≪_k**（3.2(a):
  (D_v a)·n ≪_k D_v(a+1) ＝「n コピー（和）は入れ子+1 に step-down」）が sum-vs-nest
  crux の組合せ核心。**但し p≠ψ で [n]/dom/≪_k 規則は移植不可**（[[psi-correspondence-not-assumed]]）。
  ya-pss の wf_olt_wf3 が既に §1/Lemma2.2 相当。新WF不要。値側 crux が残課題。
- **UBI ブログ（koteitan 2018）精読**: ペア数列=ヒドラ（親=nextrel0/1・上枝無視=nextrel1
  の le0祖先制限・上昇=d0>0/コピー=d0=0）。展開機構の静的可視化で停止性証明は無し。
  示唆「行1 nest は行0 祖先に従う(≤親+1)」。
- **NF-class 特徴づけ slip（subscript-Lipschitz: 入れ子で添字+1まで）は失敗**:
  (a) NT-像 49878/93974 違反（S=(1,1)(2,2)(3,3)→NT=D1(D3(0)) で外1→内3 の2ジャンプ）。
  **proj が中間レベルを collapse して添字ジャンプを作る**。(b) slip-class でも proj単調
  3.5M 違反。⟹「行1≤親+1」はシーケンス側のみ真、**proj/NT 後の term 添字には効かない**。
  ＝清潔な term-level 特徴づけが見つからない根本理由。
- **方針修正**: term-level proj 単調性の特徴づけは断念。代わりに**自己相似再帰**:
  fire 階層の (K_n,K_M) は Kn 末尾=(8,1)(8,1)コピー vs Km 末尾=(8,1)(9,0)climb で
  **より深いレベルの copy-vs-climb（=M[n]-vs-M の縮小版）**。⟹ 値側減少を「項/列サイズの
  整礎帰納で各 fire 階層の proj 比較を1段深い同型比較に還元、最深 NT_prefix_lt で底打ち」
  として組む設計。proj を別補題でなく帰納の中で descend させる。次=この自己相似再帰が
  実際に閉じるか（proj が IH を descend で運ぶか）を採掘で確認。

- (続84補) proj=NT(部分列) の精密化も内部再上昇で破れる:
  - fire 階層で proj(snd c0)(NT K) = NT(連続部分列 K') は成立（1624/1624）だが、その K' は
    **shallow では msfx（firstmax:len）に見えるが深層で破れる**: 再上昇ファミリーで
    fire 限定でも 151 違反（同反例 a=0,K=(7,1)(8,2)(7,1)・K 内部の 7→8→7 内部再上昇、
    c0 境界でない）。broad+5 サンプル 0 はサンプルが深い再上昇を取り逃すだけ。
  - ⟹ **takeWhile に絞っても proj=NT(msfx) は偽**（内部再上昇が原因）。proj=NT(連続部分列)
    だが「どの部分列か」は再上昇構造依存で、msfx/msfx2/firstmax いずれの単純規則でも不可。
  - **総括**: proj/nrm 値比較ルートの crux（値側減少 for コピー展開）は、proj の値が
    再上昇下で単純なシーケンス特徴づけを持たないため、清潔な term-level 補題で閉じない。
    proj 単調性 on NF は真だが特徴づけ不能。E6_value/msfx 系は全滅。
  - **戦略的結論**: proj/nrm 値比較を介さず、**Buchholz §2 W=T 流の木上直接帰納**を
    PSS の UBI 木（親=nextrel・コピー/上昇=bad-branch）に適応する路線が本筋に見える
    （ユーザー誘導の方向）。p≠ψ ゆえ基本列規則は自作。次セッションはこの Hydra 直接
    帰納の設計（PSS-native な fundamental sequence と W=T 帰納）から。

### (2026-06-13 続85) W=T 直接路線の骨格を確立（wtt.thy・緑・nrm-free）

- **確認**: translate(ST_PS) は標準形でも非NF多数（+3 で 26556/95182・例 D2(D1(...))
  の再上昇）。⟹ nrm は本当に必要・値側 crux 実在。よって W=T 直接路線が正解。
- **既存基盤の発見**: step_terminates_cond は translate 直用（nrm 経由でない）+ dec(証明済)
  + wfimg(NF上<o WF) に帰着。さらに **acc_downward の生成帰納で「M∈ST_PS ⟹ M∈acc(step)」は
  diag 種 accessibility に帰着**（translate/順序/nrm 全て不要）。
- **wtt.thy 新設（YAPSS・緑）**:
  - `stepR = {(T,M). M∈ST_PS ∧ step M T}`。
  - `direct_acc_of_ST_PS`（**証明済**）: diag 種 acc ⟹ 全 ST_PS が acc（生成帰納+acc_downward）。
  - `PSS_terminates_direct`（**証明済**）: diag 種 acc ⟹ wf stepR。
  - `diag_acc`（**OPEN・sorry**）: diagSeq 0 v ∈ acc stepR ＝ W=T の hard core。
  - `PSS_terminates_wtt`: diag_acc から wf stepR。
  ⟹ **PSS 停止性を nrm/順序/translate を一切使わず diag_acc 1点に帰着**。旧 nrm_order_pres
  （第7事件で偽核を含む）を捨て、diag_acc を Buchholz W=T の sum/principal 閉包
  （Lemma 2.4/2.5 の PSS 版）で攻める入口を確立。
- **次の hard core 設計（diag_acc 攻略）**: M[n]=G@B^n のゲームが、より小さいブロック B と
  prefix G のゲームから合成的に停止する composition 閉包。注意: コピー間相互作用
  （cross-copy・bad-root がコピー跨ぎ）が sum-vs-nest と同型の難所になりうる。閉包補題の
  正確な文面設計（B/G の「文脈付き停止」概念）が次の核心。p≠ψ ゆえ Buchholz の dom/[n]
  規則は使わず PSS-native に。

- (続85補) wtt.thy に acc_short（Lng M≤1 ⟹ acc・step不能の基底・証明済）追加。緑。
  diag_acc 攻略の設計（次の本格作業）:
  - **v-帰納案**: diagSeq 0 v の展開は row-1 値を下げる（last col (v,v)・i1=1・row-1 親
    (v-1,v-1)・d0=d1=1 → copies の snd=v-1）。⟹ diagSeq 0 v のゲームは「level v-1
    相当」の形に還元 → v 帰納の見込み。但し還元の各形の accessibility を v-1 から
    導く closure（合成）が要る＝Buchholz Lemma 2.4/2.5 の PSS 版。
  - **closure の難所**: コピー間相互作用（bad-root のコピー跨ぎ）。同じ proof-theoretic
    強度はどの路線でも不可避。closure 補題の正確な文面（B/G の「文脈付き停止」概念）が核心。
  - wf_olt_wf3（証明済）を使うには nrm 橋（nrm_step_dec=crux）が要るため、W=T は
    それを避ける独立証明（Buchholz §2 流の項長/構造帰納）が本筋。

### (2026-06-13 続86) ★crux の正確な局在発見: 再上昇は maxr1≥2 でちょうど出現

- **採掘結果（+3/+5）**: M∈ST_PS の translate が wf3(in_OT) か否かは maxr1 で決まる:
  - **maxr1 ≤ 1: translate は常に wf3**（0 non-wf3 / 91152+821112 @+5）。
  - **maxr1 ≥ 2: 100% 非wf3**（再上昇 D2(D1(...))・199872+160876 @+5 全部）。
- ⟹ **maxr1 ≤ 1 フラグメントは crux なしで停止性証明可能**:
  translate∈wf3・maxr1 は <o 減少で非増加（maxsub_mono_NF）・m_step_decreases（証明済）
  ・wf_olt_wf3（証明済）で直接 WF。nrm 不要。これは v-帰納の底（diagSeq 0 0, 0 1 含む
  全 level≤1 形）。
- **crux は maxr1 ≥ 2 の within-level に正確に局在**（再上昇＝proj/nrm の値比較が破れる所）。
  v-帰納: level≤1 を底に、level k の within-level WF（再上昇込み・crux）を k で帰納。
- **次**: wtt.thy に maxr1≤1 フラグメントの accessibility を形式化（crux-free・実証可能）。
  必要補題: (i) maxr1 M ≤ 1 ⟹ translate M ∈ wf3 (ii) oper は maxr1≤1 を保つ
  (iii) inv_image wf_olt_wf3 translate で subgame WF。

- (続86補) 再上昇は有界でない（crux 完全確認）+ 新ルート候補:
  - translate(M) (maxr1≥2) の principal D_a(b) で **maxsub(b)≥a が 724万件**（D2 の引数に
    D2・再上昇 maxsub(arg)-a 分布 -4..+4）。⟹ within-level peel は同レベルに戻り**還元
    不能**＝wf_ArgsA と同一 crux。maxr1≤1 のみ再上昇なし（クリーン）。
  - **crux の最終同定**: maxr1≥2 同レベル再上昇の within-level WF ＝ wf_ArgsA ＝ nrm_step_dec
    ＝ nrm_order_pres、全て同一の irreducible 核。意味論的には wf_olt_wf3（証明済）で解決済、
    gap は「列ゲーム ↔ 意味論 WF」の橋（nrm 値比較）が再上昇で清潔な特徴づけを持たない点。
  - **新ルート候補（semantic ψ-value, Buchholz §1）**: nrm-項比較を避け、**oV∘translate を
    ψ で順序数として意味論的に定義**（全項で total・ψ 再帰）、減少 oV(translate M[n]) <
    oV(translate M) を **ψ 再帰＋oper 構造で示す**。順序数上では再上昇は ψ が自動 collapse
    するので、nrm-項の非正準問題を回避できる可能性。oV-減少 ≡ nrm_step_dec（命題は同値）
    だが、**証明が順序数側（再上昇 auto-collapse）の方が項側（再上昇で破綻）より tractable
    な可能性**。ord/psi.thy の ψ 機械を使う。次セッションの最有力候補。
  - 並行して maxr1≤1 フラグメント（crux-free・translate∈wf3）は PSI で形式化可能な実成果。

- (続86補2) semantic ルート enabler 確認: **oV は全項 total**（otembed.thy: oV Z=0,
  oV(P a b c)=ψ_a(oV b)+oV c・nrm 不要）。oV_mono は wf3 限定（olt v u∧wf3 ⟹ oV v<oV u）
  だが oV 自体は非wf3 でも値を持つ。⟹ **semantic ルートの具体目標 = oV(translate(M[n]))
  < oV(translate(M))** を、m_step_decreases の <o 減少を ψ-recursion で oV 減少に持ち上げる
  形で示す。wf3 限定の oV_mono は使えない（translate 非wf3）ので、**標準形に特化した
  oV 減少**を別途証明する必要（≡nrm_step_dec だが順序数側証明）。Buchholz §1 の ‖·‖ 減少。
  - 次セッション最有力: この oV 減少を、(a) oper の bad 分岐の項変形を ψ-recursion で
    評価し (b) コピー展開 ψ_a(...)·n < ψ_a(...+1) 型の順序数事実で押さえる、形で攻める。
    PSI セッション（ord/）で otembed の oV/psi を使う。
  - 代替（保険）: maxr1≤1 フラグメント（translate∈wf3・crux-free）を先に形式化＝v-帰納の底。

### (2026-06-13 続87) ★crux irreducibility 確定 — 全ルートが wf3/正準化を要する

- **semantic ルートも crux を回避できない**: oV_order_pres（oV 厳密単調）の証明は
  **wf3 不変量に全面依存**（spinesub_le/Gterm-OT3/headle/wf3_Gterm）。非wf3（再上昇）項では
  oV 厳密単調が崩れる（y₂ collapse: olt だが oV 等値）。⟹ oV(translate M[n])<oV(translate M)
  を出すにも wf3/正準化（=nrm）が必要。
- **結論（確定）**: 3ルート全て同一 crux に収束:
  - nrm 値比較: 再上昇で proj=msfx 等が破綻（第7事件）。
  - W=T 閉包: within-level maxr1≥2 = wf_ArgsA = 同レベル再上昇。
  - semantic oV: oV 厳密単調が wf3 依存・非wf3 で崩れる。
  ＝**再上昇項の正準化（nrm 値比較）が irreducible 核**。repackaging では逃げられない。
- **唯一の前進路**: 再上昇を明示的に場合分けする「正しい messy な nrm_step_dec 証明」
  （旧 nrmstep の 11000 行が偽 E6_value で頓挫した所を、正しい補題で再構築）。これは
  multi-session の大規模形式化。novel insight が無ければ近道なし。
- **当面の確実な実成果**: maxr1≤1 フラグメント（translate∈wf3・crux-free）の accessibility を
  wf_olt_wf3 で形式化（v-帰納の底・PSI セッション）。crux は触らず確実に証明可能な部分。

**今セッション総括（続78〜87）**: (1)健全性第7事件確定・全記録・再発防止恒久化
(2)W=T 骨格 wtt.thy 緑（PSS停止性→diag_acc・reduction証明済・nrm-free）
(3)crux を maxr1≥2 再上昇に完全局在・全ルートで irreducible と確定
(4)残＝再上昇正準化の大規模形式化（または novel insight）。

- (続87補) maxr1≤1 フラグメントも純項では出ない（標準形構造が要る）:
  「subs⊆{0,1} ⟹ wf3」偽（非cnf和）、「cnf+subs⊆{0,1} ⟹ wf3」も偽（D0(D0(D1(0)))で
  OT3違反: G_0 が D1 を引き上げ ¬olt D1(0) (D0(D1(0)))）。⟹ maxr1≤1⟹wf3 は r1ok 等の
  標準形構造に依存（純項補題でない）。base フラグメントすら実質的な形式化を要する。
- **確定**: quick win は無い。全前進路（crux 本体 / maxr1≤1 base）が標準形構造の
  実質的形式化を要する。crux 本体は multi-session の大規模作業（再上昇正準化）、
  soundness 教訓（[[freeze-soundness-lessons]]）に従い拙速を避け careful に。

### (2026-06-13 続88) ★maxr1=0 base を crux-free で形式化（wttbase.thy・PSI 緑）

- **新理論 ord/wttbase.thy（PSI・緑・sorry なし）**:
  - `olt_arg_principal0`（subs⊆{0}: arg < principal）・`olt_tail_principal0`（cnf+subs⊆{0}:
    tail < whole）・`OT3all`（cnf∧wf3∧subs⊆{0} ⟹ Gterm 0 の全元 <o）。
  - **`wf3_of_cnf_subs0`: cnf t ∧ subs t⊆{0} ⟹ wf3 t**（純項・構造帰納・**r1ok 不要**）。
  - **`wf3_translate_subs0`: M∈ST_PS ∧ (∀p. snd p=0) ⟹ wf3(translate M)**
    （cnf_ST_PS + subs_translate + 上記）。
- ＝**maxr1=0 標準形は translate が wf3**＝v-帰納の底を crux なしで確立。
  全添字0で再上昇不能（cnf+subs⊆{0}⟹wf3 は 200項0違反で検証済→形式化完了）。
- wtt.thy 側: `step_level_noninc`（level 非増加）も証明済。
- 次: maxr1=0 フラグメントの accessibility（wf3_translate_subs0 + wf_olt_wf3 +
  m_step_decreases + level非増加で subgame WF）→ maxr1≤1 へ拡張は再上昇境界ぎりぎり
  （maxr1=1 は wf3 だが subs⊆{0,1} で OT3 が D0(D0(D1)) 型を避ける標準構造=r1ok 要）。

- (続88補) wttbase.thy 全数学内容 緑（PSI）: olt_arg_principal0/olt_tail_principal0/
  OT3all/wf3_of_cnf_subs0（純項 cnf∧subs⊆{0}⟹wf3）/wf3_translate_subs0（maxr1=0⟹wf3）/
  **subs0_step_closed**（maxr1=0 フラグメント step 閉包・step_in_ST_PS+oper_snd_subset）/
  **subs0_step_decreases**（フラグメントで (translate T,translate M)∈wf3-<o）。全て sorry なし。
  ⟹ maxr1=0 base の全部品が証明済。残=acc_subs0（これら+wf_olt_wf3 を wf_induct で組む
  accessibility 組立・プラミングのみ・"translate M arbitrary M rule:wf_induct_rule" の
  case 構造で難航中→次回 clean 化）。

- (続88補2) ★**acc_subs0 完成（PSI 緑・sorry 無し）**: `M∈ST_PS ⟹ (∀p∈set M. snd p=0)
  ⟹ M∈acc stepR`。maxr1=0 標準形は全て accessible＝**v-帰納の底を完全証明**（crux-free・
  nrm 不使用）。wf_induct_rule[OF wf_olt_wf3, where P=Q] + subs0_step_closed/decreases で組立。
  教訓: wf_induct は IH が ∀/⟶ 形、wf_induct_rule は meta(⋀/⟹)形—assume と合わせる。
  HO 単一化は where P= で固定。∀N 形は { fix N .. } raw ブロック+blast で導入（intro 回避）。
- これで diagSeq 0 0 ∈ acc（acc_short or acc_subs0）。次: maxr1=1 base（r1ok 要・clean 抽出）
  → level 帰納で diagSeq 0 1、さらに maxr1≥2（crux 本体）。
