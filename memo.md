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
  ビルド: `cd git && isbman build -m .. -d /home/koteitan/afp-dl/afp-2026-06-05/thys -d /home/koteitan/ya-pss/git PSI`（**-d は絶対パスで**, cwd 不安定なため）。ZFC_in_HOL ヒープは git ディレクトリの isbman 隔離heapにキャッシュ済(再ビルド ~40s, PSI のみ ~1-10s)。
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
