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
