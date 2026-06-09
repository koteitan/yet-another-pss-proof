# 参考文献サマリー (conventionals.md)

`../*.pdf` の内容要約。**PDF を再読しなくても本ファイルで足りる**ことを目標とする。
PSS 停止性の WF 核に必要な部分を中心に、実際の定義・補題まで記す。

凡例: `D_v a` = ψ_v(a) = 崩壊関数(添字 v, 引数 a)。`#` = 自然和(可換和)。`P` = 加法的主要数 = {ω^ξ}。

---

## 1. Buchholz 1986「A new system of proof-theoretic ordinal functions」(APAL 32, 195–207) 【route(A) の主軸・精読済】

ψ_v 崩壊関数(v≤ω)と記法系 (OT,<) を導入。極限 = ψ_0(Ω_ω) = Buchholz 順序数 (Π¹₁-CA₀ 相当)。**PSS の上限 ψ_0(ψ_ω(0)) はこれ**。

### §1 順序数としての ψ_v (意味論)
- `Ω_ξ := ℵ_ξ` (ξ>0), `Ω_0 := 1`。`P` = 加法的主要数。
- **C_v(α) の定義** (α に超限再帰, 全 v≤ω 同時):
  - `C_v^0(α) := Ω_v`
  - `C_v^{n+1}(α) := C_v^n(α) ∪ {γ : P(γ)⊆C_v^n(α)} ∪ {ψ_u ξ : ξ∈α∩C_v^n(α) ∧ ξ∈C_u(ξ) ∧ u≤ω}`
  - `C_v(α) := ⋃_n C_v^n(α)`,  `ψ_v α := min{γ : γ∉C_v(α)}`
- **特徴づけ (C1-C3)**: C_v(α) = 最小の X で (C1) Ω_v⊆X, (C2) ξ,η∈X⟹ξ+η∈X, (C3) ξ∈X∩α ∧ u≤ω ⟹ ψ_u ξ∈X。
- **主要補題**:
  - 1.2: ψ_v 0=Ω_v; ψ_v α∈P; Ω_v≤ψ_v α<Ω_{v+1}; α≤β⟹C_v(α)⊆C_v(β)∧ψ_v α≤ψ_v β; γ∈C_v(α)⟺P(γ)⊆C_v(α); +で閉.
  - **1.3 (単調性核)**: `α<β ∧ α∈C_v(α) ⟹ ψ_v α<ψ_v β`.
  - 1.5: `C_v(α)∩Ω_{v+1} = ψ_v α`.
  - 1.7: α<ε_0⟹ψ_0 α=ω^α; α<ε_{Ω_v+1},v≠0⟹ψ_v α=ω^{Ω_v+α}.
  - 1.8/1.9: G_u γ(順序数版, 有限集合)を定義し **γ∈C_u(α) ⟺ G_u γ⊆α**。

### §2 記法系 (OT,<) 【我々の `three` はこれ】
- **項 T**: (T1) 0∈T; (T2) a∈T,v≤ω⟹ `D_v a`∈T (主要項); (T3) a_0..a_k 主要項,k≥1⟹ `(a_0,..,a_k)`∈T (和).
- **順序 < (Def, p.200) — 純粋辞書式, K-domination 無し**:
  - (<1) b≠0 ⟹ 0<b
  - (<2) **`D_u a < D_v b ⟺ u<v ∨ (u=v ∧ a<b)`**  ← 添字優先 lex
  - (<3) a=(a_0..a_n),b=(b_0..b_m): a<b ⟺ [n<m ∧ ∀i≤n.a_i=b_i] ∨ [∃k≤min(n,m). a_k<b_k ∧ ∀i<k.a_i=b_i] (整列列の辞書式)
  - **Lemma 2.1: < は T 上の線形順序**。
- **G_u a (項版, 係数集合, p.201)**:
  - (G1) G_u 0=∅; (G2) G_u(a_0..a_k)=⋃ G_u a_i; (G3) `G_u(D_v b) = {b}∪G_u b (u≤v); ∅ (v<u)`.
- **OT (well-formed 標準形)**:
  - (OT1) 0∈OT; (OT2) a_0..a_k∈OT 主要項,k≥1, **a_k≤..≤a_0** ⟹ (a_0..a_k)∈OT; (OT3) b∈OT ∧ **G_v b<b** ⟹ D_v b∈OT.
  - (`M<a :⟺ ∀x∈M.x<a`)。**OT3 の `G_v b<b` が標準形条件**(= PSS 標準形に対応すべきもの)。
- **o(a) (項→順序数)**: o(0)=0; o((a_0..a_k))=o(a_0)#..#o(a_k); `o(D_v b)=ψ_v o(b)`.
- **Lemma 2.2 (順序保存)**: a,c∈OT で (a) o(a)∈C_0(ε_{Ω_ω+1}); (b) G_u o(a)={o(x):x∈G_u a}; **(c) a<c ⟹ o(a)<o(c)**.
- **Lemma 2.3 (整礎性=順序同型)**: C_0(ε_{Ω_ω+1})={o(x):x∈OT}; a∈OT,a<D_1 0 ⟹ o(a)=ordertype({x∈OT:x<a}); ψ_0 ε_{Ω_ω+1}=ordertype({x∈OT:x<D_1 0}).
  → **o: OT → 順序数 が順序同型**。順序数は整礎 ⟹ (OT,<) 整礎。【これが route(A) の WF 証明】

### §3 強さ (PRWO の Π¹₁-CA₀ 非証明可能性) 【WF には不要】
- `a[z]` (基本列/付値, fundamental sequence), `c_v^n(k):=D_0 D_v...D_v 0[1]..[k]`。
- Theorem 3.1: ID_v ⊬ PRWO(ψ_0 ε_{Ω_v+1})。Cor: Π¹₁-CA₀ ⊬ PRWO(ψ_0 Ω_ω)。
- これは「強さ(独立性)」であって整礎性そのものではない。我々の停止性証明には不要。

**route(A) で要るのは §1(C_v,ψ_v,補題1.2/1.3/1.5)＋§2(OT, o, Lemma 2.2(c), 2.3)**。HOL に順序数(ℵ_v, v≤ω = 非可算基数)が要る。

---

## 2. Towsner「Polymorphic Ordinal Notations」(arXiv 2504.02131v2) 【WF の構文的代替・WF 節精読済】

同じ Buchholz 順序数の記法を2系統で。**順序数を使わない構文的(syntactic)整礎性証明 = distinguished sets**。

### §2 絶対系 OT_{Ω_ω} (= Buchholz §2 とほぼ同じ。ϑ_n, Ω_n を絶対添字で)
- FC(α) (formal cardinality, Def 2.4), K_n α (critical subterms, Def 2.2), 順序 (Def 2.3, Buchholz と同型).
- Key Lemma 2.5/2.7 (substitution, ϑ の単調性) — 動機付けのみ。**§2 には distinguished-set WF 証明は無い**。

### §3 多相系 OT^poly_{Ω_ω} (単一 ϑ ＋ Ω^{(J)} de Bruijn, J≤0) 【構文的 WF の本体】
- Ω^{(J)} = 相対添字の Ω (de Bruijn)。ϑ が J を1減らす。shift α^{≤J}_{±n} (Def 3.3) で添字を平行移動。
- FC^{≤J}, K^{<J}α (Def 3.2/3.4): ϑ をくぐる毎に J 調整。順序 Def 3.5 (Buchholz 型 + shift)。
- ground G(α)=min FC(α); 正規化 α* (ground を 0 に押上げ)。
- **distinguished sets (Def 3.7)**: M_{-∞}=可算項(FC=-∞); n∈ℕ で `M_n = {α : FC(α)=0, G(α)≥-n, {β*:β∈K^{<0}α}⊆⋃_{i<n}Acc_i}`; `Acc_n = M_n の整礎部分`.
- **ladder (構文的, 順序数不要)**:
  - Lemma 3.8: m≤n, α∈Acc_m, β∈Acc_n ⟹ α^{≥0}_{-(n-m)} # β ∈ Acc_n (和で閉).
  - Lemma 3.9: α∈Acc_n ⟹ ω^α∈Acc_n.
  - **Lemma 3.10**: α∈Acc_n ⟹ ϑ(α^{≥0}_{-1})∈Acc_n (同レベル崩壊閉包).
  - **Lemma 3.11**: α∈Acc_n, n>-∞ ⟹ (ϑα)*∈⋃_{m<n}Acc_m (level drop ← de Bruijn shift が効く核).
  - **Theorem 3.12 (master)**: 全 α, 全 n≥G(α*) で α*∈Acc_n (項構造帰納). → 整礎性.
- **重要**: de Bruijn の相対化が shift を Ω-index に吸収し、絶対系で起きる「buried 高添字/負添字」問題を回避する。**絶対系(我々の `ot`)では §3.2 が直接効かない**(我々の循環反例 `acc(ψ_r 0)↔acc(ψ_p(ψ_r 0))` は §3 で解ける)。
- route(B) を採るならこの §3 系へ datatype 移行が必要。

---

## 3. Pohlers「Proof Theory: The first step into impredicativity」(Münster 講義 SS2003) 【教科書・route(A) の参照】

ψ 崩壊と整礎性の標準的教科書。該当章:
- **Ch 3 Ordinals**: 3.3.1 ε_0 以下の記法系, 3.4 Veblen 階層, 3.4.3 Γ_0 以下の記法系 (基礎).
- **Ch 9 Ordinal analysis of ID**: 9.3 半形式系, **9.4 collapsing theorem for ID_1** (ψ/Ω 崩壊), 9.6.1 coding ordinals, **9.6.2 the well-ordering proof** (← 構文的整礎性証明の教科書版, 困ったらここ), 9.7 Ω の別解釈.
- **Ch 11 KP set theory**: 11.10 collapsing for ramified set theory, 11.11 KP の順序数解析 (集合論的崩壊).
- route(A) で意味論的に詰まったら 9.6.2(構文的 well-ordering proof)を参照。Ch3 は Veblen/ε_0 記法の HOL 化の参考。

---

## 4. Carlson「Analysis of a Double Kruskal Theorem」(arXiv 1603.01900v1) 【周辺・強さ側】

- **double forest/tree** (X,≤_1,≤_2): 2つの森順序で ≤_2⊆≤_1 かつ ≤_1-互換。
- **Double Kruskal Theorem**: 有限 double tree 全体は covering(両 ≤_i 保存単射)で wqo。
- **強さ**: Double Kruskal Theorem は ACA_0 上で「Π¹₁-CA₀ の uniform Π¹₁ reflection」と同値、**Π¹₁-CA₀ (=KPℓ_0) と独立**。Simpson [1] 同様に **Buchholz の順序記法を使用**。
- 我々への関係: PSS も同じ Π¹₁-CA₀ 圏 (Buchholz 順序数) という背景証拠。WF 証明自体には不要。

---

## 5. Veldman「An intuitionistic proof of Kruskal's theorem」(Arch. Math. Logic 43, 215–264, 2004) 【周辺・WQO 側】

- Kruskal の定理(有限木は埋込で wqo)の**構成的(直観主義的)証明**。Higman 1952/Kruskal 1960 の議論は構成的に受容可、Nash-Williams の minimal-bad-sequence 論法は要再考、と主張。
- 章: Dickson の補題, almost full relations, Ramsey, 有限列定理, Higman, Vazsonyi予想, Tree Theorem, minimal-bad-sequence論法, 開帰納法原理.
- 我々への関係: wqo/Kruskal の構成的扱い (minimal-bad-sequence vs 開帰納法)。PSS の WF とは別系統だが、整礎性の構成的証明技法の参考。直接は不要。

---

## 6. 我々の形式化への対応 (まとめ)

- **`mechanized.thy` の `three` = Buchholz §2 の T**。`P a b c = D_a(b)+c`。`olt` = Buchholz 順序 (<2)+(<3) **純粋辞書式 (既に線形性 green)**。
- **誤った迂回**: `wo.thy` の `ot` は **K-domination 入り順序 = Buchholz と非互換の私の誤変種**。`buchholz.thy`/`embed.thy` も同様。→ route(A) では破棄候補。
- **NF = translate(ST_PS)** が Buchholz **OT (G_v b<b)** に対応すべき (要確認: 標準形が OT3 を満たす)。
- **route(A) 計画**: 順序数ライブラリ上に §1 の C_v/ψ_v ＋ §2 の o を定義し、**Lemma 2.2(c) `a<c⟹o(a)<o(c)`** で `three` 上の lex 整礎性 (= `proofs.thy` の対角 accessibility) を得る。olt_trans は mechanized で green、op_NF 不要。
- **route(B) (代替)**: Towsner §3 多相系へ移行し distinguished-set (3.8-3.12) で順序数なしの構文的 WF。
