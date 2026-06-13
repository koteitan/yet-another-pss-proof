# psi_proj 攻略設計（term 側 collapsing bridge）— 2026-06-13 続89

value route の最終核 `nrm_order_pres`(nrm.thy:169) を割るための設計メモ。
lean-yapss と共有（advice-reply2.md §4 分担）。

## 全体の帰着（確定）
```
PSS_terminates_nrm  (nrm.thy, 緑)
  ⟸ nrm_order_pres : v,u∈NF ⟹ olt v u ⟹ olt(nrm v)(nrm u)     -- 唯一の sorry
```
等価 semantic 版（nrm 不要・wf Rnf 直結）:
```
oV_nf_order_pres : v,u∈NF ⟹ olt v u ⟹ oV v < oV u
```
これを
```
oV_nf_order_pres ⟸ oV_nrm + (oV_order_pres on wf3, 既証明)
oV_nrm : oV(nrm t) = oV t ⟸ oV_ins(加法主要数左吸収, psi_addprinc) + psi_proj
psi_proj : ψ_a(oV b) = ψ_a(oV(proj a b))                       -- collapsing keystone
```
※ ただし oV_nf_order_pres の **order/strictness 部分は NF 構造が本質**
  （proj は wf3/r1ok で非単調・実測。memo 続89(6)）。psi_proj(値等式)とは別に
  NF-strictness の山が残る。psi_proj は pure（NF 不要）の公算大。

## 済み（ord/collapsing.thy・PSI 緑・sorry無）
- `psi_eq_of_Cset_eq`: elts(C_v α)=elts(C_v β) ⟹ psi α v = psi β v。
- `Cset_succ_eq`: α∉C_v(α) ⟹ elts(C_v(succ α)) = elts(C_v α)（Citer_succ_stays 帰納）。
- `collapse_succ` (Buchholz 1.6a): α∉C_v(α) ⟹ psi α v = psi(succ α) v。

## psi_proj への道（残り・term 側）
psi_proj は proj の **1 ステップ** b ⟶ g（g∈Gterm a b, ¬olt g b）ごとに
`ψ_a(oV b) = ψ_a(oV g)` を示し、proj の再帰（size 減少・有限）で合成。
proj は olt（syntactic）で判定するが主張は oV（semantic）— ここが核。

1 ステップを psi_eq_of_Cset_eq に載せるには（subscript=a 固定・argument を oV b↔oV g に）
```
elts (Cset (λξ∈elts(oV b). psi ξ) (oV b) a) = elts (Cset (λξ∈elts(oV g). psi ξ) (oV g) a)
```
が要る（argument 側の C-集合一致）。これは「oV g .. oV b の間が a で非 canonical」型。
collapse_succ の argument 版一般化＋ **1.9 necessity**（C-membership ⟺ Gterm/oV 条件）で
oV b が非 canonical（その係数 g が oV b を超える）であることを使う。

### ★実測の訂正（psiproj.py / perstep.py, 続89(9)）
- **psi_proj（full proj・maxo 規律）は真**: ψ_a(oV b)=ψ_a(oV(proj a(nrm b)))・
  46,033 主項で **0 反例**。proj は nrm.thy:43 通り「bad集合の olt-maxo を取り反復」。
- **✗ 任意 g の per-step は偽**: g∈Gterm a b, ¬olt g b の任意 g で ψ_a(oV b)=ψ_a(oV g) は
  64,262/72,942 で偽。⟹ **per-step は maxo 選択に従う必要**（arbitrary g 厳禁）。
- ✓ **clean fact**: bad な g（¬olt g b）は全て **oV g ≥ oV b**（72,942/72,942）。
  ＝ proj で捨てる係数は値で b 以上＝b が level a で非 canonical の証左。

### 必要な補題（ya-pss 担当・訂正版）
1. **非 canonical 判定**: b が係数 g∈Gterm a b で ¬olt g b を持つ ⟹ oV b ∉ C_a(oV b)
   （oV g ≥ oV b な係数を使う＝閉包外）。これが collapse の起動条件。
2. **collapse 一般化（argument 側）**: oV b ∉ C_a(oV b) かつ proj が canonical fixpoint
   （Gterm a(proj)<proj, proj_G 済）に到達 ⟹ ψ_a(oV b)=ψ_a(oV(proj a b))。
   collapse_succ の argument 版＋ maxo 鎖。C_a^{arg}(oV b)=C_a^{arg}(oV(proj)) を示す。
3. **1.9 necessity**（C-membership ⟺ Gterm/oV 条件）が 1.2 の土台。C-rank 帰納
   （psi.thy Citer/Cset_mem_iff）。term 側は oV/Gterm(otembed)。
これらで psi_proj。検証: tools/psiproj.py, perstep.py。

### lean 担当（advice-reply.md §3）
- 1.4(b) canonical witness / C-集合同値（1.4(a) psi_canonical_inj 済を活用）。

### 続89(16): ★psi_proj を per-maxo-step に精密帰着（proj.induct）
psi_proj (ψ_a(oV b)=ψ_a(oV(proj a b))) を proj.induct で分解:
- base（bad={g∈Gterm a b:¬olt g b}=∅, proj a b=b）: 自明（両辺同じ）。
- step（bad≠∅, proj a b = proj a (maxo bad)）: IH で ψ_a(oV(maxo bad))=ψ_a(oV(proj a(maxo bad)))。
  ⟹ 残り = **per-maxo-step `ψ_a(oV b) = ψ_a(oV(maxo bad))`**（m:=maxo bad∈Gterm a b, ¬olt m b）。
- wf3 b なら ¬olt m b ⟹ oV b ≤ oV m（oV_order_pres 逆）。m∈Gterm a b（構造的係数）。
- **これが irreducible core**: ψ_a(oV b)=ψ_a(oV m), oV b≤oV m, m∈Gterm a b。
  道具候補: collapse_succ/grow（gap [oV b,oV m) 非canonical を要するが確立が肝＝canonical-rep）。
  proj_canonical（proj a b は a-canonical・証明済）は psi_strict_mono_arg 適用の足場。
  残課題: gap 非canonical or C_a(oV b)=C_a(oV m) の確立。Lean も同地点。

### 続89(15): ψ §1 toolkit 構築進捗（necessity.thy・PSI 緑sorry無・全て自前/独立）
- **collapse**（collapsing.thy）: psi_eq_of_Cset_eq / Cset_succ_eq / collapse_succ(1.6a) /
  Cset_grow_eq / collapse_grow（一般 collapsing）。
- **n-copies**（necessity.thy）: indec_mult_nat / indec_psi_mult(ψ_β·n<ψ_(succ β)) /
  indec_psi_mult_add。＋ indecomposable_psi。
- **★1.4(a) injectivity**（necessity.thy）: psi_inj_subscript（Ω-range で subscript 決定）/
  psi_inj_arg_canonical（canonical 引数で arg 決定）/ psi_inj_canonical。
- **残る intricate core = 1.4(b) canonical-rep 構成**:
  1.9 necessity → 1.4(b)（C-元の ψ-arg は canonical rep に collapse）に帰着。
  これは「非 canonical ξ に対し ψ_ξ u = ψ_{ξ°} u, ξ° canonical」＝**ordinal collapse**で、
  collapse_grow が道具だが **ξ°（canonical rep）の構成**が肝（gap [ξ°,ξ) 非canonical を示す）。
  lean も「canonical-rep 構成で詰まる」（advice-reply §2）＝両者の共通 intricate 核。
  我々の Cstep は canonicity 省略（psi.thy:54）なので、full-gen=canonical-gen Cset 同値
  （Buchholz Remark p.197）を示すか canonical-rep を構成する必要。**ここが本丸**。

### 続89(14): oV-route 直接攻略の assembly 計画（nrm/necessity を迂回）
finding(13)で wf3(translate)/nrm_order_pres は ST_PS 固有・blockok 不可と確定。⟹ general
necessity(1.9)経由は canonical-witness の沼。**代わりに oV step-decrease を oper 構造で直接**:
- 目標(termination 十分): `oV(translate(M[n])) < oV(translate M)`（step 対のみ・wf Rnf 不要、
  inv_image VWF oV で直接 wf step 関係）。実測 bulletproof（98910 step 0 反例）。
- 構造: `oper_bad_blocks`(mechanized.thy:998) が
  `M = G@((v0,w0)#R)@[lp]`, `M[n]=G@(n 個 shifted copies, shift=k*d0 in row-0, row-1 不変)`,
  `∀x∈R. v0<fst x`, `v0<fst lp`, `d0=0 ∨ (0<d0 ∧ w0<snd lp ∧ fst lp=v0+d0)` を与える。
- **済の順序数 toolkit**: indec_mult_nat / indec_psi_mult (ψ_β·n<ψ_(succ β)) /
  indec_psi_mult_add (ψ_β·n+δ<ψ_(succ β)) / collapse_succ / collapse_grow / indecomposable_psi。
- **計画**:
  - (i) translate-block-value 橋: translate(G@blocks) の oV を block 構造で表す
    （translate の takeWhile/dropWhile 再帰を値側へ。seqlex_imp_olt の blockok_arg/tail 帰納が雛形）。
  - (ii) d0=0 ケース（同一コピー・re-climb 無し）: n 個の同一主項 = ψ_w0(arg)·n、原 M の lp が
    ψ_w0(arg+1) 型を作る ⟹ **indec_psi_mult で直接減少**。clean。
  - (iii) d0>0 ケース（row-0 ramp・re-climb・非wf3）: 埋没する大項を **collapse_succ/grow** で
    値保存しつつ畳む ⟹ 同様に n-copies 減少。**ここが本丸**。
  - 残り課題: (i) の translate-value 橋（mechanized の translate 再帰を要する）。これが次の山。
- 利点: nrm/proj/general-necessity/canonical-witness を全て迂回。値(oV)と ψ-collapse のみ。
  green toolkit が既にある。欠点: translate-value 橋 + d0>0 collapse 接続が substantial。

### ✗続89(11) 訂正: 続89(10) の (B) reduction は欠陥あり
- 「(B) ψ_{a'}(ζ)∈C_v(α)∧v≤a' ⟹ ζ<α」は **偽**。generator ケース ψ_{a'}(ζ)=ψ_u(ξ)
  (ξ<α) で、value の range により a'=u は出る（ψ_v(α)∈[Ω_v,Ω_{v+1}) が排他・
  psi_lt_Om_Suc+Om_le_psi+Om_mono）が、**引数 injectivity は canonical 限定**。
  α が collapse 領域（ψ_{a'} が [ξ,α] で一定）なら ζ≥α が起こり得る ⟹ ζ<α は偽。
- ⟹ 1.9 necessity は **canonical-rep 依存**（Buchholz は K 関数/canonical witness で
  慎重に証明）。私の (B) clean reduction は gap あり。indecomposable_psi で sum/Om を
  消す部分は正しいが、generator ケースは canonical witness（1.4b・lean が保留した方）が
  実は要る可能性が高い。necessity は当初想定より intricate。要 careful 再設計。
- 教訓（[[freeze-soundness-lessons]]）: 順序数 §1 の quick reduction は危険（第7事件と同型の
  over-confident 誤り）。各 step を慎重に・できれば検証してから形式化。

### 続89(10): 1.9 necessity を ψ-injectivity 一点に reduce（necessity.thy）【※(B) は上記で訂正】
necessity（C_build の逆: oV t∈C_v(α) ⟹ ∀x∈Gterm v t. oV x<α）の分解を精密化:
- **(B) psi-arg necessity**: ψ_{a'}(ζ)∈C_v(α) ∧ v≤a' ⟹ ζ<α。Citer n 帰納で:
  - n=0 (∈Om v): a'≥v ⟹ ψ_{a'}(ζ)≥Om a'≥Om v ⟹ ∉elts(Om v)。**矛盾で消える**（psi_lt_Om_Suc/Om_le_psi）。
  - sum ξ+η: ψ_{a'}(ζ) は **indecomposable_psi**（証明済）⟹ ξ or η が 0/δ ⟹ Citer n に帰着（IH）。
  - generator ψ_u(ξ), ξ∈Citer n∩elts α (ξ<α): ψ_{a'}(ζ)=ψ_u(ξ) ⟹ **ψ-injectivity で ζ=ξ<α**。
  ⟹ **(B) は ψ-injectivity (Buchholz 1.4a) 一点に帰着**。sum/Om は Isabelle で処理可能。
- **ψ-injectivity = lean の psi_canonical_inj（証明済）**。Isabelle に無い唯一の primitive。
  ⟹ lean から 1.4a 証明構造を貰って port するのが最効率（独立再証明は canonical-witness の
  難所で重複）。
- **(A) leading 成分抽出**: Citer 帰納＋Cantor_NF（indecomposable_psi で接続済）。(B) と独立に進められる。
- necessity.thy 済: indecomposable_psi（ψ値=加法主要数, Cantor_NF 接続）。

## 注意（freeze-soundness-lessons）
- 旧 nrmstep の syntactic 攻略（E6_value=proj=NT msfx）は **偽**（closure+5/6 反例）。
  本設計は値（oV/ψ）側で組む。各補題は実測（tools/）で +5 検証してから形式化。
- 1.9 necessity は Buchholz の実質部分・intricate。monolithic 厳禁・小補題ごと kernel 確認。
