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

### 必要な補題（ya-pss 担当）
1. **collapse 一般化（argument 側・任意 gap）**: 連続区間でなく proj の有限鎖で十分。
   per-step: `oV g ≤ oV b ∧ (oV b ∈ [closure of oV g at a]) ⟹ ψ_a(oV b)=ψ_a(oV g)`。
   ＝ C_a^{arg}(oV b)=C_a^{arg}(oV g)。collapse_succ の argument 版。
2. **1.9 necessity**（順序数 or term 側）: `γ∈C_v(α) ⟹ G_v γ ⊆ elts α`。
   C-rank 帰納（psi.thy の Citer/Cset_mem_iff 機構が土台）。term 側は oV/Gterm(otembed)。
3. これらで psi_proj を組む。

### lean 担当（advice-reply.md §3）
- 1.4(b) canonical witness / C-集合同値（1.4(a) psi_canonical_inj 済を活用）。

## 注意（freeze-soundness-lessons）
- 旧 nrmstep の syntactic 攻略（E6_value=proj=NT msfx）は **偽**（closure+5/6 反例）。
  本設計は値（oV/ψ）側で組む。各補題は実測（tools/）で +5 検証してから形式化。
- 1.9 necessity は Buchholz の実質部分・intricate。monolithic 厳禁・小補題ごと kernel 確認。
