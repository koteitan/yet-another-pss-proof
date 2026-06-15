# 進捗管理

## 注意事項
- 進捗ツリー以外をこのページに書かない。
- **各アイテムはアイテムを区別する情報のみを１行で。それ以上は書かない**（討伐補題名 or blocker を短く。設計の詳細は proof-ja.md・memory へ）。
- 凡例: **各項目には必ず 🚨（未証明）または ✅（証明済）を付ける**。 / 🚨🤖＝ agent 作業中
- 戦略(b)凡例（多相系 polymorphic `ot` へ切替した場合）: 🏺＝移植/作り直しが必要なアイテム / ✨＝その移植により閉じられる（=証明可能になる）アイテム。
  - 背景: Towsner §2（絶対系）には WF 証明が無く、§3.2 の WF は polymorphic 系専用。絶対系では `Om n` が「足場ではなく本物の大元」のため構造帰納の底が無く、Acc_n/M_n レベル構築（数百行）が要る。多相系なら §3.2 がほぼ直接移植でき `wf pR` が閉じる。

## 進捗ツリー
> **サマリ (2026-06-09, route A 確定)**: PSS 停止性 = `proofs.step_terminates`、残 = `wf Rnf`（NF=translate(ST_PS) 上 lex 整礎性）。
> 順序は **Buchholz lex**（`mechanized.three`, olt_trans/total/irrefl 緑）＝旧(1)olt_trans 解決済・旧(3)op_NF は three 直用で不要。
> WF は **route A = Buchholz §1-2 を ZFC_in_HOL 順序数上で意味論的に証明**（`ord/psi.thy`, session PSI）。旧 K-dom `ot`(wo/buchholz/embed) は誤変種で破棄予定。
> 設計詳細・ZFC_in_HOL API・経緯は memo.md / conventionals.md へ。
- 🚨 定理（標準形ペア数列システムの停止性）〔proofs.thy / embed.thy〕
  - ✅ §5 定式化〔def.thy: 親子関係 nextrel0/1・基本列 oper=M[n]・標準形 ST_PS・step〕
  - ✅ 三分木記法 $p_a(b)+c$〔mechanized.thy〕
    - ✅ datatype three = Z | P nat three three（順序を先取りしない命名）
    - ✅ 添字優先順序と線形性〔olt / olt_irrefl・olt_trans・olt_total〕
  - ✅ 変換 translate（森オーダー写像、添字=行1）
    - ✅ 定義＋task 例の sanity〔translate〕
    - ✅ 添字の出所（添字は元の行1値のみ）〔subs / subs_translate〕
  - ✅ 減少補題（translate(M[n]) ≺ translate M、標準形不要の一般形）〔m_step_decreases〕
    - ✅ 末尾追加で増大〔translate_snoc_increase〕
    - ✅ 末尾削除で減少〔translate_butlast_decrease〕
    - ✅ Pred 2 ケース（末尾(0,0)／親なし）〔translate_oper_pred〕
    - ✅ 先頭添字支配（lead が小さければ ≺）〔lead / olt_P_of_lead_lt〕
    - ✅ bad ケース〔translate_oper_bad〕
      - ✅ 文脈合同 BADCTX（G 帰納、根最小条件）〔translate_ctx_cong〕
      - ✅ 単一木補題〔translate_single_tree〕＋局所性〔le0_interval_gt〕
      - ✅ 抽象コア i1=0（正確複製）〔core_i0〕／ i1=1（上昇単一木）〔core_i1〕
      - ✅ oper bad 分岐 → core 接続〔oper_bad_unfold + drop_eq_map_nth + bookkeeping〕
  - 🎯 **★★★最新(続90): PSS 停止性 = 純粋に Buchholz §1 核のみ(構造機械化を全 close)**
    > 多セッション crux `sigma_seqlex_mono` を緑のブロック帰納で証明完成 → 構造的到達性・標準形閉包を全緑化。
    > 残る live sorry は本質的 §1 内容 2つ(`proj_nrm_argzone_olt` §1核 / `keeps_head_ST_PS` tied e=y)のみ。
    > 今セッションで偽補題6件を深層実測で破棄(Cmem_NF/PROJMONO/C1/旧tail_zone[空]/oV(nrm)eq-case/+既知)。
    > ユーザー指摘「§1 移植しても PSS と繋がらない」は正。§1/psi_proj は live path 外。続89 の「2独立ルート」は
    > 続90 sub-agent 2並列で**両者が同一の単一義務に収束**と判明(独立でなかった)。
    - 🚨 **唯一の真の live 核 `sigma_seqlex_mono`**〔nrm.thy〕: M,N∈ST_PS⟹seqlex M N⟹seqlex(σM)(σN)
      〔列・組合せ・深層979300/0〕。nrm_order_pres ⟸ これ。緑 assembly: olt_ST_iff_seqlex/translate_sigma/
      seqlex_imp_olt/untr/sigma/sigma_block_unfold(続90 緑追加)。
    - **核 `oV_mono_NF`**〔ovnf.thy・意味論・3378700/0〕は **sigma_seqlex_mono と同値**: 唯一 TRUE な還元 =
      oV_nrm(oV∘nrm=oV)+wf3_nrm+oV_order_pres+nrm_order_pres ⟸ sigma_seqlex_mono。standalone sorry のまま維持
      (将来の global 意味論攻撃の余地)。緑橋は wt-oV に保存(main 非統合=live sorry 増を避ける)。
    - 🚨 **per-principal/Cmem_NF ルートは偽**で確定(OV agent): NF⊄wf3(2207/10207)・Cmem_NF(93/179 non-canonical)・
      PROJMONO(14739 reversal)全て深層実測で破棄。**標準形(blockok 両row)不変量が本質**、cnf/wf3/r1ok 局所述語不可。
    - ✅ **続90後半: `sigma_seqlex_mono` 緑のブロック帰納証明完成**(SIG2, (S)分解で seqlex_imp_olt 移植)。
      PSS live path を3つの残核に精密局所化(nrm.thy, PSI 緑):
      PSS live path は今や3核のみ(nrm.thy・PSI 緑):
      - 🚨 **`proj_nrm_argzone_olt`**= 唯一の本質的 §1 核(term-level): ST arg-zone で proj∘nrm∘translate が olt 保存・44850/0/0。
        ≡oV_mono_NF。**ARGZ 診断: 既存 §1 sorry(psi_value_acanon/psi_proj_nonmem)に綺麗に還元しない**
        (oV(nrm t)=oV t が必須・それ自体 §1核・oV(nrm BM)が 107/400 non-canonical)⟹ ST arg-zone 不変量を carry した
        proj∘nrm 順序保存を直接攻める。緑補題 olt_iff_oV_wf3(wf3 上 oV が olt 反映)は nrm_argz_reduction_reference.thy.txt に保存。
      - **`keeps_head_ST_PS`**= head 非吸収。y<e 不発(構造)、tied e=y proj比較=§1(STS_B)のみ。
    - ✅ **構造的到達性・標準形閉包を全 close**(続90: SIG2/STRUCT/TAIL/SUF/HP):
      tail_zone_ST_PS / suffix_closure_ST_PS / suffix_oper_witness / suffix_oper_witness_residual 全緑化。
      HP が hasParent_last_ST_PS(ST_PS の全列が最終 index に parent・実測 0/190508)を ST_PS.induct で証明し
      最後の構造残核を vacuous close。緑基盤: nextrel0/1/R_drop_iff・parent_unique・le0_row0_floor・
      row0_zero_imp_row1_zero_ST_PS(floor 不変量)・nextrel0/1_exists。
    - ✅ **続90末: proj_nrm_argzone_olt を緑化・§1核を proj 発火 crux に分解(CORE2)**。compositional:
      - `argzone_val_ge`(ST arg-zone 値境界 y≤v・構造・1013167/0・**独立 closable**)
      - `nrm_argzone_olt`(nrm 単調半=nrm_order_pres one depth down・44850/0/0)
        🚨**循環注意**: depth-1 にブロック帰納を適用すると depth-2 の proj_nrm_argzone_olt に下りる
        ⟹ **深さ一般の統一サイズ帰納に再構成**しない限り独立には閉じない(easy win ではない)。
      - 🚨 `proj_step_argzone_olt` = **唯一の真に既約な §1 wall**(proj y 発火ケース・IST 値境界 carry・61075/0/0)。
        CORE2 負の結果: 局所 term-level 不変量(wf3/subs≥y/P_subdom)では不十分(各 8万〜18万 reversal で偽)、
        **firing-28%(fire×sum-vs-nest, memo 続83)が既約**。proj_emb_mono(embedding 順序)は非発火72%のみ閉じる。
    - **次攻**: (1)argzone_val_ge を ST_PS 帰納で閉じる(構造・closable) (2)sigma_seqlex_mono/nrm_argzone_olt を
      深さ一般の統一サイズ帰納に再構成し §1 を proj_step_argzone_olt 一点に集約 (3)proj_step_argzone_olt 本体
      (fire×sum-vs-nest crux・多セッション wall・lean も停滞・proj_emb_mono で非発火部+発火部の項サイズ場合分け)。
      keeps_head_ST_PS の tied e=y も同核。oV_mono_NF は意味論側同値。
    - soundness: 偽補題 6件(Cmem_NF/PROJMONO/C1[oV(proj∘nrm)=oV]/旧tail_zone_ST_PS[空]/oV(nrm)=oV の eq-case/+既知
      acanon_arg_lt/oV_mono_cnf)を深層 closure+5 で破棄(第7・8事件回避)。
    - **次攻**: (1)suffix_oper_witness_residual を hasParent 存在不変量で閉じる(構造・closable→PSS=純§1)
      (2)proj_nrm_argzone_olt を ST arg-zone 不変量 carry の直接帰納で攻める(§1核・多セッション wall・lean も停滞)。
  - 🗄 §1/psi_proj 路線(続89(21-39)・健全 infra だが live path 外): term_nec/1.4 trio/Cset_eq_Cset_c
    (psi_value_acanon modulo)/B2/wit機構。Buchholz §1 機械化として価値あるが PSS には不要と確定。
  - 🚨 整礎性 wfimg（NF=translate(ST_PS) 上で <o 整礎）★残る未証明
    - ✅ wfimg → 対角 accessibility 還元〔wf_Rnf_from_diag / acc_Rnf_of_ST_PS〕
    - 🚨 **本命＝pure-lex 構文的整礎性（順序数なし, wf.thy, sorry ゼロ・緑）** ［決定 2026-06-10, memory pss-wf-route-purelex-syntactic］
      - ✅ maxsub 単調性 on NF：w<o x ⟹ maxsub w ≤ maxsub x〔olt_imp_slex / nfinv / nfinv_ST_PS / maxsub_mono_NF'〕
      - ✅ CNF：標準形は CNF に翻訳〔cnf / cnf_ST_PS / cnf_oper（i1=0/1 ケース cnf_copies 等）/ cnf_tops_le〕
      - ✅ wf Rnf を「maxsub レベル内 WF」に還元〔wf_Rnf_from_within_level：Rnf=減少部(自明WF)∪同値部〕
      - ✅ wfE（レベル内整礎）→ 和の層を剥離〔wfsum.thy: NF=非増加和 p0(b_i)、olt=lex→multiset 拡張、olt_sum_decomp/olt_sum_mult/wf_level_from_args/wfE_from_args〕
      - ✅ 一般 summand peel＋添字 peel〔summands/olt_summands_mult（cnf だけで非増加）、singdest lex_prod〕
      - ✅ ladder の底＝レベル0 完全証明〔wf_olt0：cnf∧maxsub=0 クラス、PrSS 流 accp+multp（rA0/accp_multp_olt0/sum_acc/sing0_acc/lvl0_acc）〕
      - 🚨 ★残ただ1つ＝`wf_ArgsA`：wf on ArgsA m（崩壊核）。
        - 確定：有限 peel では閉じない／純構文クラスは t_k・x_k 連鎖で不成立（生成依存）／LPO 還元不可。
      - ✅ **柱2: wf_olt_wf3 SORRY-FREE**〔ord/psi.thy+otembed.thy, session PSI〕＝Buchholz Lemma 2.2 自前証明
        （pure-lex olt は Buchholz OT の順序そのもの；wf3=OT クラス上で oV 埋め込み厳密単調；
         C_build＋left-size 主帰納で Ccond 解消；x_k・t_k は wf3 違反で排除）
      - ✅ **柱3: olt_ST_iff_seqlex SORRY-FREE**〔seqlex.thy〕＝標準形上で translate は列 lex からの順序同型
        （blockok 規律: row0≥d・先頭=d・ステップ≤+1；blockok_ST_PS で全標準形が満たす；
         wfE ⟺ ST_PS 上の seqlex 整礎性、と BMS ネイティブに言い換え可能に）
      - 🚨🤖 本丸=(α) 新本線: **値正規化 nrm = NF→OT 順序埋め込み** → 下の「## (α) nrm 路線 進捗ツリー」参照
    - 🗑 旧 K-dom ルート（wo/buchholz/embed・不使用）〔経緯は memo.md 続30〕
  - ✅ 停止性（wfimg ⟹ 停止、減少は discharge 済み）〔step_terminates / no_infinite_expansion / step_terminates_from_diag / step_terminates_via_embed〕
    - ✅ 条件付還元〔step_terminates_cond / no_infinite_expansion_cond〕
    - ✅ step が ST_PS 内に閉じる〔step_in_ST_PS〕

## (α) nrm 路線 進捗ツリー（本丸・ord/nrm.thy + ord/nrmstep.thy）
> **PSS_terminates_nrm = inv_image wf_olt_wf3 (nrm∘translate)**（peel/レベル分解不要）。
> live sorry = nrm_order_pres 1点。攻め筋 = (弱) nrm_step_dec 直接証明（nrmstep.thy・現19 sorry 全て実証済文面）。
> 設計詳細・経緯は memo.md 続19〜続29。
- ✅ nrm 基盤〔nrm定義・proj_id/rec/wf3/G・wf3_nrm（像⊆OT）・PSI 緑〕
- ✅ 実証: 2,643,843 ペアで衝突0・逆転0〔tools/valnorm.py〕
- ✅ PSS_terminates_nrm / wf_Rnf_nrm / nrm_step_dec（order_pres からの導出）
- 🔬 **W=T 直接路線（続85〜88・本線）〔wtt.thy/ord/wttbase.thy・緑〕**: nrm/順序/translate
    を使わず PSS 停止性を **diag_acc**（diag種 accessibility）1点に帰着。
    - ✅ reduction（direct_acc_of_ST_PS / PSS_terminates_direct / acc_short）+ step_level_noninc 証明済。
    - ✅ **maxr1=0 base 完全証明**〔wf3_of_cnf_subs0（純項 cnf∧subs⊆{0}⟹wf3）/ wf3_translate_subs0 /
      subs0_step_closed/decreases / **acc_subs0**（maxr1=0標準形は全accessible）・sorry無・crux-free〕。
    - 🚨 残: maxr1=1 base（r1ok要）→ level帰納 → **maxr1≥2＝crux本体**（再上昇正準化）。
    旧 nrm_order_pres（第7事件で偽核）放棄。
  - 🔬 **§1 / psi_proj ルート（続89・意味論・nrm_order_pres を oV_mono_NF で迂回）〔ord/necessity.thy・nrm.thy〕**
    > 目標 psi_proj: wf3 b ⟹ psi(oV b)a=psi(oV(proj a b))a。section1_plan.md 参照。
    - ✅ scaffolding 緑: bad_imp_oV_ge(B1) / psi_proj_step(A1) / **psi_proj(A2 実証明 modulo nonmem)**〔nrm.thy〕
    - ✅ 構造部品 緑〔necessity.thy〕: indec_Cset_generator / psi_in_Cset_same_sub_generator /
      band_lt_psi(1.5) / psi_eq_of_not_mem(collapsing) / acanon 一式 / **1.4 trio**(psi_inj_canonical
      1.4a・indec_Cset_c_generator 1.4b core・psi_canonical_arg_lt 1.4c) / **Cset_c 全ツールキット**(D-eq-0)
    - ✅ **term_nec(Buchholz 1.9 for wf3 terms)完全緑**〔necessity.thy・sub-agent TN〕: wf3 t⟹
      oV t∈Cv_c α a⟹∀x∈Gterm a t. oV x<α。Cset_c_add_principal_elim(1.2e/g)で G_u 回避。
    - ✅ **Cset_eq_Cset_c(Buchholz Remark)**〔necessity.thy・sub-agent RM・residue 1 sorry〕
    - ✅ **B2 oV_noncanon_of_bad 緑**〔nrm.thy〕: bad係数⟹非canonical。term_nec+Remark で。
    - 🚨🤖 ★残核ただ1つ＝**§1 simultaneous induction**（= residue `noncanon_gen_in_Cset_c_residue`
      〔necessity.thy〕= psi_proj_nonmem〔nrm.thy〕、同一核）。canonical-rep 存在の (α,n)同時超限帰納。
      Buchholz が "can be shown" と省略・lean も停滞。A2/nonmem は canonical witness=oV(proj a b) の
      1.4a 同定に A2 自身を要し irreducibly circular。**sub-agent RES が本丸を攻撃中（G_u 構成 or 同時帰納）**。
  - 🚨 nrm_step_dec 直接証明〔nrmstep.thy〕＝旧値側ルート（凍結・第7事件で偽核含む）
  - 🚨🚨🚨 **健全性第7事件（最重大・続78）**: 旧値側基盤が closure+5/+6 で偽と確定。
    **偽（reachable 反例・モデル検証済）**: E6_value(proj=NT msfx)/E6_mem(msfx∈Gterm)/
    ginv(anchor-max)族/O2/O1P/GAP/GBLK0/ginv_dseg_bound/E6_nbcK_T。機構=row1上昇鎖の
    d0=0完全コピー再上昇。「全sorry +3検証完了」(続77)は本族について**無効**。
  - 🗑 **撤回（上記の偽に依存していた旧✅は全て無効）**: 旧 E6_value/E6_mem/ginv系
    （基盤/oper_bad/修復/ob_cross/qpos/dseg_bound）/nbcK系/O1/O2/GCD/GAP/GBLK0/
    OSC再構成/BT-WIN/BT-WRAP/BTFULL/BTWRAPU/btfullok/G6統一核(E6_G6)/dom_tie/lpl/
    dom_deep/CT/sibrel系凍結。＝アンカーmax型の窓row1上界の族全体（教訓: 続78〜81）。
  - ✅ **健全で残る部品（kernel-checked または深層0違反で検証済）**:
    - ✅ olt層・構造層〔nrm_snoc_seg/ins_olt_mono/einc/eflip/gap/stepsok〕
    - ✅ STS_A / proj_once / proj_submono / proj_ole / proj_nofire（既証明）
    - ✅ NT_shape〔NT(c0#rest)=P(snd c0)(proj(snd c0)(NT K))(NT T)・既証明・分解の背骨〕
    - ✅ NT_dom/NT_hd/NT_tail_lt/NT_noabsorb（C1層・既証明）
    - ✅ NT_prefix_lt〔prefix は <o・既証明・d0=0 base〕
    - ✅ r1ok 基盤（row1規律 0/14558・既証明）/ r1ok_climb（既証明）
    - 🚨 NT_tie_resolved/NT_tie_fdlex〔タイ比較¬olt・深層0違反で真・fdlex は sorry〕
    - 🚨 E6_mem_resolved の **¬olt 部分のみ真**（Gterm帰属部分は偽）
  - 🔬 **新本線: proj 単調性で値側減少を再建（続82〜83）**
    - d0=0 減少構造: **M=G@B@[lp], M[n]=G@B^n**。NT(M[1])<oNT(M)=NT_prefix_lt(真・base)。
      並行 NT_shape 再帰: nofire 階層(167208)は proj=恒等で自明・c0共有でlead一致。
    - ✅(純項・要形式化) **proj_emb_mono**: `x⊑y ⟹ ole(proj u x)(proj u y)`
      （⊑=階層的初期部分項埋込・任意wf3で0違反60609・構造帰納で証明可＝**深層監査不要**）。
      `emb_imp_ole`(x⊑y⟹x≤oy・0違反)も。fire階層406件＋nofire全部をカバー。
    - 🚨 **真の irreducible crux = fire×sum-vs-nest（1218件）**: 最深で M[n]=和(D1(0)+D1(0))
      vs M=入れ子(D1(D0(0)))。proj単調性は真だが⊑で説明できない。proj単調 on NF-class
      は深層頑健に真（再上昇120万/0・broad+5 32万/0）だが任意wf3では偽（埋もれた高subscript）。
    - 🚨 次の鍵: **NF-class の清潔な term-level 特徴づけ**（in_OT＋r1ok由来のsubscript-深さ
      条件）→ その下で proj単調性を証明。次セッションは NF特徴づけの採掘から。
  - 参考: lean-yapss/Lean Nrmstep(sorry0) も dichOK 戦略だが d0=0 未接続で**同じ crux 未解決**
    （advice.md に共有・dichOK も d0=0 完全コピーで偽）。
- 🗑 旧 (β1)Trans級翻訳 / (β2)P進再現 は不要。wf_ArgsA 路線は凍結〔wfsum に残置〕
