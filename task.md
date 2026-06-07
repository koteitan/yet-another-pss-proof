# 進捗管理

## 注意事項
- 進捗ツリー以外をこのページに書かない。
- **各アイテムはアイテムを区別する情報のみを１行で。それ以上は書かない**（討伐補題名 or blocker を短く。設計の詳細は proof-ja.md・memory へ）。
- 凡例: **各項目には必ず 🚨（未証明）または ✅（証明済）を付ける**。 / 🚨🤖＝ agent 作業中

## 進捗ツリー
- 🚨 定理（標準形ペア数列システムの停止性）〔proofs.thy〕
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
  - 🚨 整礎性 wfimg（NF = translate(ST_PS) 上で ≺ 整礎）★残る未証明
    - ✅ wfimg → 対角 accessibility への還元（oper側は減少補題で無料）〔wf_Rnf_from_diag / acc_Rnf_of_ST_PS / oper_eq_self_short〕
    - ✅ 補助: maxsub 単調性 on NF・within-level 還元（旧ルート、現在は Towsner ルートで直接 wf を狙う）〔wf.thy: maxsub_mono_NF / wf_Rnf_from_within_level / nfinv_ST_PS / spine_translate_eq 等〕
    - 🚨 **Towsner distinguished-set WF 核**〔wo.thy〕（NF⊄Buchholz OT 判明→別 datatype `ot` で整礎順序を組み NF を埋め込む）
      - ✅ 記法 `ot`(Om/Th/Su)・FC・critical subterms Kn・Kn_size〔wo.thy〕
      - ✅ K 条件付き真の整礎順序 `<\<^sub>o`（Towsner Def 2.3）を function+termination で定義〔olt / ole〕
      - ✅ Zero 最小性・和順序 ⊆ multiset 拡大〔not_olt_Zero / olt_Zero_iff / olt_Su_imp_mult〕
      - ✅ **assembly**: `wf principalR ⟹ wf {(a,b). a<\<^sub>o b ∧ wfo a ∧ wfo b}`〔wfo / bag / bag_mono / wf_olt_of_principal〕
      - 🚨 **`wf principalR`**（Om/Th 上の整礎性）★残る本丸＝Towsner Lemma 3.10–3.12（ϑ 崩壊、Acc_n/M_n 入れ子帰納。M_n の absolute 再構成）
    - 🚨 **埋め込み `three → ot` の順序保存**〔embed.thy〕
      - ✅ embed/eprincs/collapse（単一 principal は Su 化しない）＋像の well-formed〔wfo_embed〕
      - 🚨 NF 上で `w ≺ x ⟹ embed w <\<^sub>o embed x`（NF でのみ素朴 lex=真順序。off-NF は bad chain で不成立を確認）→ `wf Rnf`
  - ✅ 停止性（wfimg ⟹ 停止、減少は discharge 済み）〔step_terminates / no_infinite_expansion / step_terminates_from_diag〕
    - ✅ 条件付還元〔step_terminates_cond / no_infinite_expansion_cond〕
    - ✅ step が ST_PS 内に閉じる〔step_in_ST_PS〕
