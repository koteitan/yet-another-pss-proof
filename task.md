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
  - 🚨 整礎性 wfimg（NF=translate(ST_PS) 上で <o 整礎）★残る未証明
    - ✅ wfimg → 対角 accessibility 還元（oper 側は減少補題で無料）〔wf_Rnf_from_diag / acc_Rnf_of_ST_PS〕
    - 🚨 **Buchholz 整礎性（route A=意味論, ord/psi.thy, session PSI on ZFC_in_HOL）**
      - ✅ Ω_v=ℵ_v ＋単調〔Om / Ord_Om / Card_Om / Om_less_Suc〕
      - ✅ C_v(α)/ψ_v 定義＋well-defined〔Cstep / Cset / psi / psi_unfold / psi_ex / Ord_psi / psi_notin〕
      - ✅ 閉包 C1-C3＋Cset⊆Ord〔Om_subset_Cset / Cset_add_closed / Cset_psi_closed / Cset_Ord〕
      - ✅ Ω_v≤ψ_v α〔Om_le_psi〕＋C の α 単調〔Cstep/Citer/Cset_mono_param, CC_mono〕＋ψ_v α 単調〔psi_mono_arg〕
      - ✅ Lemma 1.3（ψ_v 厳密単調 α<β∧α∈C_v α⟹ψ_v α<ψ_v β）〔psi_strict_mono_arg〕＝順序保存の核
      - ✅ Lemma 1.2(c)（ψ_v α<Ω_{v+1}＝基数 |C_v α|≤κ）〔psi_lt_Om_Suc／vcard_Citer_le・vcard_Cset_le・gcard_*' ローカル複製〕
      - ✅ §2 skeleton 緑：oV:three→V／wf_Rnf／PSS_terminates〔ord/otembed.thy, three+V クロスセッション via YAPSS.proofs〕
      - 🚨 ★唯一の残 sorry：oV_order_pres_NF（Lemma 2.2c 順序保存 on NF）。要：1.2(b)加法主要数・1.3 C条件・OT降順
      - ✅ Lemma 1.2(b)(ψ_v 加法主要数 psi_add_principal)＋below_psi_in_Cset〔決定的tactic, runaway回避済〕
      - 🚨 補助：C条件 o b∈C_a(o b) / NF⊆OT(降順) → 2.2c へ
    - 🗑 旧ルート（K-dom `ot`, 誤変種で破棄予定）〔wo/buchholz/embed: L_ThF・op_NF 残 sorry, masterF/wf_oltRwF/cnf_ST_PS は緑だが route A では不使用〕
  - ✅ 停止性（wfimg ⟹ 停止、減少は discharge 済み）〔step_terminates / no_infinite_expansion / step_terminates_from_diag / step_terminates_via_embed〕
    - ✅ 条件付還元〔step_terminates_cond / no_infinite_expansion_cond〕
    - ✅ step が ST_PS 内に閉じる〔step_in_ST_PS〕
