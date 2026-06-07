# 進捗管理

## 注意事項
- 進捗ツリー以外をこのページに書かない。
- **各アイテムはアイテムを区別する情報のみを１行で。それ以上は書かない**（討伐補題名 or blocker を短く。設計の詳細は proof-ja.md・memory へ）。
- 凡例: **各項目には必ず 🚨（未証明）または ✅（証明済）を付ける**。 / 🚨🤖＝ agent 作業中
- 戦略(b)凡例（多相系 polymorphic `ot` へ切替した場合）: 🏺＝移植/作り直しが必要なアイテム / ✨＝その移植により閉じられる（=証明可能になる）アイテム。
  - 背景: Towsner §2（絶対系）には WF 証明が無く、§3.2 の WF は polymorphic 系専用。絶対系では `Om n` が「足場ではなく本物の大元」のため構造帰納の底が無く、Acc_n/M_n レベル構築（数百行）が要る。多相系なら §3.2 がほぼ直接移植でき `wf pR` が閉じる。

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
      - ✅🏺 記法 `ot`(Om/Th/Su)・FC・critical subterms Kn・Kn_size〔wo.thy〕（多相系: `Ω(J)` de Bruijn＋単一 `ϑ` に作り直し）
      - ✅🏺 K 条件付き真の整礎順序 `<\<^sub>o`（Towsner Def 2.3）を function+termination で定義〔olt / ole〕（多相系: Def 3.5 に作り直し）
      - ✅🏺 Zero 最小性・和順序 ⊆ multiset 拡大〔not_olt_Zero / olt_Zero_iff / olt_Su_imp_mult〕（順序定義依存→作り直し。和⊆multiset の骨格は流用可）
      - ✅ **汎用 acc 基盤**〔accinfra.thy: acc_imp_acc_trancl / acc_pullback / acc_mult_of_elems（要素ごと multiset 整礎）〕（記法非依存→**そのまま再利用**）
      - ✅🏺 **和への還元**〔wflevel.thy: wfo_Kn / bag_mono_w / acc_of_bag_elems / princ_acc_lift / **wf_oltRw_of_wf_pR**〕＝ `wf pR ⟹ wf oltRw`（順序依存→作り直し。構造はそのまま移植可）
      - 🚨✨ **`wf pR`**（well-formed principal 順序 = Om/Th 上の整礎性）★残る本丸＝古典 Buchholz WF（**多相系へ移植すれば §3.2 Lemma 3.8–3.12 をほぼ直接移植で閉じる**）
        - ✅🏺 FC 階層化補題群〔Kn_isH / FCset_Kn / FC_Kn / FCset_Th_eq_Kn / FC_Th_le / **FC_mono_pr** / Kn_lt_Th〕（多相系 FC/G で再証明）
        - 🚨✨ 入れ子帰納（崩壊補題 L_Th）：絶対系では構造帰納＋引数 acc 帰納＋述語 size 帰納＋添字/FC（同FC・異添字 p<n・同FC の `Om N` が壁）。**多相系では §3.2 の Acc_n/M_n 直接移植に置換され閉じる**
    - 🚨 **埋め込み `three → ot` の順序保存**〔embed.thy〕
      - ✅🏺 embed/eprincs/collapse（単一 principal は Su 化しない）＋像の well-formed〔wfo_embed〕（多相系: `P a b c ↦ ϑ(Ω#…)` へ作り直し）
      - 🚨🏺 NF 上で `w ≺ x ⟹ embed w <\<^sub>o embed x`（NF でのみ素朴 lex=真順序。off-NF は bad chain で不成立を確認）→ `wf Rnf`（多相 `ot`・de Bruijn 向けに作り直し）
  - ✅ 停止性（wfimg ⟹ 停止、減少は discharge 済み）〔step_terminates / no_infinite_expansion / step_terminates_from_diag〕
    - ✅ 条件付還元〔step_terminates_cond / no_infinite_expansion_cond〕
    - ✅ step が ST_PS 内に閉じる〔step_in_ST_PS〕
