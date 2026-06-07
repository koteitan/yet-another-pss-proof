# 進捗管理

## 注意事項
- 進捗ツリー以外をこのページに書かない。
- **各アイテムはアイテムを区別する情報のみを１行で。それ以上は書かない**（討伐補題名 or blocker を短く。設計の詳細は proof-ja.md・memory へ）。
- 凡例: **各項目には必ず 🚨（未証明）または ✅（証明済）を付ける**。 / 🚨🤖＝ agent 作業中
- 戦略(b)凡例（多相系 polymorphic `ot` へ切替した場合）: 🏺＝移植/作り直しが必要なアイテム / ✨＝その移植により閉じられる（=証明可能になる）アイテム。
  - 背景: Towsner §2（絶対系）には WF 証明が無く、§3.2 の WF は polymorphic 系専用。絶対系では `Om n` が「足場ではなく本物の大元」のため構造帰納の底が無く、Acc_n/M_n レベル構築（数百行）が要る。多相系なら §3.2 がほぼ直接移植でき `wf pR` が閉じる。

## 進捗ツリー
> **現状サマリ (2026-06-08)**: 停止性は **end-to-end で 2 義務に還元・コミット済**
> （`embed.step_terminates_via_embed`）: PSS 停止性 ⟸ **(1) `masterF`**（Om-free 項の
> Buchholz WO 核, 真の sorry）＋ **(2) `op`**（embed の NF 上順序保存, 仮定）。
> 基盤（shift 順序自己同型・acc 不変・ground/norm/width・omfree・distinguished-set 定義）は全て証明済。
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
  - 🚨 整礎性 wfimg（NF = translate(ST_PS) 上で ≺ 整礎）★残る未証明
    - ✅ wfimg → 対角 accessibility への還元（oper側は減少補題で無料）〔wf_Rnf_from_diag / acc_Rnf_of_ST_PS / oper_eq_self_short〕
    - ✅ 補助: maxsub 単調性 on NF・within-level 還元（旧ルート、現在は Towsner ルートで直接 wf を狙う）〔wf.thy: maxsub_mono_NF / wf_Rnf_from_within_level / nfinv_ST_PS / spine_translate_eq 等〕
    - 🚨 **distinguished-set WF 核**〔wo.thy/buchholz.thy〕（§3.2 を絶対系 `ot` に「書き換え転写」: ユーザー決定 2026-06-08）
      - ✅ 記法 `ot`(Om int/Th int/Su)・FCset・FC・critical subterms Kn・Kn_size〔wo.thy〕（**int 化済**: shift に負添字が要る）
      - ✅ K 条件付き整礎順序 `<\<^sub>o`（Towsner Def 2.3）function+termination〔olt / ole〕
      - ✅ Zero 最小性・Kn 単調補題群〔not_olt_Zero / olt_Zero_iff / Kn_lt_Th / Kn_mono_le / KnTh / Kn_le_self / olt_Th_of_le_Kn〕
      - ✅ **shift（Towsner Def 3.3 global）＝順序自己同型**〔wo.thy: shift / shift_shift/0/inv/inj/isH/eq/eqTh/eqOm/FCset/Kn / **shift_olt**〕＝正規化の基盤
      - ✅ **汎用 acc 基盤**〔accinfra.thy〕（記法非依存・再利用）
      - ✅ **和→principal 還元**〔wflevel.thy: wfo_Kn / bag_mono_w / acc_of_bag_elems / princ_acc_lift / **wf_oltRw_of_wf_pR** / wf_oltRw_of_principals〕＝ `wf pR ⟹ wf oltRw`（int で緑）
      - ✅ ground `gnd`(=Min FCset)・正規化 `norm`(=shift(-FC), top→0)・width `wdt`(=FC-gnd)〔wo.thy, +FC_shift/gnd_shift/wdt_shift/FC_norm〕
      - ✅ **shift＝順序自己同型 `shift_olt`** ＋ `shift_wfo`/`acc_shift`/`acc_shift_pR`〔wo/buchholz, ground 正規化の基盤〕
      - ✅ distinguished-set 定義 Mn/AccB/Acc（ground 階層）＋単調性＋generic `Awf`/`wf_on_Awf`〔buchholz〕
      - ✅ **致命バグ修正**: `Om int` で全体 `wf pR` は偽（`Om 0>Om(-1)>…` 無限降下）。embed 像は **Om-free**（`omfree_embed`）＝可算。WF 対象を **Om-free 項** に制限〔`omfree`/`oltRwF`/`pRF`〕
      - 🚨 **`masterF`**（= Buchholz WO 核, 真の sorry）: 全 Om-free wfo 項が `oltRwF`-acc。構造帰納＋Su は bag 還元＋Th は §3.7 distinguished-set（Lemma 3.10/3.11, Ω scaffold＋norm/shift）。★残る本丸ただ一つ
      - ✅ `wf_oltRwF`（masterF から）〔buchholz〕
    - 🚨 **埋め込み `three → ot` の順序保存**〔embed.thy〕
      - ✅ embed/eprincs/collapse＋像の well-formed〔wfo_embed〕＋**Om-free〔omfree_embed〕**（int 化済: `Th (int a) ...`）
      - ✅ **`wf_Rnf_via_embed`**: `wf Rnf` ⟸ `op`（NF 上 `w≺x ⟹ embed w<\<^sub>o embed x`）のみ（wf_oltRwF＋omfree_embed で配線済、偽の wf oltRw 仮定は除去）
      - ✅ **`step_terminates_via_embed`**: PSS 停止性 ⟸ `op` （end-to-end, masterF が唯一の内部 gap）
      - 🚨 **`op`**（NF 上順序保存, 残 2 義務の一つ）
  - ✅ 停止性（wfimg ⟹ 停止、減少は discharge 済み）〔step_terminates / no_infinite_expansion / step_terminates_from_diag / step_terminates_via_embed〕
    - ✅ 条件付還元〔step_terminates_cond / no_infinite_expansion_cond〕
    - ✅ step が ST_PS 内に閉じる〔step_in_ST_PS〕
