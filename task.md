# 進捗管理

## 注意事項
- 進捗ツリー以外をこのページに書かない。
- **各アイテムはアイテムを区別する情報のみを１行で。それ以上は書かない**（討伐補題名 or blocker を短く。設計の詳細は proof-ja.md・memory へ）。
- 凡例: **各項目には必ず 🚨（未証明）または ✅（証明済）を付ける**。 / 🚨🤖＝ agent 作業中
- 戦略(b)凡例（多相系 polymorphic `ot` へ切替した場合）: 🏺＝移植/作り直しが必要なアイテム / ✨＝その移植により閉じられる（=証明可能になる）アイテム。
  - 背景: Towsner §2（絶対系）には WF 証明が無く、§3.2 の WF は polymorphic 系専用。絶対系では `Om n` が「足場ではなく本物の大元」のため構造帰納の底が無く、Acc_n/M_n レベル構築（数百行）が要る。多相系なら §3.2 がほぼ直接移植でき `wf pR` が閉じる。

## 進捗ツリー
> **現状サマリ (2026-06-08, 致命バグ修正後)**: PSS 停止性 `embed.step_terminates_NF`、
> 内部 sorry **3つ**（他全証明済・緑）。**重要修正**: WF target を非負添字フラグメントに変更（下記）。
> **(1) `wo.olt_trans[c=Su[a=Su]]`**（順序メタ理論; **headline 非依存**＝dead, 完成不要）、
> **(2) `buchholz.L_ThF[p<n]`**（Buchholz ϑ 崩壊核; **修正後 0≤p<n で真**, level machinery 要）、
> **(3) `embed.op_NF[P/P]`**（embed の NF 順序保存; Z ケース済, 経験的に 0 反例）。
> **🚨致命バグ修正済 (commit)**: 旧 `oltRwF`(omfree のみ) は **ill-founded**（`Th(-k)0` 無限降下）
> ＝ `wf_oltRwF`/`masterF` は偽で、L_ThF sorry 経由で緑だった（L_ThF は「難」でなく「偽」だった）。
> **修正**: `nneg`(全添字≥0) を target に追加（`wo.nneg`/`nneg_Kn`, `nneg_embed`, oltRwF/masterF/L_ThF/
> bag_mono_wF に thread）。これで architecture は **健全**, L_ThF p<n は真の目標に。
> 基盤（shift 自己同型・acc 不変・ground/norm・nneg fragment・reduction chain・cntbl_downclosed）は全証明済。
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
      - 🚨 **順序メタ理論**（出典: Buchholz [Buc1] Lemma 2.1）: `olt_Om_mono`✅, `olt_asym`/`olt_irrefl`✅(無条件,但し olt_trans 依存)。
        **`olt_trans` 残 sorry = c=Su[a=Su]（Su/Su/Su 単一支配元推移）1つ**（他8ケースは size 帰納で証明済）。
        **続23 確定方針**: olt_trans を **wfo 制限版 `olt_trans_wf`** に置換（下流=buchholz/embed/op_NF は全 wfo、無条件版は不要と確認）。
        Su/Su は **multp_HO bridge**: `olt_Su_imp_multp\<^sub>H\<^sub>O`✅(forward)＋`multp\<^sub>H\<^sub>O_imp_olt_Su`✅(reverse, 要 asym+trans+mnlcong)。
        carrier 仮説は **combined size 帰納(trans_wf∧asym_wf∧mnlcong_wf 同時)** で供給（distinct 三項は size 和<total で IH、x=z は asym で vacuous）。
        **経験的事実(python)**: mnlcong は wfo で真/非 wfo で偽；wfo 順序は **置換合同 ~ を法に線形**（`Th p c~Th p c'` if `c~c'`）。
        ~150-250 行。scratch_trans.thy に bridge 配線雛形。★3義務の一つ
      - ✅ Zero 最小性・Kn 単調補題群〔not_olt_Zero / olt_Zero_iff / Kn_lt_Th / Kn_mono_le / KnTh / Kn_le_self / olt_Th_of_le_Kn〕
      - ✅ **shift（Towsner Def 3.3 global）＝順序自己同型**〔wo.thy: shift / shift_shift/0/inv/inj/isH/eq/eqTh/eqOm/FCset/Kn / **shift_olt**〕＝正規化の基盤
      - ✅ **汎用 acc 基盤**〔accinfra.thy〕（記法非依存・再利用）
      - ✅ **和→principal 還元**〔wflevel.thy: wfo_Kn / bag_mono_w / acc_of_bag_elems / princ_acc_lift / **wf_oltRw_of_wf_pR** / wf_oltRw_of_principals〕＝ `wf pR ⟹ wf oltRw`（int で緑）
      - ✅ ground `gnd`(=Min FCset)・正規化 `norm`(=shift(-FC), top→0)・width `wdt`(=FC-gnd)〔wo.thy, +FC_shift/gnd_shift/wdt_shift/FC_norm〕
      - ✅ **shift＝順序自己同型 `shift_olt`** ＋ `shift_wfo`/`acc_shift`/`acc_shift_pR`〔wo/buchholz, ground 正規化の基盤〕
      - ✅ distinguished-set 定義 Mn/AccB/Acc（ground 階層）＋単調性＋generic `Awf`/`wf_on_Awf`〔buchholz〕
      - ✅ **致命バグ修正2 (nneg)**: 旧 target `oltRwF`(omfree のみ) も **ill-founded**（`Th(-k)0` 無限降下, omfree内）＝`wf_oltRwF`/`masterF` は偽だった。**非負添字 `nneg`(全添字≥0) を追加**し target を健全化〔`wo.nneg`/`nneg_Kn`/`nneg_embed`, oltRwF/pRF/bag_mono_wF/masterF/L_ThF に thread〕
      - ✅ `cntbl`(FCset=∅)＋`cntbl_downclosed`（可算フラグメントは <o-downward-closed; 但し cntbl 自体も ill-founded＝target ではない, 補題は再利用可）〔wo.thy〕
      - ✅ **`masterF`（nneg 付きで証明済）**: 全 omfree∧wfo∧nneg 項が `oltRwF`-acc。構造帰納（Om消滅／Su は bag／Th は L_ThF）
      - 🚨 **`L_ThF`（再構成済: 外側レベル k 強帰納＋内側 acc 帰納。残核は `e∈acc` 1点）**: `omfree d⟹wfo d⟹nneg d⟹0≤n⟹d∈acc⟹Th n d∈acc`。dom_acc/p=n(accIH)/Su(bag) 全済、p<n は levelIH で `e∈acc` に帰着。**残核 `eacc:e∈acc`**＝Pohlers 9.6.15 controlled⟹acc（要 Mn/AccB 完全構成: 構造帰納 on e は level≥n の Th collapse で破綻）。olt_trans 不使用維持 ★
      - ✅ `wf_oltRwF`（masterF から）〔buchholz〕
    - 🚨 **埋め込み `three → ot` の順序保存**〔embed.thy〕
      - ✅ embed/eprincs/collapse＋像の well-formed〔wfo_embed〕＋**Om-free〔omfree_embed〕**（int 化済: `Th (int a) ...`）
      - ✅ **`wf_Rnf_via_embed`**: `wf Rnf` ⟸ `op`（NF 上 `w≺x ⟹ embed w<\<^sub>o embed x`）のみ（wf_oltRwF＋omfree_embed で配線済、偽の wf oltRw 仮定は除去）
      - ✅ **`step_terminates_via_embed`**: PSS 停止性 ⟸ `op`
      - ✅ **`step_terminates_NF`（無条件の停止性定理）** ＝ `step_terminates_via_embed[OF op_NF]`
      - 🚨 **`op_NF`**: Z✅＋`embed_P_neq_Zero`✅、**P/P 残 sorry**。分解検証済(Python 0 反例)・補題整備中:
        - ✅ **K 条件 a<e**: `wo.Kn_dom`（omfree c⟹γ∈Kn a c⟹a<e⟹γ<o Th e D）＋`wo.Th_lt_of_sub_lt`（omfree g⟹m<n⟹Th m g<o Th n h）＝leading-subscript clause 完成
        - ✅ **op_NF glue 基盤 全完成**: `wo.Kn_dom`/`Th_lt_of_sub_lt`(K条件 a<e)・`embed.bag_embed`/`bag_collapse`/`bag_embed_P`(principal bag)・`embed.collapse_lt_dom`/`collapse_neq_Zero`(DM single-dominator)・`embed.eprincs_form`/`eprincs_lt_Th`(tail 支配)・`wf.tops`/`cnf_tops_le`(cnf 添字上限)・`mechanized.translate_takeWhile_snoc_le`・`wf.cnf_snoc`/`cnf_butlast`・`embed.uncollapse`/`collapse_inj`/`embed_inj`(単射)・`embed.collapse_prepend_diff`(equal-leading DM, tail 用)
        - ✅ **`embed.op_lt_a`（op_NF の a<e ケース完全証明, cnf w のみ要）**
        - ✅ **cnf 機械 全証明**: `translate_block_append`/`translate_shift`(mechanized), `cnf_take`/`cnf_butlast`/`cnf_snoc`/`cnf_tops_le`/`cnf_replicate_block`/`cnf_ctx_cong`(**一般化: 先頭principal非増加 P a1 b1 Z ≤o P a2 b2 Z**)/`cnf_tail`/`cnf_oper_i1eq0`(i1=0)/**`cnf_oper_i1eq1`(i1=1 昇順コピー, 自己相似 copies_Suc_front＋shift不変＋w0<snd lp spine支配, core_i1 で decr 内部導出)**(wf)
        - ✅ **`cnf_ST_PS` 完全証明 (wf.thy sorry=0)**: `shiftr0`/`copies` 定義群＋`oper_bad_blocks`(mechanized: bad分岐分解 obtains)＋`cnf_oper`(全oper分岐)＋ST_PS帰納。罠: obtain discharge は `by (rule ...)`（blast はループ）, translate 非展開に `simp only: leq`
        - 🚨 **その他残**: `bfb_ST_PS`＋op_NF **a=e principal**, op_cnf 組立（tail は collapse_prepend_diff, embed_inj で irrefl 回避済）, L_ThF leveled-Acc
  - ✅ 停止性（wfimg ⟹ 停止、減少は discharge 済み）〔step_terminates / no_infinite_expansion / step_terminates_from_diag / step_terminates_via_embed〕
    - ✅ 条件付還元〔step_terminates_cond / no_infinite_expansion_cond〕
    - ✅ step が ST_PS 内に閉じる〔step_in_ST_PS〕
