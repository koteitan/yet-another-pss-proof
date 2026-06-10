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
      - 🚨🤖 本丸=(α) 新本線: **値正規化 nrm = NF→OT 順序埋め込み**〔ord/nrm.thy 緑〕
        - ✅ nrm 定義＋ proj_id/proj_rec/proj_wf3/proj_G/**wf3_nrm**（像⊆OT）全証明済（PSI 3s 緑）
        - ✅ 実証: 2,643,843 ペア（NF+遺伝ブロック、クロスレベル込）で衝突0・逆転0〔tools/valnorm.py〕
        - ✅ **PSS_terminates_nrm** = inv_image wf_olt_wf3 (nrm∘translate)（peel/レベル分解不要）
        - ✅ wf_Rnf_nrm（order_pres⟹wf Rnf）・nrm_step_dec（order_pres から導出）
        - 🚨 live sorry = nrm_order_pres ただ1つ。攻め筋2段: (弱) nrm_step_dec 直接証明
          〔E6: proj=首最大row1接尾辞切出し、E7: 第一差分は prefix/sub の2種のみ、oper 機構流用〕
          / (強) 全ペア保存＝proj-mono（弱単調＋CRUX 単射、A_a 全集合で実証済・衝突0）
        - 🚨🤖 攻略 nrmstep.thy（Pred ケース）: ✅ olt層（nrm_snoc_seg/ins_olt_mono）
          ✅ 構造層（einc/eflip・gap補題・fire_transport・nrm_snoc_str・projE骨格・
          ST_snocokS_gen+INV螺旋・maxo_ub・stepsok）✅ **STS_A 完全証明**（cnf隣接+pre帰納）
          ✅ **proj_once**（射影=1ステップ; max臨界は自ら無発火）+ **proj_submono**＋Gterm_trans/maxg_nofire
          ✅ **E6アーキテクチャ移行**（projE系削除→msfx接尾辞定理に再編; maxr1/msfx/NT_single/proj_fire_ne 純粋部品緑;
          ST_snocokS_gen にインライン配線・長さ帰納で循環なし; 実証 V1-V5 全0違反 = memo続22）
          ✅ post一般化（segprov/STS_A/ST_snocokS_gen/ST_snocok_int/nrm_snoc_int、内部位置対応・実証8243で0違反）
          ✅ fbseg（森境界ピース）＋閉包補題3本 / NT_noabsorb / **NT_tail_lt**（nrm和尾部厳密増大）
          ✅ C1層完成: fbseg_hd_level（blockokレベル固定・drop=0）→NT_dom→NT_shape→NT_hd/NT_tail_lt（memo続24）
          ✅ **E6_value 本体**（E6_mem/E6_dom_tie 分解のコンビネータ・proj_once+maxo_ub）
          ✅ **GCAT**（Gカタログ・u一様・E6_value非依存）+ subs連鎖 + NT_msfx_hdsub + 低添字dominance
          ✅ nrm_snoc_mid/NT_prefix_lt（mid-host）/ msfx_tail / **E6_dom_tie_resolved**（l=j0閉鎖）/
          **E6_hdom**（排除コア、GCATパターン）— 層化循環は最終組立で同時帰納に（memo続25）
          ✅ 健全性修正: E6_lpl/E6_dom_deep に可視性前提（旧文面は偽・実証2163逆転をキャッチ）
          ✅ E6_mem_resolved（hdom排除+K側カスケード+T側移送）/ E6_nbcK 再構成（可視性連言=Gterm_NT_high で証明）
          ✅ **r1ok 基盤**（row1規律 snd≤親snd+1・実証0/14558）: 生成帰納+diag+take/butlast+
          oper骨格+oper_bad主証明+copy_witness 全緑 — **残 r1ok_climb 1点**（memo続26）
          ✅ 【続29】旧 sibm/SIB_shape は偽（閉包境界アーティファクト）→ **sibm2/sibrel 修復完了・緑**:
          sibrel 4族（E/P/F1/F2・lexdiff時hm²）・SIB_shape2・NT_tie_resolved 3ケース・STS_B 前提修正
          ✅ 正確文面の閉包+1監査: E6_lpl/dom_deep/nbcK_T/K/r1ok_climb/seam/qcut/iii 全0違反、
          E6_memT は前提空（討伐可）。マイナーは必ず閉包+1で回す（audit_plus1/exact.py）
          ✅ **sibm2_oper_bad 討伐**: シーム分解全層（I-closed/II-int/II-cross/I-open O1/
          blift=b<j0全分岐/copyhead=b=j0全分岐）＋CFGA_r1（NT_dom_sub_eq窓で証明）＋
          sibrel衝突代数（nopref/ascent/diverge）— 残 = 極小核3点
          {seam_open_m1(14件・e1j0=0機構) / seam_copyhead_m1(20件・全てcoreM-eq・L=1) /
          seam_copyhead_deep(実証0件)}
          🚨 実効コア: 🥇シーム極小核3点 / NT_lexdiff_lt（116万対0failの新値補題）/
          E6_tie_nofire0/1（¬hmタイラン無発火）/
          fire-cascade系5点（E6_lpl / E6_dom_deep / E6_memT / E6_nbcK_T / E6_nbcK_K = GRAND同時帰納の本丸）/
          r1ok_climb（e1正側0/729・機構=memo続26補5）/ TOP_desc（トップ木nrm弱降下0/474・未ステート）
          🚨 行レベル: E6_qcut_last / E6_iii_singleton / E6_seam ＋ STS_B（fbsegDリフト＋TOP_desc経路、memo続27-28）
          🚨 スタブ: NT_tie / E6_mem / E6_dom_tie（resolved版あり・最終組立=長さ同時帰納にインライン）
        - 旧 (β1)Trans級翻訳 / (β2)P進再現 は不要に。wf_ArgsA 路線は凍結（wfsum に残置）
    - 🗑 旧 K-dom ルート（wo/buchholz/embed：absolute, 残 sorry あり・不使用）。oV の「NF 直接埋め込み」は collapse で破棄（wf3 上の埋め込みとして柱2に再生）。
  - ✅ 停止性（wfimg ⟹ 停止、減少は discharge 済み）〔step_terminates / no_infinite_expansion / step_terminates_from_diag / step_terminates_via_embed〕
    - ✅ 条件付還元〔step_terminates_cond / no_infinite_expansion_cond〕
    - ✅ step が ST_PS 内に閉じる〔step_in_ST_PS〕
