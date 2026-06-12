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
- 🚨🤖 nrm_step_dec 直接証明〔nrmstep.thy〕
  - ✅ olt層・構造層〔nrm_snoc_seg/ins_olt_mono/einc/eflip/gap/fire_transport/stepsok〕
  - ✅ STS_A 完全証明 / proj_once / proj_submono
  - ✅ E6 アーキテクチャ〔msfx 接尾辞定理・実証 V1-V5 全0違反・memo続22〕＋ post一般化〔0/8243〕
  - ✅ C1層〔fbseg_hd_level→NT_dom→NT_shape→NT_hd/NT_tail_lt・memo続24〕
  - ✅ コンビネータ群〔E6_value/GCAT/E6_hdom/E6_dom_tie/E6_mem_resolved/E6_nbcK/Gterm_NT_high〕
  - ✅ r1ok 基盤〔row1規律 0/14558・残 r1ok_climb のみ・memo続26〕
  - ✅ sibm2/sibrel 修復〔旧 sibm/SIB_shape は偽＝閉包境界教訓・SIB_shape2・NT_tie_resolved 3ケース・memo続29〕
  - ✅ sibrel4 修復〔閉包+3で旧sibrel偽（4例目すり抜け）→第4分岐(末尾snd降下)追加 0/729131・全消費側再構成・NT_enddrop凍結・続67〜70〕
  - ✅ 正確文面の閉包+1監査〔E6_lpl 等 全0違反・STS_B 前提修正・E6_memT 前提空・audit_*.py〕
  - ✅ sibm2_oper_bad 討伐〔n帰納×シーム分解・CFGA_r1=NT_dom_sub_eq窓・sibrel衝突代数 nopref/ascent/diverge〕
  - ✅ E6_tie_nofire0/1 討伐〔Gterm_empty_lowhead＝スパイン低頭でカタログ空・memo続29補15〕
  - ✅ seam_copyhead_m1 討伐〔一般L直証: coreM 4分岐×E-const/F1直証・F2-L1=blockok反駁・実在114件全カバー〕
  - 🚨 シーム残差〔seam_open_m1 14件 e1j0=0機構 / copyhead残差 P・E2var・F2L2 閉包+1で0件 / copyhead_deep 実証0件〕
  - ✅ t1ok/t3ok 基盤＋E6_tie_nofire_high0 討伐〔タイラン≤u+1/=u 不変量・y∈{u,u+1}強制→hm矛盾・残 t1ok/t3ok_oper_bad〕
  - ✅ E6_tie_nofire_high1 討伐〔t14ok=タイ停止ランhm不変量＋hm_take接頭辞遺伝〕＝タイ無発火コンプレックス完全制覇
  - 🚨 値側コア〔NT_lexdiff_lt 0/116万〕
  - ✅ ginv 基盤＋E6_nbcK_T 討伐〔ginv=閉鎖窓row1上界・生成帰納骨格緑・dseg橋渡し・残 ginv_oper_bad のみ〕
  - 🚨 fire-cascade 残2点〔E6_memT/E6_nbcK_K（lpl/dom_deep は G6 で討伐済）〕
  - ✅ ginv_oper_bad 討伐〔A/B/C/E転送＋反駁＋d01/d02閉鎖証人・残差 GBLK0/qpos の2点〕
  - ✅ t1ok_oper_bad 討伐〔3ケース転送＋BT1・unfolding再帰/metis/arith原子の3事故克服〕
  - ✅ t3ok_oper_bad 討伐〔t1okクローン+T3デルタ+BT1_T3凍結〕
  - ✅ t14ok 健全性修正〔閉包+2で旧形偽→hi前提付きへ弱化・high1無傷・(hi,¬hm)=0/54440〕
  - ✅ BT-WIN/BT-WRAP 統一不変量〔タイ不要窓停止形＋d0:0頭タイ形・閉包+2全0違反・BT1系は系に〕
  - ✅ 凍結階層確立〔BTFULL（全域形63999/0）→BTWIN系化 / BTWRAPG（τ量化49609/0）→BTWRAP系化〕
  - ✅ btfullok±T3 ユニバーサル化〔全ホスト不変量・標準テンプレート緑・ginv_BTFULL系は導出〕
  - ✅ btfullok(3)_oper_bad 討伐〔ユニバーサル窓シーム5ケース＋T3クローン・BT階層がBTWRAPU±U3の2点に立脚〕
  - ✅ BTWRAPU±U3 討伐〔LAND+鎖帰納+CT / +NT3空クラス〕＝**BT窓族完全終結**
  - ✅ GBLK0 討伐〔GAP 246件級へ分解〕
  - ✅ OSC再構成〔CT/GAP→導出・O1はBTWRAPU qa=0系で討伐・残凍結 O2(158/0)+GCD(7/0)・i1>0真空性証明済〕
  - 🚨 GRANDシーム残〔O2(158)/GCD(7)/NT3(空)/BTWRAP_T3_pos(6・主部20699はBTWRAPU3導出済)/qpos(171)/t14ok_oper_bad(地図済)〕
  - ✅ E6_iii_singleton 討伐〔FBS=fire-butlast安定 5370/0 の対偶2行〕
  - ✅ E6_qcut_last 討伐〔QDIAG=厳密対角凍結（拡張fire単独 32491/0）＋単調帰納・dropWhile リスト論証〕
  - ✅ E6_seam 分割〔q脱結合凍結核 seam_MIN(458980/0)＋seam_INV(426489/0)・本体は2行導出〕
  - ✅ G6統一支配核〔E6_G6 凍結 711342/0・E6_dom_tie/E6_lpl 討伐・E6_dom_deep/dom_tie_resolved 削除〕
  - 🚨 行レベル凍結核〔E6_G6/seam_MIN/seam_INV/E6_FBS/E6_QDIAG 本体〕＋ STS_B 本体〔0/26322〕
  - ✅ r1ok_climb 討伐〔q=0強制＋r'=parent0(j1)＋nextrel1最小性で残差なし完全証明〕
  - ✅ TOP_desc ステート〔prefix弱化形・閉包+2 967/0 凍結・本体は未証明〕
  - 🚨 スタブ〔NT_tie/E6_mem＝resolved版あり・最終組立＝1本の同時長さ帰納にインライン（SCC地図=memo続59）〕
- 🗑 旧 (β1)Trans級翻訳 / (β2)P進再現 は不要。wf_ArgsA 路線は凍結〔wfsum に残置〕
