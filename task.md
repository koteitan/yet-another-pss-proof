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
- 🔬 **W=T 直接路線（続85〜88・本線）〔wtt.thy/ord/wttbase.thy・緑〕**: nrm/順序/translate
    を使わず PSS 停止性を **diag_acc**（diag種 accessibility）1点に帰着。
    - ✅ reduction（direct_acc_of_ST_PS / PSS_terminates_direct / acc_short）+ step_level_noninc 証明済。
    - ✅ **maxr1=0 base 完全証明**〔wf3_of_cnf_subs0（純項 cnf∧subs⊆{0}⟹wf3）/ wf3_translate_subs0 /
      subs0_step_closed/decreases / **acc_subs0**（maxr1=0標準形は全accessible）・sorry無・crux-free〕。
    - 🚨 残: maxr1=1 base（r1ok要）→ level帰納 → **maxr1≥2＝crux本体**（再上昇正準化）。
    旧 nrm_order_pres（第7事件で偽核）放棄。
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
