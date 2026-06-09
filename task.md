# 進捗管理

## 注意事項
- 進捗ツリー以外をこのページに書かない。
- **各アイテムはアイテムを区別する情報のみを１行で。それ以上は書かない**（討伐補題名 or blocker を短く。設計の詳細は proof-ja.md・memory へ）。
- 凡例: **各項目には必ず 🚨（未証明）または ✅（証明済）を付ける**。 / 🚨🤖＝ agent 作業中
- 戦略(b)凡例（多相系 polymorphic `ot` へ切替した場合）: 🏺＝移植/作り直しが必要なアイテム / ✨＝その移植により閉じられる（=証明可能になる）アイテム。
  - 背景: Towsner §2（絶対系）には WF 証明が無く、§3.2 の WF は polymorphic 系専用。絶対系では `Om n` が「足場ではなく本物の大元」のため構造帰納の底が無く、Acc_n/M_n レベル構築（数百行）が要る。多相系なら §3.2 がほぼ直接移植でき `wf pR` が閉じる。

## 進捗ツリー
> **現状サマリ (2026-06-09, 方針A確定＝完全自前証明)**: PSS 停止性 `embed.step_terminates_NF`、
> 内部 sorry **3つ**（他全証明済・緑, baseline RC=0）。**方針(ユーザー確定)= (A) 全て自前で完全証明**
> （本系はオリジナル $p_a(b)$ 記法＝非標準で文献引用は不成立。sorry ゼロを目指す）。
> **3 sorry はいずれも研究級の順序論/証明論コア（当初想定より大）**:
> **(1) `wo.olt_trans[c=Su[a=Su]]`**（非標準=多重集合単一支配元の推移律。**🚨bridge ルート死亡: mnlcong は wfo でも偽**(続28)。
>   trans は真だが multp 経由不可→直接証明の再設計要。順序は非線形=置換で非比較ペア有り）、
> **(2) `buchholz.L_ThF[e∈acc]`**（Towsner 崩壊整礎性=超限 distinguished-set 構成。predecessor 非有界→Π¹₁, 初等帰納不可）、
> **(3) `embed.op_NF[P/P]`**（embed の NF 順序保存=翻訳忠実性, **完全オリジナル**。(1)依存＋NF K条件）。
> **依存**: step_terminates_NF ← wf_Rnf_via_embed ← {wf_oltRwF←masterF←L_ThF, op_NF←olt_trans}。
> **基盤（全証明済・緑）**: shift 自己同型・acc 不変・ground/norm・**nneg fragment(健全化済)**・reduction chain・
>   cnf_ST_PS・decrease・size 境界群(scratch_trans.thy 緑)・trans 8ケース(wfo付き別 scratch 緑)。
> **経験事実(python)**: mnlcong wfo でも偽(続28 訂正)・olt_trans 無条件に真・順序は非線形(置換非比較)。
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
      - 🚨 **順序メタ理論（完全自前。本系は非標準=オリジナル $p_a(b)$ なので文献引用は不成立, ユーザー確定 2026-06-09=方針A）**:
        `olt_Om_mono`✅, `olt_asym`/`olt_irrefl`✅(無条件,但し olt_trans 依存)。
        **`olt_trans` 残 sorry = c=Su[a=Su]（Su/Su 単一支配元推移）1つ**（他8ケースは size 帰納で証明済, wfo付き別 scratch で緑検証済）。
        **🚨重大訂正(続28)**: **mnlcong は wfo でも偽**(深さ3 python, 131万 CE; 例 u=Th0(Su[Ω0,Ω1]),v=Th0(Th0(Su[Ω0,Ω1])),m=Th0(Su[Ω1,Ω0]))。
        ∴ **multp_HO bridge ルート(mnlcong 必須)は wfo でも無効＝死亡**。順序は「置換合同を法に線形」ですらない(下方集合が置換で不変でない)。
        続23-27 の wfo 制限 bridge 方針は誤り。trans 自体は無条件に真(python CE=0)だが multp 経由は不可。
        **要・直接証明の再設計**: 単一支配元 witness 構成に comparability が要るが順序が非線形で標準手法不可。研究級。
        資産: scratch_trans.thy(緑) に size 境界群(carrier_sum_lt 等, 直接証明でも流用可)・bridge 配線(本筋外)。★3義務の一つ・最難の一つ
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
      - 🚨 **`L_ThF`（再構成済: 外側レベル k 強帰納＋内側 acc 帰納。残核は `e∈acc` 1点）**: `omfree d⟹wfo d⟹nneg d⟹0≤n⟹d∈acc⟹Th n d∈acc`。dom_acc/p=n(accIH)/Su(bag) 全済、p<n は levelIH で `e∈acc` に帰着。
        **🚨残核 `eacc:e∈acc` は研究級(続21-22 確定)**: predecessor `Th p e`(p<n) の e はサイズ・レベル**非有界**(例 `Th 0(Th 5 Z)<o Th 1 d`)＝構造/size/level のいかなる初等帰納でも有界化不可。masterF↔L_ThF↔Coll が相互 entangle。Towsner も「Acc_n 全体は Π¹₁-CA₀ 不可」と明記。
        ∴ **Towsner Acc_n=既存 Mn/AccB の超限ラダー(3.8-3.12)＋接続**が必須。我々順序 ≠ Towsner順序(明示 subscript 比較 vs 引数内Ω)で逐語転写不可＝戦略のみ流用の独自実行。olt_trans 不使用維持 ★最難
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
