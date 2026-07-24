# 進捗管理

## 注意事項
- 進捗ツリー以外をこのページに書かない。
- **各アイテムはアイテムを区別する情報のみを１行で。それ以上は書かない**。**人間用なので絶対に短く。**
  - ❌ `✅ wfE（レベル内整礎）→ 和の層を剥離〔wfsum.thy: NF=非増加和 p0(b_i)、olt=lex→multiset 拡張、olt_sum_decomp/olt_sum_mult/wf_level_from_args/wfE_from_args〕`
  - ⭕️ `✅ wfE（レベル内整礎）`
  - 補題名リスト・設計詳細は書かない。エージェントが参照元を要するなら **ソースコードのコメント**に「この補題＝task.md の○○アイテム」と書く。設計詳細は PROOF-STATUS.md / memo.md / memory へ。
- 凡例: **各項目には必ず 🚨（未証明）または ✅（証明済）を付ける**。 / 🚨🤖＝ agent 作業中

## 進捗ツリー
> 詳細・経緯は PROOF-STATUS.md §(a0)（authoritative）/ memo.md / memory へ。
- ✅ **定理: 標準形ペア数列システムの停止性（証明完了・sorryAx-free）**
  - ✅ §5 定式化
  - ✅ 三分木記法 p_a(b)+c
  - ✅ 添字優先順序 olt（線形）
  - ✅ 変換 translate
  - ✅ 減少補題 translate(M[n]) ≺ translate M
  - ✅ step が ST_PS 内に閉じる
  - ✅ 停止性還元（整礎性 ⟹ 停止）
  - ✅ 整礎性（＝核）
    - ✅ 3還元ルート（nrm-order / pure-lex / W=T）— 全て sorryAx-free modulo 核
    - ✅ Buchholz §2 embedding 半分（oV / wf_olt_wf3 / Gterm / proj）
    - ✅ Buchholz §1 substrate（crank / Gset / Lemma 1.9 generator / fixpoint base / 4-leaf joint skeleton）
    - ✅ door1 Towsner ladder（cr_inv / M_n / Acc_n / Lemma 3.8 / ϑ-closure collapse 方向 forest-fact-free）
    - ❌ 旧ルートの壁（H0clause forest core）＝ W_u ルートで迂回済み、もはや不要
      - 同核: H0clause_oper_step / CollapseResidueMaxo / wf_ArgsA / diag_acc / Towsner 3.11 cross-stratum / Buchholz 1.9-term
      - 3 door + 全 lever（rank / critSub / WQO / gap-embed / §1 / fixpoint）収束、shortcut なし確定
      - ❌ Buchholz distinguished-set 再 foundation（external-param C^α(X)、Arai §3.1）= 3 gate de-risk で REFUTED（bypass #13、§22）: olt は syntactic、WF certificate は wf_olt_wf3(oV/wf3) のみ ⟹ 壁を wf3_of_cnf=H0clause に relocate するだけ。door1 が faithful な term-level 法、壁は intrinsic。core triply-confirmed
    - ★★ 順序数なし W_u ルート（pss-proof の構文的 OT_B 整礎性を PSS ネイティブ移植）＝ H0clause 壁を迂回、残り1命題
      - ✅ end-to-end 配線（OrdinalFree.lean）: PSS_terminates_ordinal_free / no_infinite_expansion / stepR 版、全て sorryAx-free
      - ✅ 第2の柱 W-membership 完全証明（Wset.lean 全体 sorryAx-free、塔恒等式 oper_cons_tower 含む）
      - ✅ 共終性の全分岐（seqlex 還元 / degenerate / bad 分解 / d0=0 crux）
      - ✅ AscArgDom を単一の host-free 核 ArgDomCore へ還元（AscArg.lean、sorryAx-free）
      - ✅ ArgDomCore は局所不変量（blockok/z0ok/r1ok/cnf）からは導けない＝ST_PS 導出帰納が必須（反例を Lean で証明）
      - ✅ ArgDomCore の ST_PS 導出帰納を配線（diag / 短 / (0,0)-last / noparent の各分岐は証明済）
      - ✅ bad 分岐の場合分け確定（境界は |G|+|blk|）＋ A1 用の転送補題（prefix 非依存 / shiftr0 同変）を証明
      - ✅ argDomCoreOn_bad（A1 / B / A2 交差ケース）＝ ArgDomCore 証明完了
      - ✅ **最終定理 PSS_terminates_unconditional / no_infinite_expansion_holds（Final.lean、無条件・順序数なし）**
