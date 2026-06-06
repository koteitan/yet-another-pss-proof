# 進捗管理

## 注意事項
- 進捗ツリー以外をこのページに書かない。
- **各アイテムはアイテムを区別する情報のみを１行で。それ以上は書かない**（討伐補題名 or blocker を短く。設計の詳細は proof-ja.md・memory へ）。
- 凡例: **各項目には必ず 🚨（未証明）または ✅（証明済）を付ける**。 / 🚨🤖＝ agent 作業中

## 進捗ツリー
- 🚨 定理（標準形ペア数列システムの停止性）〔proofs.thy〕
  - ✅ §5 定式化〔def.thy: 親子関係 nextrel0/1・基本列 oper=M[n]・標準形 ST_PS・step〕
  - ✅ オーダー記法 $p_a(b)+c$〔mechanized.thy〕
    - ✅ datatype ord = Z | P nat ord ord
    - ✅ 添字優先順序と線形性〔olt / olt_irrefl・olt_trans・olt_total〕
  - ✅ 変換 translate（森オーダー写像、添字=行1）
    - ✅ 定義＋task 例の sanity〔translate〕
    - ✅ 添字の出所（添字は元の行1値のみ）〔subs / subs_translate〕
  - 🚨 減少補題（translate(M[n]) ≺ translate M）
    - ✅ 末尾追加で増大〔translate_snoc_increase〕
    - ✅ 末尾削除で減少〔translate_butlast_decrease〕
    - ✅ Pred 2 ケース（末尾(0,0)／親なし）〔translate_oper_pred〕
    - ✅ 先頭添字支配（lead が小さければ ≺）〔lead / olt_P_of_lead_lt〕
    - 🚨 bad ケース
      - ✅ 文脈合同 BADCTX（G 帰納）〔translate_ctx_cong〕
      - 🚨 単一木性（B@[last]・コピーが根 M_{j0} の単一木）
      - 🚨 コア（copies ≺ B@[last]、スパイン下降→lead 支配）
      - 🚨 oper の bad 分岐との接続（parent/δ0）
  - 🚨 整礎性（NF = translate(ST_PS) 上で ≺ 整礎）
    - ✅ 添字単調性（M[n] の行1値 ⊆ M の行1値、δ₁=0）〔oper_snd_subset / subs_translate_oper〕
    - 🚨 最大添字 n の階層化帰納（n=0 で PrSS CNF 帰着）
  - ✅ 停止性への還元（条件付：減少＋整礎 ⟹ 停止）〔step_terminates_cond / no_infinite_expansion_cond〕
