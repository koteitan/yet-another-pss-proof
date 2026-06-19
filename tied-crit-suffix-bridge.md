# tied_crit_lt_hb の suffix-NT bridge 証明スケッチ（続94, route b）

残る本丸 `tied_crit_lt_hb`（nrm.thy:2888）を木側 suffix 構造で攻める計画。
記号: 標準形 `M=(0,0)#r`、arg-zone `W=takeWhile (0<fst) r`、`X=nrm(translate W)`、`hb=harg X`。
`NT S := nrm(translate S)`。発火 = `proj 0 X ≠ X`。

## 目標
`tied_crit_lt_hb`: 発火時、`g∈Gterm 0 hb ∧ lead g = lead hb ⟹ olt g hb`。
（非 tied `lead g<lead hb` は `nontied_lt_head` で緑。`lead g>lead hb` は F2+G1 で除外。）

## deep-verified 構造事実（266k 発火・危険域超え, 0 例外）
- **(X1)** `lead X = 1`、`X = P 1 hb hc`。 〔probe_sp_i2_deep 0/779999〕
- **(F2)** `lead hb = maxsub X`、ゆえに `maxsub hb = lead hb`（F2+G1+lead_le_maxsub から導出可）。
- **(S-hb)** `hb = NT(W[i0:])` なる suffix start `i0` が存在。 〔probe_suffix_chain 8354/8354〕
- **(S-crit)** tied G_0-critical `g = NT(W[i:])` なる `i (>i0)` が存在。 〔probe_infix_deep H_suffix 0/513459〕

## bridge を閉じる順序補題（要・深層検証中 = probe_tied_suffix_order, Lemma L）
- **(L)** 標準ホスト内 `i0<i` で `lead(NT W[i0:]) = lead(NT W[i:]) = k ⟹ olt (NT W[i:]) (NT W[i0:])`。
  「tied-lead の later-suffix は earlier-suffix より `<o`」。

## 導出（L が真なら）
`g`（tied G_0-crit, lead g=lead hb=k）について、(S-crit) で `g=NT(W[i:])`、(S-hb) で `hb=NT(W[i0:])`、`i>i0`、
lead 一致（共に k）。(L) より `olt g hb`。∎ ⟹ `tied_crit_lt_hb` 緑、残核は `argz_head_spine` のみに。

## なぜ wf3 では届かないか（class-essential の根）
tied critical `g`（lead k）は `D_0` 等の低添字主項の下に埋もれ得て `Gterm k hb` に入らない
（例 `hb=D_k(D_0(g))`: `g∈Gterm 0 hb` だが `Gterm k hb={D_0(g)}` で `g∉`）。
ゆえ wf3=`Gterm k hb<hb`（OT3）では `g<hb` を出せない。標準形の suffix 構造（=oper コピー）が本質。

## L の形式化方針（未着手）
- 既存 `NT_prefix_lt`（緑 nrmstep.thy:9986）は **prefix**版（`olt(NT C)(NT(C@D))`）。L は **suffix**版で別物。
- `nrm_snoc` 系は右拡張(snoc)。L は左 drop(cons 除去)で新規 infra が要る。
- 候補: `W[i0:]=W[i0:i]@W[i:]` 分解 + tied-lead 条件下で先頭ブロック比較。oper 構造との接続（自己相似コピー）。
- 注意: L が「原問題と同等の難しさ」に陥っていないか要検討（suffix-NT 順序という別命題なので帰納の取り方次第）。

## ツール
tools/{probe_suffix_chain, probe_infix_deep, probe_tied_suffix_order, probe_sp_i2_deep}.py。
base = enum_ST + fast_pss.oper + valnorm(nrm/lt_term) + wfe_explore(translate)。
