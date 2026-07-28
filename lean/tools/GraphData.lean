/-
# 参照グラフの抽出

`lean/*.lean` の宣言をノード、**カーネルの証明項が使う定数**を辺として書き出す。
`DeadCode.lean` と同じ歩き方なので、記法・`@[simp]` による暗黙の使用・`omega` や
`decide` が生成した補題・インスタンス解決も、すべて辺として数える。

    cd lean && lake env lean tools/GraphData.lean > tools/graph-deps.json

出力は 1 行の JSON。

    {"nodes":[{"name":..,"module":..,"line":..,"kind":"thm"|"def"},..],
     "edges":[["a","b"],..]}

`kind` は定理（`.thmInfo`）と定義（それ以外）の別である。
-/
import Final

open Lean Elab Command

namespace GraphData

/-- 名前の 1 成分を、エスケープ（`«…»`）を付けない生の文字列で返す。 -/
def rawStr : Name → String
  | .str _ s => s
  | .num _ i => toString i
  | .anonymous => ""

/-- コンパイラが自動生成した宣言か。ノードにも辺にも出さない。 -/
def isGenerated (n : Name) : Bool :=
  n.components.any fun c =>
    let s := rawStr c
    s.startsWith "_" || s.startsWith "term_" || s.startsWith "inst"
      || s == "rec" || s == "recOn" || s == "brecOn" || s == "below"
      || s == "casesOn" || s == "noConfusion" || s == "noConfusionType"
      || s == "ndrec" || s == "ndrecOn" || s == "induct" || s == "ibelow"
      || s == "binductionOn" || s == "injEq" || s == "inj" || s == "sizeOf_spec"
      || s == "elim" || s == "ctorElim" || s == "ctorElimType"
      || s == "ctorIdx" || s.startsWith "match_" || s.startsWith "proof_"
      || s == "eq_def" || s == "sunfold"
      -- `eq_1`, `eq_2`, … は方程式補題。`eq_Z_of_olt_one` のような本物の定理を
      -- 巻き込まないよう、`eq_` の後ろが数字のときだけ除外する。
      || (s.startsWith "eq_" && (s.drop 3).all Char.isDigit && s.length > 3)

/-- JSON の文字列としてエスケープする。 -/
def esc (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ (if c == '"' then "\\\"" else if c == '\\' then "\\\\" else toString c)) ""

end GraphData

elab "#graphdata" : command => do
  let env ← getEnv
  let ours : List Name :=
    [`Pss, `Term, `Decrease, `Reduction, `Cnf, `Seqlex, `Column,
     `Cofinality, `ArgDom, `Wset, `Final]
  let mods := env.header.moduleNames
  -- 本リポジトリの宣言だけを集める
  let mut own : Std.HashMap Name Name := {}          -- 宣言 -> モジュール
  for (n, ci) in env.constants.toList do
    if GraphData.isGenerated n then continue
    if ci matches .ctorInfo _ | .recInfo _ then continue
    let some idx := env.getModuleIdxFor? n | continue
    let m := mods[idx.toNat]!
    unless ours.contains m do continue
    own := own.insert n m
  let mut nodes : Array String := #[]
  let mut edges : Array String := #[]
  for (n, m) in own.toList do
    let some ci := env.find? n | continue
    let line ← match ← findDeclarationRanges? n with
      | some r => pure r.range.pos.line
      | none   => pure 0
    let kind := if ci matches .thmInfo _ then "thm" else "def"
    nodes := nodes.push
      s!"\{\"name\":\"{GraphData.esc n.toString}\",\"module\":\"{m}\",\"line\":{line},\"kind\":\"{kind}\"}"
    -- 型と（定理を含む）値が使う定数のうち、本リポジトリのものだけを辺にする
    let cs := ci.type.getUsedConstants
      ++ (match ci.value? (allowOpaque := true) with
          | some v => v.getUsedConstants
          | none   => #[])
    let mut seen : Std.HashSet Name := {}
    for c in cs do
      if c == n then continue
      if seen.contains c then continue
      seen := seen.insert c
      if own.contains c then
        edges := edges.push
          s!"[\"{GraphData.esc n.toString}\",\"{GraphData.esc c.toString}\"]"
  IO.println s!"\{\"nodes\":[{String.intercalate "," nodes.toList}],\"edges\":[{String.intercalate "," edges.toList}]}"

#graphdata
