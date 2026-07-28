/-
# 未使用宣言の検出

`Final.lean` の 5 定理を根として、**カーネルの証明項を辿って**到達可能な定数の
集合を求め、`YAPSS/*.lean` に書かれた宣言のうちそこに入らないものを列挙する。

証明項そのものを辿るので、記法（`<o` = `olt`）・`@[simp]` による暗黙の使用・`omega` や
`decide` が生成した補題・インスタンス解決も、すべて正しく「使用」として数える。
テキスト検索による近似ではない。

    cd lean && lake env lean tools/DeadCode.lean

注意: 定理の証明項は `ConstantInfo.value? (allowOpaque := true)` でないと取れない
（`allowOpaque := false` は `.thmInfo` に対して `none` を返す）。
-/
import Final

open Lean Elab Command

namespace DeadCode

/-- `n` から到達可能な定数を `seen` に足す。型と（定理を含む）値の両方を辿る。 -/
partial def visit (env : Environment) (n : Name) (seen : Std.HashSet Name) :
    Std.HashSet Name :=
  if seen.contains n then seen else
  let seen := seen.insert n
  match env.find? n with
  | none => seen
  | some ci =>
    let cs := ci.type.getUsedConstants
      ++ (match ci.value? (allowOpaque := true) with
          | some v => v.getUsedConstants
          | none   => #[])
    cs.foldl (fun s c => visit env c s) seen

/-- 名前の 1 成分を、エスケープ（`«…»`）を付けない生の文字列で返す。 -/
def rawStr : Name → String
  | .str _ s => s
  | .num _ i => toString i
  | .anonymous => ""

/-- コンパイラが自動生成した宣言（記法マクロ・`deriving`・構成子補題など）か。
これらは「未使用」として報告しない。 -/
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

end DeadCode

/-- 根から到達できない宣言を、モジュールごとに列挙する。 -/
elab "#deadcode" : command => do
  let env ← getEnv
  let roots : List Name :=
    [``YAPSS.PSS_terminates_unconditional, ``YAPSS.no_infinite_expansion_holds,
     ``YAPSS.pss_cofinality_holds, ``YAPSS.wf_olt_ST_PS_holds, ``YAPSS.wf_Rnf_holds]
  let reach := roots.foldl (fun s r => DeadCode.visit env r s) (∅ : Std.HashSet Name)
  -- 本リポジトリのモジュールに属する宣言だけを対象にする
  -- 本リポジトリのモジュール（`lakefile.toml` の roots と同じ）
  let ours : List Name :=
    [`Pss, `Term, `Decrease, `Reduction, `Cnf, `Seqlex, `Column,
     `Cofinality, `ArgDom, `Wset, `Final]
  let mods := env.header.moduleNames
  let mut rows : Array (Name × Name × Nat) := #[]      -- (module, decl, line)
  let mut total : Std.HashMap Name Nat := {}
  let mut dead  : Std.HashMap Name Nat := {}
  for (n, ci) in env.constants.toList do
    if DeadCode.isGenerated n then continue
    -- 構成子は単独では消せない（`inductive` ごと消えるときに一緒に消える）
    if ci matches .ctorInfo _ | .recInfo _ | .inductInfo _ then continue
    let some idx := env.getModuleIdxFor? n | continue
    let m := mods[idx.toNat]!
    unless ours.contains m do continue
    total := total.insert m ((total.getD m 0) + 1)
    if reach.contains n then continue
    dead := dead.insert m ((dead.getD m 0) + 1)
    let line ← match ← findDeclarationRanges? n with
      | some r => pure r.range.pos.line
      | none   => pure 0
    rows := rows.push (m, n, line)
  let sorted := rows.qsort fun a b =>
    if a.1 == b.1 then a.2.2 < b.2.2 else a.1.toString < b.1.toString
  let mut out := s!"未使用宣言 {sorted.size} 件\n"
  for (m, n, line) in sorted do
    out := out ++ s!"  {m}:{line}  {n}\n"
  out := out ++ "\nモジュール別（未使用 / 全体）\n"
  for m in mods do
    if ours.contains m then
      let t := total.getD m 0
      if t > 0 then out := out ++ s!"  {m}: {dead.getD m 0} / {t}\n"
  logInfo out

#deadcode
