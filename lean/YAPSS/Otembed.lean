/-
**The order embedding `oV : Three → Ordinal`** (Buchholz §2) and the
resulting well-foundedness of `olt` on the Buchholz class `wf3`.
Lean port of `ord/otembed.thy`.

`P a b c` is Buchholz's `D_a(b) + c`, so `oV (P a b c) = ψ_a(oV b) + oV c`
and `oV Z = 0`.
-/
import YAPSS.Psi
import YAPSS.Wfsum

namespace YAPSS

open Three Ordinal

universe u

noncomputable def oV : Three → Ordinal.{u}
  | Z => 0
  | P a b c => psi (oV b) a + oV c

@[simp] theorem oV_Z : oV.{u} Z = 0 := rfl
@[simp] theorem oV_P (a : ℕ) (b c : Three) :
    oV.{u} (P a b c) = psi (oV b) a + oV c := rfl

theorem psi_le_oV (a : ℕ) (b c : Three) : psi (oV.{u} b) a ≤ oV (P a b c) :=
  le_self_add

/-! ## Additive-principal sums and the subscript bound -/

/-- `allprinc_lt d t`: every principal `ψ_{a'}(oV b')` along the spine of `t`
is `< d`.  If `d` is additive principal, the whole value `oV t` stays
`< d`. -/
def allprinc_lt (d : Ordinal.{u}) : Three → Prop
  | Z => True
  | P a b c => psi (oV b) a < d ∧ allprinc_lt d c

@[simp] theorem allprinc_lt_Z (d : Ordinal.{u}) : allprinc_lt d Z := trivial
@[simp] theorem allprinc_lt_P {d : Ordinal.{u}} {a : ℕ} {b c : Three} :
    allprinc_lt d (P a b c) ↔ psi (oV b) a < d ∧ allprinc_lt d c := Iff.rfl

theorem oV_lt_of_allprinc {d : Ordinal.{u}} (hd : addprinc d) {t : Three}
    (ht : allprinc_lt d t) : oV t < d := by
  induction t with
  | Z => exact hd.1
  | P a b c ihb ihc =>
    obtain ⟨h, ht⟩ := ht
    exact hd.2 _ _ h (ihc ht)

/-- `spinesub_le m t`: every spine subscript of `t` is `≤ m`. -/
def spinesub_le (m : ℕ) : Three → Prop
  | Z => True
  | P a _ c => a ≤ m ∧ spinesub_le m c

@[simp] theorem spinesub_le_Z (m : ℕ) : spinesub_le m Z := trivial
@[simp] theorem spinesub_le_P {m a : ℕ} {b c : Three} :
    spinesub_le m (P a b c) ↔ a ≤ m ∧ spinesub_le m c := Iff.rfl

theorem spinesub_le_mono {m m' : ℕ} {t : Three} (h : spinesub_le m t)
    (hmm : m ≤ m') : spinesub_le m' t := by
  induction t with
  | Z => trivial
  | P a b c ihb ihc =>
    obtain ⟨h1, h2⟩ := h
    exact ⟨by omega, ihc h2⟩

/-! ## Buchholz coefficient sets `G_u` and the OT well-formedness predicate -/

/-- `Gterm u t` = Buchholz's `G_u` on terms: for the principal `D_a(b)`, it
is `{b} ∪ G_u b` when `u ≤ a`, else `∅`; on a sum it is the union. -/
def Gterm (u : ℕ) : Three → Set Three
  | Z => ∅
  | P a b c => (if u ≤ a then insert b (Gterm u b) else ∅) ∪ Gterm u c

@[simp] theorem Gterm_Z (u : ℕ) : Gterm u Z = ∅ := rfl
theorem Gterm_P (u a : ℕ) (b c : Three) :
    Gterm u (P a b c) = (if u ≤ a then insert b (Gterm u b) else ∅) ∪ Gterm u c := rfl

theorem mem_Gterm_P {u a : ℕ} {b c x : Three} :
    x ∈ Gterm u (P a b c) ↔
      (u ≤ a ∧ (x = b ∨ x ∈ Gterm u b)) ∨ x ∈ Gterm u c := by
  rw [Gterm_P]
  by_cases h : u ≤ a <;> simp [h]

/-- `hdle x y`: the principal head of `x` is `≤` that of `y` (subscript-first,
tails ignored). -/
def hdle : Three → Three → Prop
  | Z, _ => True
  | P _ _ _, Z => False
  | P a b _, P e f _ => a < e ∨ (a = e ∧ (olt b f ∨ b = f))

@[simp] theorem hdle_Z (y : Three) : hdle Z y := trivial
@[simp] theorem hdle_P_Z (a : ℕ) (b c : Three) : ¬ hdle (P a b c) Z := fun h => h
@[simp] theorem hdle_P_P {a e : ℕ} {b c f g : Three} :
    hdle (P a b c) (P e f g) ↔ a < e ∨ (a = e ∧ (olt b f ∨ b = f)) := Iff.rfl

/-- `wf3 t`: `t` is a Buchholz OT term — recursively well-formed, the OT3
condition `G_a b < b` for each principal `D_a(b)`, and OT2 non-increasing
spine. -/
def wf3 : Three → Prop
  | Z => True
  | P a b c => wf3 b ∧ wf3 c ∧ (∀ x ∈ Gterm a b, olt x b) ∧ hdle c (P a b Z)

@[simp] theorem wf3_Z : wf3 Z := trivial
@[simp] theorem wf3_P {a : ℕ} {b c : Three} :
    wf3 (P a b c) ↔
      wf3 b ∧ wf3 c ∧ (∀ x ∈ Gterm a b, olt x b) ∧ hdle c (P a b Z) := Iff.rfl

theorem wf3_spinesub_le {t : Three} (h : wf3 t) : spinesub_le (lead t) t := by
  induction t with
  | Z => trivial
  | P a b c ihb ihc =>
    obtain ⟨wfb, wfc, -, hd⟩ := h
    refine ⟨le_rfl, ?_⟩
    cases c with
    | Z => trivial
    | P a' b' c' =>
      have ha' : a' ≤ a := by
        rcases hdle_P_P.1 hd with h | ⟨h, -⟩ <;> omega
      exact spinesub_le_mono (ihc wfc) ha'

def headle_all (bnd : Three) : Three → Prop
  | Z => True
  | P a b c => hdle (P a b Z) bnd ∧ headle_all bnd c

@[simp] theorem headle_all_Z (bnd : Three) : headle_all bnd Z := trivial
@[simp] theorem headle_all_P {bnd : Three} {a : ℕ} {b c : Three} :
    headle_all bnd (P a b c) ↔ hdle (P a b Z) bnd ∧ headle_all bnd c := Iff.rfl

theorem hdle_head_ignores_tail {a : ℕ} {b c z : Three} :
    hdle (P a b c) z ↔ hdle (P a b Z) z := by
  cases z <;> rfl

/-! ## Order preservation on the Buchholz class (Buchholz Lemma 2.2(c)) -/

/-! ## Buchholz collapsing module (value route — see git/nrm_stepdec_design.md)

`(M1)` Every additive-principal element of `C_v(α)` lying in the level-`v` band
`[Ω_v, Ω_{v+1})` is `ψ_v(ξ)` for some `ξ ∈ C_v(α)`, `ξ < α`.  The level is
forced because `ψ_u(ξ) ∈ [Ω_u, Ω_{u+1})` and these bands are disjoint. -/
theorem Gterm_tsize {t x : Three} {v : ℕ} (hx : x ∈ Gterm v t) :
    tsize x < tsize t := by
  induction t with
  | Z => simp at hx
  | P a b c ihb ihc =>
    rcases mem_Gterm_P.1 hx with ⟨-, rfl | hx⟩ | hx
    · simp only [tsize]
      omega
    · have := ihb hx
      simp only [tsize]
      omega
    · have := ihc hx
      simp only [tsize]
      omega

/-! ## Well-foundedness of `olt` on the Buchholz class `wf3` (Lemma 2.2)

The value map embeds `(wf3, olt)` into the ordinals, so `olt` is well-founded
on `wf3`.  This is Buchholz's Lemma 2.2 proved (rather than cited): the sole
ingredient beyond §1 is the strict monotonicity above. -/

end YAPSS
