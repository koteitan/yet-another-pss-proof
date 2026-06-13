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

theorem allprinc_lt_jump {m e : ℕ} {t : Three} (h : spinesub_le m t)
    (hme : m < e) (β : Ordinal.{u}) : allprinc_lt (psi β e) t := by
  induction t with
  | Z => trivial
  | P a b c ihb ihc =>
    obtain ⟨h1, h2⟩ := h
    exact ⟨psi_subscript_jump (by omega) _ _, ihc h2⟩

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

/-- The head order `hdle` is transitive. -/
theorem hdle_trans {x y z : Three} (h1 : hdle x y) (h2 : hdle y z) : hdle x z := by
  cases x with
  | Z => trivial
  | P ax bx cx =>
    obtain ⟨ay, byy, cy, rfl⟩ : ∃ ay byy cy, y = P ay byy cy := by
      cases y with
      | Z => exact absurd h1 (hdle_P_Z _ _ _)
      | P ay byy cy => exact ⟨ay, byy, cy, rfl⟩
    obtain ⟨az, bz, cz, rfl⟩ : ∃ az bz cz, z = P az bz cz := by
      cases z with
      | Z => exact absurd h2 (hdle_P_Z _ _ _)
      | P az bz cz => exact ⟨az, bz, cz, rfl⟩
    rw [hdle_P_P] at h1 h2 ⊢
    rcases h1 with h1 | ⟨rfl, h1⟩
    · rcases h2 with h2 | ⟨rfl, -⟩
      · exact Or.inl (by omega)
      · exact Or.inl h1
    · rcases h2 with h2 | ⟨rfl, h2⟩
      · exact Or.inl h2
      · refine Or.inr ⟨rfl, ?_⟩
        rcases h1 with h1 | rfl
        · rcases h2 with h2 | rfl
          · exact Or.inl (olt_trans h1 h2)
          · exact Or.inl h1
        · exact h2

def headle_all (bnd : Three) : Three → Prop
  | Z => True
  | P a b c => hdle (P a b Z) bnd ∧ headle_all bnd c

@[simp] theorem headle_all_Z (bnd : Three) : headle_all bnd Z := trivial
@[simp] theorem headle_all_P {bnd : Three} {a : ℕ} {b c : Three} :
    headle_all bnd (P a b c) ↔ hdle (P a b Z) bnd ∧ headle_all bnd c := Iff.rfl

theorem hdle_head_ignores_tail {a : ℕ} {b c z : Three} :
    hdle (P a b c) z ↔ hdle (P a b Z) z := by
  cases z <;> rfl

theorem wf3_headle_aux {t bnd : Three} (h : wf3 t) (hd : hdle t bnd) :
    headle_all bnd t := by
  induction t with
  | Z => trivial
  | P a b c ihb ihc =>
    obtain ⟨wfb, wfc, -, hdc⟩ := h
    have hd' : hdle (P a b Z) bnd := hdle_head_ignores_tail.1 hd
    have hcbnd : hdle c bnd := hdle_trans hdc hd'
    exact ⟨hd', ihc wfc hcbnd⟩

theorem wf3_headle {a : ℕ} {b c : Three} (h : wf3 (P a b c)) :
    headle_all (P a b Z) c :=
  wf3_headle_aux h.2.1 h.2.2.2

/-! ## Order preservation on the Buchholz class (Buchholz Lemma 2.2(c)) -/

theorem oV_pos (a : ℕ) (b c : Three) : 0 < oV.{u} (P a b c) :=
  lt_of_lt_of_le (psi_addprinc (oV b) a).1 (psi_le_oV a b c)

/-- **Building values inside `C`**: if every `G_v`-critical subterm of `t` has
value `< α`, then `oV t ∈ C_v(α)`.  (Subscripts `< v` contribute
`ψ_a(·) < Ω_{a+1} ≤ Ω_v ⊆ C`; subscripts `≥ v` are `G`-collected, so their
arguments are below `α` and the `ψ`-closure of `C` applies; sums by
`+`-closure.)  No well-formedness needed. -/
theorem C_build {v : ℕ} {t : Three} {α : Ordinal.{u}}
    (h : ∀ x ∈ Gterm v t, oV x < α) :
    oV t ∈ Cset (psiRes α) α v := by
  induction t with
  | Z =>
    have z0 : (0 : Ordinal.{u}) < Om v := lt_of_lt_of_le zero_lt_one (one_le_Om v)
    exact Iio_Om_subset_Cset z0
  | P a b c ihb ihc =>
    have IHc : oV c ∈ Cset (psiRes α) α v := by
      apply ihc
      intro x hx
      exact h x (mem_Gterm_P.2 (Or.inr hx))
    have head : psi (oV b) a ∈ Cset (psiRes α) α v := by
      by_cases hva : v ≤ a
      · have bmem : oV b < α := h b (mem_Gterm_P.2 (Or.inl ⟨hva, Or.inl rfl⟩))
        have IHb : oV b ∈ Cset (psiRes α) α v := by
          apply ihb
          intro x hx
          exact h x (mem_Gterm_P.2 (Or.inl ⟨hva, Or.inr hx⟩))
        have := Cset_psi_closed IHb bmem a
        rwa [psiRes, if_pos bmem] at this
      · have av : a < v := by omega
        have hlt : psi (oV b) a < Om v := by
          calc psi (oV b) a < Om (a + 1) := psi_lt_Om_succ _ _
            _ ≤ Om v := Om_mono (by omega)
        exact Iio_Om_subset_Cset hlt
    exact Cset_add_closed head IHc

/-- The C-membership needed by 1.3, from order-preservation below the
argument. -/
theorem Ccond_of_lt {a : ℕ} {b : Three}
    (h : ∀ x ∈ Gterm a b, oV.{u} x < oV b) :
    oV.{u} b ∈ Cset (psiRes (oV b)) (oV b) a :=
  C_build h

/-! ## Buchholz collapsing module (value route — see git/nrm_stepdec_design.md)

`(M1)` Every additive-principal element of `C_v(α)` lying in the level-`v` band
`[Ω_v, Ω_{v+1})` is `ψ_v(ξ)` for some `ξ ∈ C_v(α)`, `ξ < α`.  The level is
forced because `ψ_u(ξ) ∈ [Ω_u, Ω_{u+1})` and these bands are disjoint. -/
theorem psi_form_of_mem {α δ : Ordinal.{u}} {v : ℕ}
    (hap : Ordinal.IsPrincipal (· + ·) δ)
    (hlo : Om v ≤ δ) (hhi : δ < Om (v + 1)) (hmem : δ ∈ Cset (psiRes α) α v) :
    ∃ ξ ∈ Cset (psiRes α) α v, ξ < α ∧ psi ξ v = δ := by
  obtain ⟨n, hn⟩ := Cset_mem_iff.1 hmem
  clear hmem
  induction n generalizing δ with
  | zero =>
    rw [Citer, Function.iterate_zero, id_eq] at hn
    exact absurd hn (not_lt.2 hlo)
  | succ n IH =>
    rw [Citer_succ, Cstep] at hn
    rcases hn with (h1 | h2) | h3
    · exact IH hap hlo hhi h1
    · obtain ⟨x, hx, y, hy, hxy⟩ := h2
      have hmemn : δ ∈ Citer (psiRes α) α v n := by
        rcases eq_or_lt_of_le (show x ≤ δ from hxy ▸ le_self_add) with hxe | hxlt
        · exact hxe ▸ hx
        · rcases eq_or_lt_of_le (show y ≤ δ from hxy ▸ le_add_self) with hye | hylt
          · exact hye ▸ hy
          · exact absurd hxy.symm (ne_of_gt (hap hxlt hylt))
      exact IH hap hlo hhi hmemn
    · obtain ⟨u, ⟨ξ, ⟨hξC, hξα⟩, hξδ⟩⟩ := Set.mem_iUnion.1 h3
      have hξα : ξ < α := hξα
      simp only [psiRes, if_pos hξα] at hξδ
      -- δ = psi ξ u; band-disjointness forces u = v
      have huv : u = v := by
        have h1 : Om u ≤ δ := hξδ ▸ Om_le_psi ξ u
        have h2 : δ < Om (u + 1) := hξδ ▸ psi_lt_Om_succ ξ u
        have hle1 : u ≤ v := by
          by_contra hc
          exact absurd (lt_of_le_of_lt h1 hhi) (not_lt.2 (Om_mono (by omega)))
        have hle2 : v ≤ u := by
          by_contra hc
          exact absurd (lt_of_le_of_lt hlo h2) (not_lt.2 (Om_mono (by omega)))
        omega
      subst huv
      exact ⟨ξ, Citer_subset_Cset hξC, hξα, hξδ⟩

/-- The plateau bridge: if `α ≤ β` and `ψ_v(α)` is *not* in `C_v(β)`, then
`ψ_v(α) = ψ_v(β)`.  (`ψ_v(β)` is the least non-member of `C_v(β)`, so it is
`≤ ψ_v(α)`; monotonicity gives the reverse.)  This reduces the collapsing
core `psi_proj` to showing `ψ_v(oV t) ∉ C_v(oV g*)` for the collapse target. -/
theorem psi_eq_of_notMem {α β : Ordinal.{u}} {v : ℕ} (hαβ : α ≤ β)
    (hnm : psi α v ∉ Cset (psiRes β) β v) : psi α v = psi β v := by
  refine le_antisymm (psi_mono_arg hαβ v) ?_
  rw [psi_unfold β v]
  exact csInf_le' hnm

/-- Strict monotonicity from membership in the *outer* `C_v(α)` (weaker
hypothesis than Buchholz 1.3's `ζ ∈ C_v(ζ)`, since `C_v(ζ) ⊆ C_v(α)`):
if `ζ ∈ C_v(α)` and `ζ < α` then `ψ_v(ζ) < ψ_v(α)`. -/
theorem psi_strict_mono_mem {α ζ : Ordinal.{u}} {v : ℕ}
    (hζ : ζ ∈ Cset (psiRes α) α v) (hζα : ζ < α) : psi ζ v < psi α v := by
  refine lt_of_le_of_ne (psi_mono_arg hζα.le v) (fun he => ?_)
  have hmem : psi ζ v ∈ Cset (psiRes α) α v := by
    have := Cset_psi_closed hζ hζα v
    rwa [psiRes, if_pos hζα] at this
  exact psi_notMem α v (he ▸ hmem)

/-- **NEC value-bound:** if `ψ_v(β) ∈ C_v(α)` then `β < α`.  (The arg of an
in-`C_v(α)` principal value lies below `α`.)  Proof: `M1` gives `ψ_v(β)=ψ_v(ζ)`
with `ζ<α, ζ∈C_v(α)`; `psi_strict_mono_mem` then forces `ψ_v(β)<ψ_v(α)`, so
`β<α` by monotonicity.  This is the principal/value half of the Buchholz
necessity direction. -/
theorem psi_arg_lt_of_mem {α β : Ordinal.{u}} {v : ℕ}
    (h : psi β v ∈ Cset (psiRes α) α v) : β < α := by
  have hap : Ordinal.IsPrincipal (· + ·) (psi β v) :=
    fun {x y} hx hy => (psi_addprinc β v).2 x y hx hy
  obtain ⟨ζ, hζmem, hζα, hζeq⟩ :=
    psi_form_of_mem hap (Om_le_psi β v) (psi_lt_Om_succ β v) h
  -- hζeq : psi ζ v = psi β v
  have hlt : psi β v < psi α v := by
    rw [← hζeq]; exact psi_strict_mono_mem hζmem hζα
  by_contra hc
  exact absurd (psi_mono_arg (not_lt.1 hc) v) (not_le.2 hlt)

/-- `C_v(α)` is closed under CNF-summand extraction: if `δ + r ∈ C_v(α)` with
`δ` additive-principal and `r < δ`, then `δ ∈ C_v(α)` and `r ∈ C_v(α)`.
Induction on the `Citer` stage; the `+`-generator case uses ordinal subtraction
and additive-principal absorption to recurse; the `ψ`-generator case forces
`r = 0` (a `ψ`-value is additive-principal). -/
theorem Cset_add_split {α : Ordinal.{u}} {v : ℕ} {δ r : Ordinal.{u}}
    (hr : r < δ) (hprin : Ordinal.IsPrincipal (· + ·) δ)
    (hmem : δ + r ∈ Cset (psiRes α) α v) :
    δ ∈ Cset (psiRes α) α v ∧ r ∈ Cset (psiRes α) α v := by
  obtain ⟨n, hn⟩ := Cset_mem_iff.1 hmem
  clear hmem
  induction n generalizing r with
  | zero =>
    rw [Citer, Function.iterate_zero, id_eq] at hn
    exact ⟨Iio_Om_subset_Cset (lt_of_le_of_lt (le_self_add : δ ≤ δ + r) hn),
           Iio_Om_subset_Cset (lt_of_le_of_lt (le_add_self : r ≤ δ + r) hn)⟩
  | succ n IH =>
    rw [Citer_succ, Cstep] at hn
    rcases hn with (h1 | h2) | h3
    · exact IH hr h1
    · obtain ⟨u, hu, w, hw, huw⟩ := h2
      dsimp only at huw
      rcases lt_or_ge u δ with hδu | hδu
      · -- u < δ : absorption u + δ = δ, then w = δ + r
        rcases lt_or_ge w δ with hδw | hδw
        · -- u < δ, w < δ : u + w < δ ≤ δ + r contradicts huw
          exact absurd huw
            (ne_of_lt (lt_of_lt_of_le (hprin hδu hδw) le_self_add))
        · obtain ⟨w', rfl⟩ := exists_add_of_le hδw
          have habs : u + δ = δ := hprin.add_eq_right hδu
          have heq : δ + w' = δ + r := by
            rw [← add_assoc, habs] at huw; exact huw
          have hw'r : w' = r := (add_right_inj δ).1 heq
          subst hw'r
          exact IH hr hw
      · -- δ ≤ u : u = δ + u', recurse on δ + u' ∈ Citer n
        obtain ⟨u', rfl⟩ := exists_add_of_le hδu
        have hcancel : u' + w = r := by
          have h := huw
          rw [add_assoc] at h
          exact (add_right_inj δ).1 h
        have hu'lt : u' < δ := lt_of_le_of_lt (hcancel ▸ (le_self_add : u' ≤ u' + w)) hr
        obtain ⟨hδmem, hu'mem⟩ := IH hu'lt hu
        exact ⟨hδmem, hcancel ▸ Cset_add_closed hu'mem (Citer_subset_Cset hw)⟩
    · obtain ⟨uu, ⟨ζ, ⟨hζC, hζα⟩, hζδ⟩⟩ := Set.mem_iUnion.1 h3
      have hζα : ζ < α := hζα
      simp only [psiRes, if_pos hζα] at hζδ
      have hr0 : r = 0 := by
        by_contra hne
        have hrpos : 0 < r := pos_iff_ne_zero.2 hne
        have hap : Ordinal.IsPrincipal (· + ·) (δ + r) := by
          rw [← hζδ]; exact fun {x y} hx hy => (psi_addprinc ζ uu).2 x y hx hy
        have hδlt : δ < δ + r := by
          rcases lt_or_eq_of_le (le_self_add : δ ≤ δ + r) with h | h
          · exact h
          · have h2 : δ + 0 = δ + r := by rw [add_zero]; exact h
            exact absurd ((add_right_inj δ).1 h2).symm (ne_of_gt hrpos)
        exact absurd (hap hδlt (lt_of_lt_of_le hr le_self_add)) (lt_irrefl _)
      subst hr0
      rw [add_zero] at hζδ
      refine ⟨?_, Iio_Om_subset_Cset (lt_of_lt_of_le zero_lt_one (one_le_Om v))⟩
      rw [← hζδ]
      have := Cset_psi_closed (Citer_subset_Cset hζC) hζα uu
      rwa [psiRes, if_pos hζα] at this

/-- `G`-critical subterms are well-formed (Buchholz's Proposition
`a ∈ OT → G_u a ⊆ OT`). -/
theorem wf3_Gterm {t x : Three} (ht : wf3 t) {v : ℕ} (hx : x ∈ Gterm v t) :
    wf3 x := by
  induction t with
  | Z => simp at hx
  | P a b c ihb ihc =>
    obtain ⟨wfb, wfc, -, -⟩ := ht
    rcases mem_Gterm_P.1 hx with ⟨-, rfl | hx⟩ | hx
    · exact wfb
    · exact ihb wfb hx
    · exact ihc wfc hx

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

/-- Every spine principal of a well-formed term whose head is dominated by
`D_a(b)` (with `b ≺ f`) is `< ψ_a(oV f)`: subscript-smaller ones by the jump,
subscript-equal ones by strict monotonicity 1.3. -/
theorem allprinc_lt_spine {n : ℕ} {a : ℕ} {b f : Three}
    (mono : ∀ b', olt b' f → wf3 b' → tsize b' < n → oV.{u} b' < oV f)
    (ccnd : ∀ (a' : ℕ) (b' c'' : Three), wf3 (P a' b' c'') → tsize b' < n →
      oV.{u} b' ∈ Cset (psiRes (oV b')) (oV b') a')
    (bf : olt b f) :
    ∀ {c : Three}, headle_all (P a b Z) c → wf3 c → tsize c < n →
      allprinc_lt (psi (oV.{u} f) a) c := by
  intro c
  induction c with
  | Z => intro _ _ _; trivial
  | P a' b' c'' ihb ihc =>
    intro hall wfn hsz
    have wfn' := wfn
    obtain ⟨hd, hall'⟩ := hall
    obtain ⟨wfb', wfc'', -, -⟩ := wfn
    have sb' : tsize b' < n := by
      have : tsize b' < tsize (P a' b' c'') := by
        simp only [tsize]
        omega
      omega
    have szc'' : tsize c'' < n := by
      have : tsize c'' < tsize (P a' b' c'') := by
        simp only [tsize]
        omega
      omega
    have head : psi (oV b') a' < psi (oV f) a := by
      rcases hdle_P_P.1 hd with h | ⟨rfl, bb⟩
      · exact psi_subscript_jump h _ _
      · have hb'f : olt b' f := by
          rcases bb with h | rfl
          · exact olt_trans h bf
          · exact bf
        have ob : oV b' < oV f := mono b' hb'f wfb' sb'
        have mem : oV b' ∈ Cset (psiRes (oV b')) (oV b') a' := ccnd a' b' c'' wfn' sb'
        exact psi_strict_mono_arg ob mem
    exact ⟨head, ihc hall' wfc'' szc''⟩

/-- **Buchholz Lemma 2.2(c)** on `wf3` (= Buchholz `OT`): the value map is
strictly monotone.  Main induction on the size of the *left* term. -/
theorem oV_order_pres {v u' : Three} (hv : wf3 v) (hu : wf3 u') (h : olt v u') :
    oV.{u} v < oV u' := by
  generalize hs : tsize v = n
  induction n using Nat.strong_induction_on generalizing v u' with
  | _ n IHn =>
    subst hs
    have ccnd : ∀ (a' : ℕ) (b' c' : Three), wf3 (P a' b' c') → tsize b' < tsize v →
        oV.{u} b' ∈ Cset (psiRes (oV b')) (oV b') a' := by
      intro a' b' c' wfn szb'
      have wfb' : wf3 b' := wfn.1
      have G : ∀ x ∈ Gterm a' b', olt x b' := wfn.2.2.1
      apply Ccond_of_lt
      intro x xG
      have wfx : wf3 x := wf3_Gterm wfb' xG
      have szx : tsize x < tsize b' := Gterm_tsize xG
      exact IHn (tsize x) (by omega) wfx wfb' (G x xG) rfl
    cases v with
    | Z =>
      obtain ⟨e, f, g, rfl⟩ : ∃ e f g, u' = P e f g := by
        cases u' with
        | Z => exact absurd h (olt_irrefl Z)
        | P e f g => exact ⟨e, f, g, rfl⟩
      simpa using oV_pos e f g
    | P a b c =>
      obtain ⟨e, f, g, rfl⟩ : ∃ e f g, u' = P e f g := by
        cases u' with
        | Z => exact absurd h (not_olt_Z _)
        | P e f g => exact ⟨e, f, g, rfl⟩
      obtain ⟨wfb, wfc, hG, hhd⟩ := wf3_P.1 hv
      obtain ⟨wff, wfg, -, -⟩ := wf3_P.1 hu
      rcases olt_P_P.1 h with hsub | ⟨rfl, harg⟩ | ⟨rfl, rfl, htail⟩
      · -- subscript case
        have sple : spinesub_le a (P a b c) := wf3_spinesub_le hv
        have hap : allprinc_lt (psi (oV f) e) (P a b c) :=
          allprinc_lt_jump sple hsub _
        calc oV (P a b c) < psi (oV f) e :=
            oV_lt_of_allprinc (psi_addprinc _ _) hap
          _ ≤ oV (P e f g) := psi_le_oV e f g
      · -- argument case
        have mono : ∀ b', olt b' f → wf3 b' → tsize b' < tsize (P a b c) →
            oV.{u} b' < oV f := by
          intro b' A1 A2 A3
          exact IHn (tsize b') (by omega) A2 wff A1 rfl
        have hac : headle_all (P a b Z) c := wf3_headle hv
        have szc : tsize c < tsize (P a b c) := by
          simp only [tsize]
          omega
        have spine : allprinc_lt (psi (oV f) a) c :=
          allprinc_lt_spine mono ccnd harg hac wfc szc
        have szb : tsize b < tsize (P a b c) := by
          simp only [tsize]
          omega
        have obf : oV b < oV f := mono b harg wfb szb
        have memb : oV b ∈ Cset (psiRes (oV b)) (oV b) a := ccnd a b c hv szb
        have lead : psi (oV b) a < psi (oV f) a := psi_strict_mono_arg obf memb
        have hap : allprinc_lt (psi (oV f) a) (P a b c) := ⟨lead, spine⟩
        calc oV (P a b c) < psi (oV f) a :=
            oV_lt_of_allprinc (psi_addprinc _ _) hap
          _ ≤ oV (P a f g) := psi_le_oV a f g
      · -- tail case
        have szc : tsize c < tsize (P a b c) := by
          simp only [tsize]
          omega
        have hcg : oV c < oV g := IHn (tsize c) (by omega) wfc wfg htail rfl
        show psi (oV b) a + oV c < psi (oV b) a + oV g
        exact add_lt_add_right hcg _

/-! ## Well-foundedness of `olt` on the Buchholz class `wf3` (Lemma 2.2)

The value map embeds `(wf3, olt)` into the ordinals, so `olt` is well-founded
on `wf3`.  This is Buchholz's Lemma 2.2 proved (rather than cited): the sole
ingredient beyond §1 is the strict monotonicity above. -/

/-- `olt` restricted to the Buchholz class. -/
def oltWf3 (w x : Three) : Prop := olt w x ∧ wf3 w ∧ wf3 x

theorem wf_olt_wf3 : WellFounded oltWf3 := by
  refine Subrelation.wf ?_ (InvImage.wf oV.{0} Ordinal.lt_wf)
  rintro w x ⟨hlt, hw, hx⟩
  exact oV_order_pres hw hx hlt

end YAPSS
