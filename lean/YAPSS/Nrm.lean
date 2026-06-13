/-
**Value normalization `nrm`**: a small syntactic projection sending an
arbitrary term to a Buchholz OT term (`wf3`) of the same `ψ`-value.
Lean port of `ord/nrm.thy`.

At a principal `D_a(b)` whose argument violates the OT3 condition (some
`g ∈ G_a(b)` with `¬ g <o b`), the value `ψ_a` is constant on the interval up
to the offending critical value, so the name may be rewritten to
`D_a(max G_a(b))` without changing the value; iterating yields the OT-normal
name.  Sums absorb principals dominated by a later one (ordinal addition).

The route to `wf Rnf`:
  * `wf3_nrm`: every `nrm`-image is an OT term             (proved below)
  * `nrm_order_pres`: on `NF`, `v <o u → nrm v <o nrm u`   (THE remaining
    core, `sorry` exactly as in the Isabelle source; validated empirically
    on 2.6 million pairs, zero violations)
  * `wf_olt_wf3`: `<o` is well-founded on OT terms         (proved, Otembed)
-/
import YAPSS.Otembed

namespace YAPSS

open Three

/-! ## Decidability of `olt` -/

instance oltDecidable : ∀ x y : Three, Decidable (olt x y)
  | Z, Z => isFalse (fun h => h)
  | Z, P _ _ _ => isTrue trivial
  | P _ _ _, Z => isFalse (fun h => h)
  | P _ b c, P _ f g =>
    haveI := oltDecidable b f
    haveI := oltDecidable c g
    decidable_of_iff _ olt_P_P.symm

/-! ## Executable critical-term collection -/

def Glist (u : ℕ) : Three → List Three
  | Z => []
  | P a b c => (if u ≤ a then b :: Glist u b else []) ++ Glist u c

@[simp] theorem Glist_Z (u : ℕ) : Glist u Z = [] := rfl
theorem Glist_P (u a : ℕ) (b c : Three) :
    Glist u (P a b c) = (if u ≤ a then b :: Glist u b else []) ++ Glist u c := rfl

theorem mem_Glist {u : ℕ} {t x : Three} : x ∈ Glist u t ↔ x ∈ Gterm u t := by
  induction t with
  | Z => simp
  | P a b c ihb ihc =>
    rw [Glist_P, mem_Gterm_P]
    by_cases h : u ≤ a <;> simp [h, ihb, ihc, or_assoc]

def maxo : Three → List Three → Three
  | x, [] => x
  | x, y :: ys => maxo (if olt x y then y else x) ys

@[simp] theorem maxo_nil (x : Three) : maxo x [] = x := rfl
theorem maxo_cons (x y : Three) (ys : List Three) :
    maxo x (y :: ys) = maxo (if olt x y then y else x) ys := rfl

theorem maxo_in (x : Three) (ys : List Three) : maxo x ys ∈ x :: ys := by
  induction ys generalizing x with
  | nil => simp
  | cons y ys ih =>
    rw [maxo_cons]
    by_cases h : olt x y
    · rw [if_pos h]
      rcases List.mem_cons.1 (ih y) with he | hm
      · rw [he]
        simp
      · simp [hm]
    · rw [if_neg h]
      rcases List.mem_cons.1 (ih x) with he | hm
      · rw [he]
        simp
      · simp [hm]

theorem maxo_hdtl_in {gs : List Three} (h : gs ≠ []) :
    maxo gs.headI gs.tail ∈ gs := by
  cases gs with
  | nil => exact absurd rfl h
  | cons g gs => exact maxo_in g gs

/-! ## Projection at a collapse point -/

def proj (u : ℕ) (b : Three) : Three :=
  let gs := (Glist u b).filter fun g => ¬ olt g b
  if gs = [] then b else proj u (maxo gs.headI gs.tail)
  termination_by tsize b
  decreasing_by
    rename_i h
    have hin : maxo gs.headI gs.tail ∈ gs := maxo_hdtl_in h
    have hG : maxo gs.headI gs.tail ∈ Gterm u b := by
      have := List.mem_of_mem_filter (hin : _ ∈ (Glist u b).filter _)
      exact mem_Glist.1 this
    exact Gterm_tsize hG

theorem proj_id {u : ℕ} {b : Three}
    (h : (Glist u b).filter (fun g => ¬ olt g b) = []) : proj u b = b := by
  rw [proj]
  simp only [h]
  rfl

theorem proj_rec {u : ℕ} {b : Three}
    (h : (Glist u b).filter (fun g => ¬ olt g b) ≠ []) :
    proj u b = proj u (maxo ((Glist u b).filter (fun g => ¬ olt g b)).headI
                          ((Glist u b).filter (fun g => ¬ olt g b)).tail) := by
  rw [proj]
  simp only [if_neg h]

theorem Gterm_wf3 {u : ℕ} {t x : Three} (hx : x ∈ Gterm u t) (ht : wf3 t) :
    wf3 x :=
  wf3_Gterm ht hx

theorem proj_wf3 {u : ℕ} {b : Three} (hb : wf3 b) : wf3 (proj u b) := by
  generalize hs : tsize b = n
  induction n using Nat.strong_induction_on generalizing b with
  | _ n IH =>
    subst hs
    by_cases h : (Glist u b).filter (fun g => ¬ olt g b) = []
    · rw [proj_id h]
      exact hb
    · rw [proj_rec h]
      have hin := maxo_hdtl_in h
      have hG : maxo ((Glist u b).filter (fun g => ¬ olt g b)).headI
          ((Glist u b).filter (fun g => ¬ olt g b)).tail ∈ Gterm u b :=
        mem_Glist.1 (List.mem_of_mem_filter hin)
      exact IH (tsize _) (Gterm_tsize hG) (Gterm_wf3 hG hb) rfl

theorem proj_G (u : ℕ) (b : Three) : ∀ g ∈ Gterm u (proj u b), olt g (proj u b) := by
  generalize hs : tsize b = n
  induction n using Nat.strong_induction_on generalizing b with
  | _ n IH =>
    subst hs
    by_cases h : (Glist u b).filter (fun g => ¬ olt g b) = []
    · rw [proj_id h]
      intro g hg
      have hmem : g ∈ Glist u b := mem_Glist.2 hg
      by_contra hng
      have hmem2 : g ∈ (Glist u b).filter (fun g => ¬ olt g b) :=
        List.mem_filter.2 ⟨hmem, by simpa using hng⟩
      rw [h] at hmem2
      simp at hmem2
    · rw [proj_rec h]
      have hin := maxo_hdtl_in h
      have hG : maxo ((Glist u b).filter (fun g => ¬ olt g b)).headI
          ((Glist u b).filter (fun g => ¬ olt g b)).tail ∈ Gterm u b :=
        mem_Glist.1 (List.mem_of_mem_filter hin)
      exact IH (tsize _) (Gterm_tsize hG) _ rfl

/-! ## Sum insertion with absorption, and `nrm` -/

def ins (a : ℕ) (b : Three) : Three → Three
  | Z => P a b Z
  | P e f g => if a < e ∨ (a = e ∧ olt b f) then P e f g else P a b (P e f g)

@[simp] theorem ins_Z (a : ℕ) (b : Three) : ins a b Z = P a b Z := rfl
theorem ins_P (a : ℕ) (b : Three) (e : ℕ) (f g : Three) :
    ins a b (P e f g)
      = if a < e ∨ (a = e ∧ olt b f) then P e f g else P a b (P e f g) := rfl

def nrm : Three → Three
  | Z => Z
  | P a b c => ins a (proj a (nrm b)) (nrm c)

@[simp] theorem nrm_Z : nrm Z = Z := rfl
theorem nrm_P (a : ℕ) (b c : Three) :
    nrm (P a b c) = ins a (proj a (nrm b)) (nrm c) := rfl

theorem wf3_ins {a : ℕ} {b t : Three} (wb : wf3 b) (wt : wf3 t)
    (g : ∀ x ∈ Gterm a b, olt x b) : wf3 (ins a b t) := by
  cases t with
  | Z => exact wf3_P.2 ⟨wb, trivial, g, trivial⟩
  | P e f gg =>
    rw [ins_P]
    by_cases h : a < e ∨ (a = e ∧ olt b f)
    · rw [if_pos h]
      exact wt
    · rw [if_neg h]
      have hd : hdle (P e f gg) (P a b Z) := by
        push Not at h
        obtain ⟨hae, hef⟩ := h
        rw [hdle_P_P]
        rcases Nat.lt_or_ge e a with hlt | hge
        · exact Or.inl hlt
        · have hea : e = a := by omega
          subst hea
          rcases olt_total f b with hfb | rfl | hbf
          · exact Or.inr ⟨rfl, Or.inl hfb⟩
          · exact Or.inr ⟨rfl, Or.inr rfl⟩
          · exact absurd hbf (hef rfl)
      exact wf3_P.2 ⟨wb, wt, g, hd⟩

theorem wf3_nrm (t : Three) : wf3 (nrm t) := by
  induction t with
  | Z => trivial
  | P a b c ihb ihc =>
    rw [nrm_P]
    exact wf3_ins (proj_wf3 ihb) ihc (proj_G a (nrm b))

/-! ## Value preservation of `ins` (value route — see git/nrm_stepdec_design.md)

`ins a b c = oV (P a b c)`: in the absorbing branch the inserted principal
`ψ_a(oV b)` is `< ψ_e(oV f)` (the leading additive-principal term of `oV c`),
so it is swallowed.  The argument-equal subcase uses Buchholz strict
monotonicity 1.3, which needs `oV b ∈ C_a(oV b)` — supplied by the OT3 condition
`hGb` at level `a` (in the `nrm` use this is exactly `proj_G`). -/
theorem oV_ins {a : ℕ} {b c : Three} (wb : wf3 b) (wc : wf3 c)
    (hGb : ∀ x ∈ Gterm a b, olt x b) :
    oV.{u} (ins a b c) = oV (P a b c) := by
  cases c with
  | Z => rfl
  | P e f g =>
    rw [ins_P]
    by_cases h : a < e ∨ (a = e ∧ olt b f)
    · rw [if_pos h]
      obtain ⟨wff, wfg, -, -⟩ := wf3_P.1 wc
      have hlt : psi.{u} (oV b) a < psi (oV f) e := by
        rcases h with hae | ⟨rfl, hbf⟩
        · exact psi_subscript_jump hae _ _
        · have obf : oV.{u} b < oV f := oV_order_pres wb wff hbf
          have hmem : oV.{u} b ∈ Cset (psiRes (oV b)) (oV b) a := by
            apply Ccond_of_lt
            intro x hx
            exact oV_order_pres (wf3_Gterm wb hx) wb (hGb x hx)
          exact psi_strict_mono_arg obf hmem
      have hp : Ordinal.IsPrincipal (· + ·) (psi.{u} (oV f) e) :=
        fun {x y} hx hy => (psi_addprinc (oV f) e).2 x y hx hy
      have absorb : psi.{u} (oV b) a + psi (oV f) e = psi (oV f) e :=
        hp.add_eq_right hlt
      simp only [oV_P]
      rw [← add_assoc, absorb]
    · rw [if_neg h]

/-- Converse of `oV_order_pres` on `wf3` (value route lemma 4): on the Buchholz
class the value order refines back to `<o`.  Via `olt`-trichotomy + the forward
strict monotonicity. -/
theorem oV_order_refl {x y : Three} (wx : wf3 x) (wy : wf3 y)
    (h : oV.{u} x < oV y) : olt x y := by
  rcases olt_total x y with hxy | rfl | hyx
  · exact hxy
  · exact absurd h (lt_irrefl _)
  · exact absurd (oV_order_pres wy wx hyx) (not_lt.2 h.le)

/-- Value route lemma 3, conditional on `psi_proj` (the Buchholz collapsing
core, still open — see git/nrm_stepdec_design.md M1–M3).  Given that `proj`
preserves the outer `ψ_a`-value, `nrm` preserves the whole `oV`-value.  This
verifies the reduction `oV_ins ∘ psi_proj ⟹ oV∘nrm = oV` is sound. -/
theorem oV_nrm_of_psi_proj
    (psi_proj : ∀ (a : ℕ) (b : Three), wf3 b →
      psi.{u} (oV (proj a b)) a = psi (oV b) a) :
    ∀ t : Three, oV.{u} (nrm t) = oV t := by
  intro t
  induction t with
  | Z => rfl
  | P a b c ihb ihc =>
    rw [nrm_P]
    rw [oV_ins (proj_wf3 (wf3_nrm b)) (wf3_nrm c) (proj_G a (nrm b))]
    rw [oV_P, oV_P, psi_proj a (nrm b) (wf3_nrm b), ihb, ihc]

/-! ## The remaining core: order preservation on `NF`

Validated empirically on 2,643,843 pairs of (hereditary blocks of)
standard-form translates: zero collapses, zero reversals.  The counterexample
outside `NF` is `y₂ = p₀(p₁(y₁)) <o y₁ = p₀(p₁(p₁(0)))` with
`nrm y₂ = nrm y₁`; its pair sequence `(0,0)(1,1)(2,0)(3,1)(4,1)` is not
standard, so the standardness discipline (row-1 parenthood) is what the proof
must exploit. -/

/-- The `proj` fixpoint is `a`-reduced: its value lies in its own `C_a`.
From `proj_G` (OT3 at level `a`) + `oV_order_pres`.  A building block for the
collapsing core. -/
theorem proj_oV_mem_C (a : ℕ) (b : Three) (wb : wf3 b) :
    oV.{u} (proj a b) ∈ Cset (psiRes (oV (proj a b))) (oV (proj a b)) a := by
  apply Ccond_of_lt
  intro x hx
  exact oV_order_pres (wf3_Gterm (proj_wf3 wb) hx) (proj_wf3 wb) (proj_G a b x hx)

/-- **`psi_proj` reduced to a precise per-step obligation.**  Strong induction on
`tsize b` along `proj`'s recursion: if the violator filter is empty, `proj a b = b`
(refl); otherwise `proj a b = proj a g*` for `g* = maxo …` (the max OT3-violator,
`g* ∈ G_a(b)`, `¬ g* <o b`), and `ψ_a(oV g*) = ψ_a(oV b)` follows from the
per-step C-membership hypothesis `notmem` via `psi_eq_of_notMem` (using
`oV b ≤ oV g*`); the IH closes `ψ_a(oV(proj a g*)) = ψ_a(oV g*)`.  This isolates
the whole collapsing core to `notmem`. -/
theorem psi_proj_of_notmem (a : ℕ)
    (notmem : ∀ (b' g : Three), wf3 b' → g ∈ Gterm a b' → ¬ olt g b' →
      psi.{u} (oV b') a ∉ Cset (psiRes (oV g)) (oV g) a)
    (b : Three) (wb : wf3 b) :
    psi.{u} (oV (proj a b)) a = psi (oV b) a := by
  generalize hs : tsize b = n
  induction n using Nat.strong_induction_on generalizing b with
  | _ n IH =>
    subst hs
    by_cases h : (Glist a b).filter (fun g => ¬ olt g b) = []
    · rw [proj_id h]
    · rw [proj_rec h]
      have hin := maxo_hdtl_in h
      set g := maxo ((Glist a b).filter (fun g => ¬ olt g b)).headI
                    ((Glist a b).filter (fun g => ¬ olt g b)).tail with hg
      have hgmem : g ∈ Gterm a b := mem_Glist.1 (List.mem_of_mem_filter hin)
      have hgviol : ¬ olt g b := by
        have := List.of_mem_filter hin
        simpa using this
      have wg : wf3 g := wf3_Gterm wb hgmem
      have hsz : tsize g < tsize b := Gterm_tsize hgmem
      have ihg : psi.{u} (oV (proj a g)) a = psi (oV g) a := IH (tsize g) hsz g wg rfl
      have hle : oV.{u} b ≤ oV g := by
        rcases olt_total b g with hbg | hbe | hgb
        · exact le_of_lt (oV_order_pres wb wg hbg)
        · rw [hbe]
        · exact absurd hgb hgviol
      have hstep : psi.{u} (oV g) a = psi (oV b) a :=
        (psi_eq_of_notMem hle (notmem b g wb hgmem hgviol)).symm
      rw [ihg]; exact hstep

/-- **The precise remaining collapsing obligation** (replaces the old opaque
`psi_proj` sorry): at a non-`a`-reduced `b'` with an OT3-violator `g ∈ G_a(b')`
(`¬ g <o b'`, so `oV b' ≤ oV g`), the principal value `ψ_a(oV b')` is *not* in
`C_a(oV g)`.  Equivalent (via 1.5 + monotonicity) to `ψ_a(oV b') = ψ_a(oV g)` —
the Buchholz collapse across the critical point.  This is the genuine necessity
core (and is exactly where a non-canonical `b'` defeats the `wf3` necessity
`NEC_of_argExtract`); still open. -/
theorem psi_proj_notmem (a : ℕ) (b' g : Three) (wb' : wf3 b')
    (hg : g ∈ Gterm a b') (hv : ¬ olt g b') :
    psi.{u} (oV b') a ∉ Cset (psiRes (oV g)) (oV g) a := by
  sorry

/-- **Hard core 1 (Buchholz collapsing):** `proj` preserves the outer `ψ_a`-value.
Assembled from `psi_proj_of_notmem` and the per-step obligation `psi_proj_notmem`. -/
theorem psi_proj (a : ℕ) (b : Three) (wb : wf3 b) :
    psi.{u} (oV (proj a b)) a = psi (oV b) a :=
  psi_proj_of_notmem a (psi_proj_notmem a) b wb

/-- **Hard core 2 (standardness / UBI):** on `NF` the subscript-first order
refines the `ψ`-value order.  Off `NF` this fails (the `y₂ <o y₁`, equal-value
counterexample above is non-standard), so the proof must consume standardness
(the UBI valid-forest / row-1 parenthood invariant). Still open. -/
theorem oV_nf_order_pres {v u : Three} (hv : v ∈ NF) (hu : u ∈ NF)
    (h : olt v u) : oV.{u} v < oV u := by
  sorry

/-- The remaining core, now REDUCED to the two hard cores above via the proven
glue (`oV_ins`, `oV_order_refl`, `oV_nrm_of_psi_proj`).  This assembly is
kernel-checked; only `psi_proj` and `oV_nf_order_pres` remain `sorry`. -/
theorem nrm_order_pres {v u : Three} (hv : v ∈ NF) (hu : u ∈ NF)
    (h : olt v u) : olt (nrm v) (nrm u) := by
  apply oV_order_refl.{0} (wf3_nrm v) (wf3_nrm u)
  rw [oV_nrm_of_psi_proj.{0} psi_proj.{0} v, oV_nrm_of_psi_proj.{0} psi_proj.{0} u]
  exact oV_nf_order_pres.{0} hv hu h

/-! ## Well-foundedness of `<o` on `NF`, and PSS termination -/

theorem wf_Rnf_nrm : WellFounded Rnf := by
  refine Subrelation.wf ?_ (InvImage.wf nrm wf_olt_wf3)
  rintro v u ⟨hlt, hu, hv⟩
  exact ⟨nrm_order_pres hv hu hlt, wf3_nrm v, wf3_nrm u⟩

theorem PSS_terminates_strong : WellFounded stepRel :=
  step_terminates wf_Rnf_nrm

/-! ## Step decrease: the weaker (live) obligation

For termination alone, only the expansion-step pairs must decrease — a
single-host statement, amenable to induction over the `oper` case analysis
together with the sequence-side characterization of `proj`.
`nrm_order_pres` subsumes this lemma via `m_step_decreases`. -/

theorem nrm_step_dec {M : PairSeq} {n : ℕ} (hM : ST_PS M)
    (L : 1 < M.length) (hn : 1 ≤ n) :
    olt (nrm (translate (M⟦n⟧))) (nrm (translate M)) := by
  have st : step M (M⟦n⟧) := step.step_oper L hn
  have TS : ST_PS (M⟦n⟧) := step_in_ST_PS hM st
  exact nrm_order_pres ⟨M⟦n⟧, TS, rfl⟩ ⟨M, hM, rfl⟩ (m_step_decreases L hn)

theorem PSS_terminates_nrm : WellFounded stepRel := by
  refine Subrelation.wf ?_ (InvImage.wf (fun M => nrm (translate M)) wf_olt_wf3)
  rintro T M ⟨hM, hstep⟩
  cases hstep with
  | @step_oper n L hn =>
    exact ⟨nrm_step_dec hM L hn, wf3_nrm _, wf3_nrm _⟩

end YAPSS
