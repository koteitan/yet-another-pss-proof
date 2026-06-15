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

/-- **`psi_proj_notmem` reduced to interval non-canonicity.**  The per-step
collapse obligation `ψ_a(oV b') ∉ C_a(oV g)` — equivalently the plateau equality
`ψ_a(oV b') = ψ_a(oV g)` (`psi_notMem_iff_eq`) — follows from the proven plateau
lemma `collapse_le` once every ordinal in `[oV b', oV g)` is `a`-non-canonical.
This isolates the genuine remaining core to the interval hypothesis `H` (true,
since `psi_proj_notmem` is, but a statement about *all* ordinals in the gap, not
just term values). -/
theorem psi_proj_notmem_of_intervalNoncanon (a : ℕ) (b' g : Three) (wb' : wf3 b')
    (hg : g ∈ Gterm a b') (hv : ¬ olt g b')
    (H : ∀ γ : Ordinal.{u}, oV b' ≤ γ → γ < oV g → γ ∉ Cset (psiRes γ) γ a) :
    psi.{u} (oV b') a ∉ Cset (psiRes (oV g)) (oV g) a := by
  have wg : wf3 g := wf3_Gterm wb' hg
  have hle : oV.{u} b' ≤ oV g := by
    rcases olt_total b' g with h | rfl | h
    · exact (oV_order_pres wb' wg h).le
    · exact le_rfl
    · exact absurd h hv
  have heq : psi.{u} (oV b') a = psi (oV g) a := collapse_le (oV g) (oV b') hle H
  exact (psi_notMem_iff_eq hle).2 heq

/-- **The precise remaining collapsing obligation** (replaces the old opaque
`psi_proj` sorry): at a non-`a`-reduced `b'` with an OT3-violator `g ∈ G_a(b')`
(`¬ g <o b'`, so `oV b' ≤ oV g`), the principal value `ψ_a(oV b')` is *not* in
`C_a(oV g)`.  Equivalent (via 1.5 + monotonicity) to `ψ_a(oV b') = ψ_a(oV g)` —
the Buchholz collapse across the critical point.  This is the genuine necessity
core (and is exactly where a non-canonical `b'` defeats the `wf3` necessity
`NEC_of_argExtract`); reduces to interval non-canonicity by
`psi_proj_notmem_of_intervalNoncanon`; still open. -/
theorem psi_proj_notmem (a : ℕ) (b' g : Three) (wb' : wf3 b')
    (hg : g ∈ Gterm a b') (hv : ¬ olt g b') :
    psi.{u} (oV b') a ∉ Cset (psiRes (oV g)) (oV g) a := by
  sorry

/-- **Hard core 1 (Buchholz collapsing):** `proj` preserves the outer `ψ_a`-value.
Assembled from `psi_proj_of_notmem` and the per-step obligation `psi_proj_notmem`. -/
theorem psi_proj (a : ℕ) (b : Three) (wb : wf3 b) :
    psi.{u} (oV (proj a b)) a = psi (oV b) a :=
  psi_proj_of_notmem a (psi_proj_notmem a) b wb

/-! ### Reduction of `oV_nf_order_pres` to its two genuine standardness cores

The `wf3`-route value-order proof `oV_order_pres` splits `olt` into three
branches (subscript `a<e`, argument `a=e, b<f`, tail `a=e,b=f,c<g`).  On `NF`
that proof does **not** port, because each branch needs a `wf3` fact that is
*false* on `NF`: the subscript branch needs `spinesub_le` (the row-1 spine
bound — false on `NF`, 15745 violations at closure+8), and the argument branch
needs the C-membership `oV b ∈ C_a(oV b)` (false on `NF`, 10185 violations even
when the resulting `ψ`-inequality is true).  So a direct port is blocked.

Two structural `NF` facts repair the split:

* `NF_lead0`: every `NF` term's outer subscript is `0`.  Hence comparing two
  `NF` terms, the **subscript branch cannot occur at the top** (`0 < 0` is
  absurd) — it is eliminated unconditionally.
* The remaining argument and tail branches are isolated as the two cores below.

The tail branch is discharged by `tsize`-strong-induction inside
`oV_nf_order_pres` itself, using tail-`NF`-closure `NF_tail` (the *tail* is again
an `NF` term, verified hereditarily); the argument-branch core
`oV_nf_arg_lt` is the genuine UBI/row-1 content (C-membership-free, see the
design notes — collapse is excluded by `r1ok`, the dual of `psi_proj_notmem`). -/

/-! ### The argument-branch head, via the collapsing core `psi_proj`

The direct C-membership routes for `ψ_0(oV b) < ψ_0(oV f)` are all **blocked on
`NF`** (kernel-verified on the minimal example `b = p₁(p₂0)`, `f = p₁(p₂(p₃0))`):

* `psi_strict_mono_arg` needs `oV b ∈ C_0(oV b)` — false (the inner `ψ₂0` lies
  in the band `[Ω₂,Ω₃)` above `oV b ∈ [Ω₁,Ω₂)`, so `oV b ∉ C_0(oV b)`);
* `psi_strict_mono_mem` needs `oV b ∈ C_0(oV f)` — also false: by `M1`
  (`psi_form_of_mem`) + `Cset_level_mono` + `psi_arg_lt_of_mem` membership would
  force `oV(p₂0) < oV f`, but band-disjointness gives `oV f < oV(p₂0)`.

The repair is to route through the **collapsing core** `psi_proj`: `proj 0 b` is
`0`-reduced (`proj_G`), so its value sits in its **own** `C_0` (`proj_oV_mem_C`,
already proven), and `psi_proj` identifies `ψ_0(oV(proj 0 b)) = ψ_0(oV b)`.  Then
Buchholz strict monotonicity `psi_strict_mono_arg` applies at `proj 0 b`.  Thus
the argument head reduces to the **proj-side value order**
`oV(proj 0 b) < oV(proj 0 f)` — and to `psi_proj` itself.  This pins the precise
dependency: **the argument core needs the collapsing core** (the two are the two
faces of the same Buchholz content, as the memory note warned). -/

/-- The argument-branch head `ψ_0(oV b) < ψ_0(oV f)`, reduced (via the proven
`psi_proj` glue and `proj_oV_mem_C`) to the proj-side value order
`oV(proj 0 b) < oV(proj 0 f)`.  C-membership-free at `b` itself; the C-membership
is supplied at the `0`-reduced fixpoint `proj 0 b` where it is *true*
(`proj_oV_mem_C`).  NB: the proj-side hypothesis needs `proj`-monotonicity, which
is **false** on `wf3` (a dead static-domain family); kept only as a fallback. -/
theorem psi0_lt_of_proj_lt {b f : Three} (wb : wf3 b) (wf : wf3 f)
    (hproj_lt : oV.{u} (proj 0 b) < oV (proj 0 f)) :
    psi.{u} (oV b) 0 < psi (oV f) 0 := by
  rw [← psi_proj 0 b wb, ← psi_proj 0 f wf]
  exact psi_strict_mono_arg hproj_lt (proj_oV_mem_C 0 b wb)

/-- **The clean sufficiency reduction (new main axis).**  The argument head
`ψ_0(β₀) < ψ_0(α)` follows from a single `0`-canonical ordinal `γ` in the gap
`[β₀, α)` — *no* `psi_proj`, *no* `proj`-monotonicity.  Proof: `γ ∈ C_0(γ) ⊆
C_0(α)` (`CC_mono`, since `γ ≤ α`); `psi_strict_mono_mem` gives `ψ_0(γ) < ψ_0(α)`;
`psi_mono_arg` gives `ψ_0(β₀) ≤ ψ_0(γ)`.  This isolates the whole argument-head
content to the **existence of an in-gap `0`-canonical witness** — the sufficiency
side of the Buchholz collapse. -/
theorem psi0_lt_of_canon_between {β₀ γ α : Ordinal.{u}}
    (hγc : γ ∈ Cset (psiRes γ) γ 0) (hbγ : β₀ ≤ γ) (hγα : γ < α) :
    psi.{u} β₀ 0 < psi α 0 :=
  lt_of_le_of_lt (psi_mono_arg hbγ 0)
    (psi_strict_mono_mem (CC_mono hγα.le 0 hγc) hγα)

/-- The argument head specialised to term values: `ψ_0(oV b) < ψ_0(oV f)` from an
in-gap `0`-canonical witness `γ ∈ [oV b, oV f)`.  This is the crux interface for
`oV_nf_arg_lt`: the remaining obligation is to **construct** such a `γ` from the
`NF`/UBI/r1ok structure of `b, f`. -/
theorem psi0_oV_lt_of_canon_between {b f : Three} {γ : Ordinal.{u}}
    (hγc : γ ∈ Cset (psiRes γ) γ 0) (hbγ : oV b ≤ γ) (hγf : γ < oV f) :
    psi.{u} (oV b) 0 < psi (oV f) 0 :=
  psi0_lt_of_canon_between hγc hbγ hγf

/-- **Witness existence ⟺ non-collapse** (the converse direction, via
`collapse_le`'s contrapositive).  If `ψ_a` is *not* constant on `[α, β]` then the
gap `[α, β)` contains an `a`-canonical ordinal.  Combined with
`psi0_lt_of_canon_between`, this shows the in-gap canonical witness is **equivalent
to** the strict inequality `ψ_a α < ψ_a β` (given `α ≤ β`, `psi_mono_arg` makes
non-equality and strictness coincide).  So the witness search is neither easier
nor harder than the head itself; the true content is **non-collapse on `NF`**. -/
theorem canon_witness_of_psi_ne {a : ℕ} {α β : Ordinal.{u}} (hαβ : α ≤ β)
    (hne : psi α a ≠ psi β a) :
    ∃ γ, α ≤ γ ∧ γ < β ∧ γ ∈ Cset (psiRes γ) γ a := by
  by_contra hno
  push Not at hno
  exact hne (collapse_le β α hαβ (fun γ hγα hγβ => hno γ hγα hγβ))

/-- **The argument head ⟺ non-collapse.**  Given `oV b ≤ oV f`, the strict
inequality `ψ_0(oV b) < ψ_0(oV f)` holds **iff** `ψ_0(oV b) ≠ ψ_0(oV f)`
(`psi_mono_arg` upgrades `≤` + `≠` to `<`).  So the entire argument-head content
on `NF` is the single fact: *standardness excludes the `ψ_0`-plateau between
`oV b` and `oV f`* — the dual of the collapsing obligation `psi_proj_notmem`. -/
theorem psi0_oV_lt_iff_ne {b f : Three} (hle : oV.{u} b ≤ oV f) :
    psi.{u} (oV b) 0 < psi (oV f) 0 ↔ psi.{u} (oV b) 0 ≠ psi.{u} (oV f) 0 := by
  constructor
  · exact fun h => ne_of_lt h
  · exact fun hne => lt_of_le_of_ne (psi_mono_arg hle 0) hne

/-! ### Why the argument head needs `proj` (the three routes, all kernel-checked)

The argument head `ψ_0(oV b) < ψ_0(oV f)` (`olt b f`, both `NF` arguments) has
exactly three candidate routes, and on the minimal example `b=p₁(p₂0)`,
`f=p₁(p₂(p₃0))` we settled all three in kernel:

1. **Sufficiency witness** (`psi0_lt_of_canon_between`): a `0`-canonical `γ ∈
   [oV b, oV f)`.  But `canon_witness_of_psi_ne` shows the witness exists **iff**
   the head is strict (`collapse_le` converse) — so the witness search is the
   head, not a cheaper lever.  No shortcut.

2. **Direct C-membership** (`psi_strict_mono_arg`/`psi_strict_mono_mem`): needs
   `oV b ∈ C_0(oV b)` or `oV b ∈ C_0(oV f)`.  **Both false** (kernel: the inner
   `ψ₂0 ∈ [Ω₂,Ω₃)` sits above `oV b ∈ [Ω₁,Ω₂)` — a *subscript ascent*, which
   `NF` arguments structurally contain).  `nrm` does not help (it leaves
   `b=p₁(p₂0)` unchanged).

3. **`proj` route** (`psi0_lt_of_proj_lt`): `proj 0` *collapses the subscript
   ascent* — kernel `#eval`: `proj 0 b = p₂0`, `proj 0 f = p₃0`, and
   `olt (proj 0 b) (proj 0 f)`.  This is the **only** working route.  It needs
   (i) `psi_proj` (the collapsing core), (ii) the proj-side order
   `olt (proj 0 b) (proj 0 f)`, (iii) `wf3 (proj 0 b)`.

So the argument core is **inseparable from the collapsing core** `psi_proj`.
The remaining genuine content is the proj-side order — `proj 0`-monotonicity,
which is **false on general `wf3`** (7291 reversals) but **true on `NF`
arguments** (audited: 79800/79800, zero reversals) — a real structural fact of
standardness, not a static anchor. -/

/-- The argument head reduced to its working route: `wf3`-ness of `b` and the
proj-side order `olt (proj 0 b) (proj 0 f)`.  Routes through `psi0_lt_of_proj_lt`
(hence through `psi_proj`).  This is the precise residual for the argument head:
**`proj 0`-monotonicity on `NF` arguments**. -/
theorem psi0_oV_lt_of_proj_olt {b f : Three} (wb : wf3 b) (wf : wf3 f)
    (hproj : olt (proj 0 b) (proj 0 f)) :
    psi.{u} (oV b) 0 < psi (oV f) 0 :=
  psi0_lt_of_proj_lt wb wf
    (oV_order_pres (proj_wf3 wb) (proj_wf3 wf) hproj)

/-- **Argument-branch core (genuine UBI / row-1 content).**  At the outer
subscript `0` (forced by `NF_lead0`), a strictly larger argument gives a strictly
larger value.  The head routes through `proj` (the only working route, see
above) — needing `psi_proj`, the proj-side order, and tail control.  Off `NF` it
fails (the `y₂ <o y₁` equal-value counterexample is a non-standard plateau). -/
theorem oV_nf_arg_lt {b c f g : Three}
    (hv : (P 0 b c) ∈ NF) (hu : (P 0 f g) ∈ NF) (harg : olt b f) :
    oV.{u} (P 0 b c) < oV (P 0 f g) := by
  sorry

/-- Every `ST_PS` list is non-empty (the diagonals have length `v+1`; `oper`
preserves non-emptiness via `oper_eq_dropLast_append`). -/
theorem stps_len_pos {M : PairSeq} (hM : ST_PS M) : 0 < M.length := by
  induction hM with
  | diag v => rw [diagSeq_cons (Nat.zero_le v)]; simp
  | @oper N n hN hn ih =>
    by_cases L : 1 < N.length
    · obtain ⟨R, hR, -⟩ := oper_eq_dropLast_append L hn
      rw [hR, List.length_append, List.length_dropLast]; omega
    · rw [oper_eq_self_short n (by omega)]; exact ih

/-- Every `ST_PS` list begins with `(0,0)`: the diagonals start at `(0,0)`, and
`oper` preserves the head (`N⟦n⟧ = N.dropLast ++ R` keeps `N`'s first column when
`1 < |N|`).  So for `ST_PS (p :: rest)` the `dropWhile`-threshold is `p.1 = 0`. -/
theorem stps_head {M : PairSeq} (hM : ST_PS M) : M.headD (0,0) = (0,0) := by
  induction hM with
  | diag v => rw [diagSeq_cons (Nat.zero_le v)]; rfl
  | @oper N n hN hn ih =>
    by_cases L : 1 < N.length
    · obtain ⟨R, hR, -⟩ := oper_eq_dropLast_append L hn
      rw [hR]
      match N, L with
      | a :: b :: u, _ =>
        simp only [List.dropLast_cons_cons, List.cons_append, List.headD_cons]
        simpa using ih
    · rw [oper_eq_self_short n (by omega)]; exact ih

/-- The dropWhile-tail of a base diagonal `(0,0) :: diagSeq 1 v` is empty: every
non-leading column has row-0 `≥ 1 > 0`, so `dropWhile (0 < ·.1)` drops them all. -/
theorem suffix_diag (v : ℕ) :
    (diagSeq 1 v).dropWhile (fun q => (0 : ℕ) < q.1) = [] := by
  rw [List.dropWhile_eq_nil_iff]
  intro x hx
  have := fst_in_diagSeq hx
  simp only [decide_eq_true_eq]; omega

/-! ### `oper`-prefix-commute: suffix-invariance of the parent relations

To prove `oper (A ++ T) n = A ++ oper T n` (when the operative last block lies in
`T` and `T` is root-anchored) we need the parent-relation machinery
(`entry`/`nextrel0`/`nextrel1`/`le0`/`idx1`/`hasParent`/`parent`) evaluated at
indices `≥ |A|` to be unaffected by the prefix `A`.  These are concrete unfolding
lemmas on the relation defs. -/

/-- `getD` reads the right summand on out-of-`A` indices. -/
theorem getD_app_right (A T : PairSeq) {i : ℕ} (h : A.length ≤ i) :
    (A ++ T).getD i (0,0) = T.getD (i - A.length) (0,0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right h]

/-- `entry` is suffix-invariant: `entry (A ++ T) i (|A| + j) = entry T i j`. -/
theorem entry_append_right (A T : PairSeq) (i j : ℕ) :
    entry (A ++ T) i (A.length + j) = entry T i j := by
  unfold entry; rw [getD_app_right A T (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- `nextrel0` is suffix-invariant on shifted indices (the valley between
`|A|+j0` and `|A|+j1` only sees `T`-indices). -/
theorem nextrel0_append_right (A T : PairSeq) (j0 j1 : ℕ) :
    nextrel0 (A ++ T) (A.length + j0) (A.length + j1) ↔ nextrel0 T j0 j1 := by
  unfold nextrel0; rw [List.length_append]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    rw [entry_append_right, entry_append_right] at h4
    refine ⟨by omega, by omega, by omega, h4, ?_⟩
    intro j hj
    have := h5 (A.length + j) (by omega); rwa [entry_append_right, entry_append_right] at this
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨by omega, by omega, by omega,
      by rw [entry_append_right, entry_append_right]; exact h4, ?_⟩
    intro j hj
    obtain ⟨j', rfl⟩ : ∃ j', j = A.length + j' := ⟨j - A.length, by omega⟩
    rw [entry_append_right, entry_append_right]; exact h5 j' (by omega)

/-- `nextrel0`-reachability lifts from `T` to `A ++ T` on shifted indices. -/
theorem rtg_nextrel0_lift (A T : PairSeq) {j0 c : ℕ}
    (h : Relation.ReflTransGen (nextrel0 T) j0 c) :
    Relation.ReflTransGen (nextrel0 (A ++ T)) (A.length + j0) (A.length + c) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hbc hcd ih =>
    exact Relation.ReflTransGen.tail ih ((nextrel0_append_right A T b c).2 hcd)

/-- `le0` lifts from `T` to `A ++ T` on shifted indices (forward direction). -/
theorem le0_append_right_of (A T : PairSeq) {j0 j1 : ℕ} (h : le0 T j0 j1) :
    le0 (A ++ T) (A.length + j0) (A.length + j1) := by
  obtain ⟨hb0, hb1, hrt⟩ := h
  exact ⟨by rw [List.length_append]; omega, by rw [List.length_append]; omega,
    rtg_nextrel0_lift A T hrt⟩

/-- `nextrel0` strictly increases the index. -/
theorem nextrel0_lt {M : PairSeq} {a b : ℕ} (h : nextrel0 M a b) : a < b := h.2.2.1

/-- A `nextrel0`-reachability chain never decreases the index. -/
theorem rtg_nextrel0_ge {M : PairSeq} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 M) a b) : a ≤ b := by
  induction h with
  | refl => exact le_refl _
  | @tail c d hcd hde ih => exact le_of_lt (lt_of_le_of_lt ih (nextrel0_lt hde))

/-- A `nextrel0`-reachability chain in `A ++ T` starting at a shifted index
`|A| + a` stays within `T` (each step increases the index from `≥ |A|`), so it
mirrors a chain in `T`. -/
theorem rtg_nextrel0_unlift (A T : PairSeq) {a c : ℕ}
    (h : Relation.ReflTransGen (nextrel0 (A ++ T)) (A.length + a) c) :
    ∃ c', c = A.length + c' ∧ Relation.ReflTransGen (nextrel0 T) a c' := by
  induction h with
  | refl => exact ⟨a, rfl, Relation.ReflTransGen.refl⟩
  | @tail d e hde hef ih =>
    obtain ⟨d', rfl, ihd⟩ := ih
    have hge : A.length ≤ e :=
      le_of_lt (lt_of_le_of_lt (Nat.le_add_right _ _) (nextrel0_lt hef))
    obtain ⟨e', rfl⟩ : ∃ e', e = A.length + e' := ⟨e - A.length, by omega⟩
    exact ⟨e', rfl, Relation.ReflTransGen.tail ihd ((nextrel0_append_right A T d' e').1 hef)⟩

/-- `le0` is suffix-invariant on shifted indices: forward by `le0_append_right_of`,
backward because the chain stays in `T` (`rtg_nextrel0_unlift`). -/
theorem le0_append_right (A T : PairSeq) (j0 j1 : ℕ) :
    le0 (A ++ T) (A.length + j0) (A.length + j1) ↔ le0 T j0 j1 := by
  constructor
  · rintro ⟨hb0, hb1, hrt⟩
    rw [List.length_append] at hb0 hb1
    obtain ⟨c', hc', hrtT⟩ := rtg_nextrel0_unlift A T hrt
    have hjc : j1 = c' := by omega
    subst hjc
    exact ⟨by omega, by omega, hrtT⟩
  · exact le0_append_right_of A T

/-- `nextrel0` blocking: with `T` root-anchored (`entry T 0 0 = 0`) no `nextrel0`
edge crosses from a prefix index `k < |A|` into a positive-row-0 column at index
`j ≥ |A|` (the root at `|A|` violates the valley). -/
theorem nextrel0_no_cross (A T : PairSeq) (hroot : entry T 0 0 = 0)
    {k j : ℕ} (hk : k < A.length) (hj : A.length ≤ j)
    (hpos : 0 < entry (A ++ T) 0 j) (hne : nextrel0 (A ++ T) k j) : False := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hne
  have hjne : A.length < j := by
    rcases Nat.lt_or_ge A.length j with h | h
    · exact h
    · -- A.length = j, but entry j > 0 and entry (A.length) = root = 0
      have : j = A.length := by omega
      subst this
      have hz : entry (A ++ T) 0 A.length = 0 := by
        have := entry_append_right A T 0 0; rw [Nat.add_zero] at this; rw [this, hroot]
      omega
  have hval := h5 A.length ⟨by omega, hjne⟩
  have hz : entry (A ++ T) 0 A.length = 0 := by
    have := entry_append_right A T 0 0; rw [Nat.add_zero] at this; rw [this, hroot]
  rw [hz] at hval; omega

/-- A row-0-`0` column has no `nextrel0`-predecessor (`nextrel0` needs a strict
row-0 increase into it). -/
theorem nextrel0_no_pred_zero {M : PairSeq} {a b : ℕ} (hz : entry M 0 b = 0)
    (h : nextrel0 M a b) : False := by
  obtain ⟨_, _, _, h4, _⟩ := h; rw [hz] at h4; omega

/-- A `nextrel0`-reachability chain ending at a row-0-`0` column is trivial
(`refl`): the root has no predecessor. -/
theorem rtg_to_root {M : PairSeq} {k b : ℕ} (hz : entry M 0 b = 0)
    (h : Relation.ReflTransGen (nextrel0 M) k b) : k = b := by
  cases h with
  | refl => rfl
  | tail _ hlast => exact absurd hlast (fun hh => nextrel0_no_pred_zero hz hh)

/-- **`le0` blocking** (the key cross-boundary fact): with `T` root-anchored, no
`le0`-chain crosses from a prefix index `k < |A|` into a positive-row-0 column at
index `|A| + j1`.  Induction on the chain: each step into a positive column has
its source `≥ |A|` (`nextrel0_no_cross`); a root source would have no predecessor
(`rtg_to_root`), forcing `k` itself `≥ |A|`. -/
theorem le0_no_cross (A T : PairSeq) (hroot : entry T 0 0 = 0)
    {k j1 : ℕ} (hk : k < A.length) (hpos : 0 < entry (A ++ T) 0 (A.length + j1))
    (h : le0 (A ++ T) k (A.length + j1)) : False := by
  obtain ⟨-, -, hrt⟩ := h
  suffices H : ∀ e, Relation.ReflTransGen (nextrel0 (A ++ T)) k e →
      A.length ≤ e → 0 < entry (A ++ T) 0 e → A.length ≤ k by
    exact absurd (H _ hrt (by omega) hpos) (by omega)
  intro e hrt'
  induction hrt' with
  | refl => intro he _; exact he
  | @tail c d hcd hde ih =>
    intro hd hpd
    have hcA : A.length ≤ c := by
      by_contra hlt; push_neg at hlt
      exact nextrel0_no_cross A T hroot hlt hd hpd hde
    by_cases hcpos : 0 < entry (A ++ T) 0 c
    · exact ih hcA hcpos
    · have hcz : entry (A ++ T) 0 c = 0 := by omega
      have hkc : k = c := rtg_to_root hcz hcd
      omega

/-- `nextrel1` is suffix-invariant on shifted indices.  The row-1 valley universal
ranges only over `j > |A| + j0 ≥ |A|` (all in `T`); `le0` is suffix-invariant
(`le0_append_right`). -/
theorem nextrel1_append_right (A T : PairSeq) (j0 j1 : ℕ) :
    nextrel1 (A ++ T) (A.length + j0) (A.length + j1) ↔ nextrel1 T j0 j1 := by
  unfold nextrel1
  rw [List.length_append]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    rw [entry_append_right, entry_append_right] at h4
    rw [le0_append_right] at h5
    refine ⟨by omega, by omega, by omega, h4, h5, ?_⟩
    intro j hj
    obtain ⟨hj1, hj2⟩ := hj
    -- forward: T-valley.  apply M-valley h6 at shifted index |A|+j
    have := h6 (A.length + j) ⟨by omega, (le0_append_right A T j j1).2 hj2⟩
    rwa [entry_append_right, entry_append_right] at this
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨by omega, by omega, by omega,
      by rw [entry_append_right, entry_append_right]; exact h4,
      (le0_append_right A T j0 j1).2 h5, ?_⟩
    intro j hj
    obtain ⟨hj1, hj2⟩ := hj
    -- backward: M-valley.  j > |A|+j0 ≥ |A|, so j = |A|+j' in T
    obtain ⟨j', rfl⟩ : ∃ j', j = A.length + j' := ⟨j - A.length, by omega⟩
    rw [le0_append_right] at hj2
    have := h6 j' ⟨by omega, hj2⟩
    rwa [entry_append_right, entry_append_right]

/-- `nextR` (row-indexed) is suffix-invariant on shifted indices. -/
theorem nextR_append_right (A T : PairSeq) (i j0 j1 : ℕ) :
    nextR (A ++ T) i (A.length + j0) (A.length + j1) ↔ nextR T i j0 j1 := by
  unfold nextR
  by_cases hi : i = 0
  · rw [if_pos hi, if_pos hi]; exact nextrel0_append_right A T j0 j1
  · rw [if_neg hi, if_neg hi]; exact nextrel1_append_right A T j0 j1

/-- `idx1` is suffix-invariant on shifted indices (it only reads the column). -/
theorem idx1_append_right (A T : PairSeq) (j : ℕ) :
    idx1 (A ++ T) (A.length + j) = idx1 T j := by
  unfold idx1; rw [entry_append_right]

/-- A `nextR` edge gives `le0` to its target. -/
theorem nextR_le0 {M : PairSeq} {i k b : ℕ} (h : nextR M i k b) : le0 M k b := by
  unfold nextR at h
  by_cases hi : i = 0
  · rw [if_pos hi] at h; exact ⟨h.1, h.2.1, Relation.ReflTransGen.single h⟩
  · rw [if_neg hi] at h; exact h.2.2.2.2.1

/-- A `nextR`-source of a positive-row-0 column at index `|A| + j1` is in `T`
(via `le0_no_cross`). -/
theorem nextR_src_in_T (A T : PairSeq) (hroot : entry T 0 0 = 0)
    {i k j1 : ℕ} (hpos : 0 < entry (A ++ T) 0 (A.length + j1))
    (h : nextR (A ++ T) i k (A.length + j1)) : A.length ≤ k := by
  by_contra hlt; push_neg at hlt
  exact le0_no_cross A T hroot hlt hpos (nextR_le0 h)

/-- `hasParent` is suffix-invariant at a positive-row-0 column `|A| + j1` (the
parent lies in `T` by `nextR_src_in_T`; uniqueness transfers via
`nextR_append_right`). -/
theorem hasParent_append_right (A T : PairSeq) (hroot : entry T 0 0 = 0)
    {i j1 : ℕ} (hpos : 0 < entry (A ++ T) 0 (A.length + j1)) :
    hasParent (A ++ T) i (A.length + j1) ↔ hasParent T i j1 := by
  unfold hasParent
  constructor
  · rintro ⟨j0, hj0, huniq⟩
    have hge := nextR_src_in_T A T hroot hpos hj0
    obtain ⟨j0', rfl⟩ : ∃ j0', j0 = A.length + j0' := ⟨j0 - A.length, by omega⟩
    refine ⟨j0', (nextR_append_right A T i j0' j1).1 hj0, ?_⟩
    intro y hy
    have : A.length + y = A.length + j0' :=
      huniq (A.length + y) ((nextR_append_right A T i y j1).2 hy)
    omega
  · rintro ⟨j0', hj0', huniq⟩
    refine ⟨A.length + j0', (nextR_append_right A T i j0' j1).2 hj0', ?_⟩
    intro y hy
    have hge := nextR_src_in_T A T hroot hpos hy
    obtain ⟨y', rfl⟩ : ∃ y', y = A.length + y' := ⟨y - A.length, by omega⟩
    have := huniq y' ((nextR_append_right A T i y' j1).1 hy)
    omega

/-- `parent` shifts by `|A|` at a positive-row-0 column (both `parent (A++T)` and
`|A| + parent T` satisfy the unique `nextR`). -/
theorem parent_append_right (A T : PairSeq) (hroot : entry T 0 0 = 0)
    {i j1 : ℕ} (hpos : 0 < entry (A ++ T) 0 (A.length + j1))
    (hpT : hasParent T i j1) :
    parent (A ++ T) i (A.length + j1) = A.length + parent T i j1 := by
  have hpM : hasParent (A ++ T) i (A.length + j1) :=
    (hasParent_append_right A T hroot hpos).2 hpT
  -- both `parent (A++T)` and `|A| + parent T` satisfy nextR; conclude equal by uniqueness
  exact hpM.unique (parent_nextR hpM)
    ((nextR_append_right A T i (parent T i j1) j1).2 (parent_nextR hpT))

/-- **The combinatorial heart of suffix-closure** (pure `oper`/`dropWhile`, no
`ST_PS`).  For a long list `N` (`1 < |N|`) and `N⟦n⟧ = p :: rest`, the
`dropWhile`-tail of `N⟦n⟧` is one of three shapes, all of which are `[]` or
`oper` of a smaller list (hence `ST_PS` once the inputs are):
  * empty;
  * `(tail N)⟦n⟧` — `oper` operates only on the last top-level block, which lies
    inside the tail, so it commutes with taking the tail (Case A, `tail N ≠ []`);
  * `N⟦n-1⟧` — the `v0 = 0` tiling sub-case, where the `n` copies become fresh
    top-level siblings and the tail is the last `n-1` copies (Case B,
    `tail N = []`).
Empirically exact (`tail(N⟦n⟧) ∈ {[], (tail N)⟦n⟧, N⟦n-1⟧}`, 0/11638; over all
`(N,n)` pairs 0/23444).  This is the genuine forest/hydra sub-recursion content;
left as the single residual feeding `ST_PS_suffix`.

PROOF PATH (the remaining kernel = `oper`-prefix-commute).  Write `N = (0,0) ::
FB ++ T` where `FB = N.tail.takeWhile (0 < ·.1)` (first block interior, all
row-0 `> 0`) and `T = tail N = N.tail.dropWhile (0 < ·.1)` (from the 2nd root).
  * If `T ≠ []`: `oper` touches only the LAST top-level block, which lies in `T`,
    so `oper N n = (0,0) :: FB ++ oper T n` (the COMMUTE — needs `parent`/`idx1`/
    `entry`/`le0` of the last column to be suffix-invariant; the row-0 `= 0`
    root of `T` blocks any `nextrel0`/`le0` edge from `T` back into `FB`).  Then
    `dropWhile (0 < ·.1)` strips `FB` (all row-0 `> 0`) and stops at `oper T n`
    (starts at a row-0 `= 0` root), giving `(tail N)⟦n⟧` — Case A.
  * If `T = []`: `N = (0,0) :: FB` is a single block; the `v0 = 0` tiling makes
    the `n` copies fresh roots, tail `= N⟦n-1⟧` — Case B.
The COMMUTE (`oper (A ++ T) n = A ++ oper T n` when the operative block ⊆ `T`,
`T` root-anchored) is the deep `oper`-structural kernel; equivalently the `R` of
`oper_eq_dropLast_append N` equals that of `oper_eq_dropLast_append (tail N)`
(both are the copies of the shared last block). -/
theorem oper_tail_cases {N : PairSeq} {n : ℕ} (L : 1 < N.length) (hn : 1 ≤ n)
    {p : ℕ × ℕ} {rest : PairSeq} (hL : p :: rest = N⟦n⟧) :
    rest.dropWhile (fun q => p.1 < q.1) = [] ∨
    (∃ q rest', q :: rest' = N ∧
      rest.dropWhile (fun q => p.1 < q.1)
        = (rest'.dropWhile (fun r => q.1 < r.1))⟦n⟧) ∨
    (2 ≤ n ∧ rest.dropWhile (fun q => p.1 < q.1) = N⟦n-1⟧) := by
  sorry

/-- **`ST_PS`-suffix-closure (the single combinatorial residual).**  For an
`ST_PS` list `p :: rest`, the `dropWhile`-tail — the columns from the first
row-0 return to `≤ p.1` onward — is empty or again `ST_PS`.

Audited TRUE (783/783 non-empty suffixes at closure+6; `/tmp/nf_tail2.py`).
The tail is a literal contiguous suffix `M.drop k`.  Proof skeleton (induction on
the `ST_PS` derivation):
* **diag**: tail is empty (`suffix_diag`) — `p = (0,0)`, all others row-0 `≥ 1`.
* **oper, `Pred` branches**: `M⟦n⟧ = Pred M = M.dropLast`; the suffix of a
  `dropLast` is the IH suffix with its last column dropped (or empty).
* **oper, tiling branch** (`oper_bad_blocks`: `M = G ++ (v0,w0)::R ++ [lp]`,
  `M⟦n⟧ = G ++ copies`, `R` all above `v0`): if `v0 > 0` the suffix lives inside
  `G` (IH); if `v0 = 0` the `n` copies become fresh top-level siblings and the
  suffix is `copies 2..n`, an `ST_PS`-shaped object — the Buchholz/hydra
  sub-recursion.  This last sub-case is the genuine open content. -/
theorem ST_PS_suffix {p : ℕ × ℕ} {rest : PairSeq} (hM : ST_PS (p :: rest)) :
    rest.dropWhile (fun q => p.1 < q.1) = [] ∨
    ST_PS (rest.dropWhile (fun q => p.1 < q.1)) := by
  generalize hL : (p :: rest) = M at hM
  induction hM generalizing p rest with
  | diag v =>
    rw [diagSeq_cons (Nat.zero_le v)] at hL
    obtain ⟨rfl, rfl⟩ := List.cons.injEq .. ▸ hL
    exact Or.inl (suffix_diag v)
  | @oper N n hN hn ih =>
    by_cases L : 1 < N.length
    · -- N long: the tail is [], (tail N)⟦n⟧, or N⟦n-1⟧ (oper_tail_cases)
      rcases oper_tail_cases L hn hL with hempty | ⟨q, rest', hN, heq⟩ | ⟨hn2, hNm1⟩
      · exact Or.inl hempty
      · -- (tail N)⟦n⟧: ST_PS via IH (tail N is [] or ST_PS) + oper rule
        rw [heq]
        rcases ih hN with hte | hts
        · -- tail N empty: ([])⟦n⟧ = []  → left disjunct
          left; rw [hte]; unfold oper; simp
        · exact Or.inr (ST_PS.oper hts hn)
      · -- N⟦n-1⟧ with n ≥ 2: ST_PS via oper rule (n-1 ≥ 1)
        exact Or.inr (hNm1 ▸ ST_PS.oper hN (by omega))
    · -- N short: N⟦n⟧ = N
      rw [oper_eq_self_short n (by omega)] at hL
      exact ih hL

/-- **Tail-`NF`-closure.**  Reduced to the pure list-level `ST_PS_suffix`: the
tail `c` of `P 0 b c ∈ NF` is `translate` of the `dropWhile`-tail of the `ST_PS`
preimage, which (when non-empty, i.e. `c ≠ Z`) is again `ST_PS`. -/
theorem NF_tail {b c : Three} (hv : (P 0 b c) ∈ NF) (hc : c ≠ Z) : c ∈ NF := by
  obtain ⟨M, hM, hMt⟩ := hv
  obtain ⟨p, rest, rfl⟩ : ∃ p rest, M = p :: rest := by
    have := stps_len_pos hM
    cases M with
    | nil => simp at this
    | cons p rest => exact ⟨p, rest, rfl⟩
  rw [translate] at hMt
  have hceq : c = translate (rest.dropWhile (fun q => p.1 < q.1)) := by
    injection hMt with _ _ h3; exact h3.symm
  rcases ST_PS_suffix hM with hempty | hstps
  · rw [hempty, translate] at hceq; exact absurd hceq hc
  · exact ⟨_, hstps, by rw [hceq]⟩

/-- **Hard core 2 (standardness / UBI), now reduced.**  On `NF` the
subscript-first order refines the `ψ`-value order.  The subscript branch is
**eliminated** via `NF_lead0` (outer subscript `0`).  The **tail branch is now
folded into this proof's own `tsize` strong induction** (via `NF_tail`, which
yields strictly smaller `NF` operands), so the only genuine residuals are the
argument core `oV_nf_arg_lt` and tail-`NF`-closure `NF_tail`. -/
theorem oV_nf_order_pres {v u : Three} (hv : v ∈ NF) (hu : u ∈ NF)
    (h : olt v u) : oV.{u} v < oV u := by
  generalize hs : tsize v = n
  induction n using Nat.strong_induction_on generalizing v u with
  | _ n IH =>
    subst hs
    cases v with
    | Z =>
      cases u with
      | Z => exact absurd h (olt_irrefl Z)
      | P e f g =>
        have he : e = 0 := NF_lead0 hu rfl
        subst he
        simpa using oV_pos 0 f g
    | P a b c =>
      have ha : a = 0 := NF_lead0 hv rfl
      subst ha
      cases u with
      | Z => exact absurd h (not_olt_Z _)
      | P e f g =>
        have he : e = 0 := NF_lead0 hu rfl
        subst he
        rcases olt_P_P.1 h with hsub | ⟨_, harg⟩ | ⟨_, rfl, htail⟩
        · exact absurd hsub (lt_irrefl 0)
        · exact oV_nf_arg_lt hv hu harg
        · show psi (oV b) 0 + oV c < psi (oV b) 0 + oV g
          refine add_lt_add_right ?_ _
          by_cases hcZ : c = Z
          · subst hcZ
            have hgZ : g ≠ Z := by
              rintro rfl; exact absurd htail (not_olt_Z _)
            obtain ⟨e2, f2, g2, rfl⟩ : ∃ e2 f2 g2, g = P e2 f2 g2 := by
              cases g with
              | Z => exact absurd rfl hgZ
              | P e2 f2 g2 => exact ⟨_, _, _, rfl⟩
            simpa using oV_pos e2 f2 g2
          · have hcNF : c ∈ NF := NF_tail hv hcZ
            have hgZ : g ≠ Z := by
              rintro rfl; exact absurd htail (not_olt_Z _)
            have hgNF : g ∈ NF := NF_tail hu hgZ
            have szc : tsize c < tsize (P 0 b c) := by simp only [tsize]; omega
            exact IH (tsize c) szc hcNF hgNF htail rfl

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
