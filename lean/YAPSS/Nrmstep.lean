/-
**Attack file for `nrm_order_pres` / `nrm_step_dec`** — the independent Lean
campaign on the remaining core (this file is NOT a port of `ord/nrmstep.thy`;
it shares the mathematical skeleton discovered there but is developed
directly in Lean).

Layer 1 (this file, pure — no class assumptions):
  * `maxo_ub`        — `maxo` is an upper bound of its argument list
  * `Gterm_trans`    — the critical-term relation is transitive
  * `proj_ole`       — projection is inflationary (`b ≤o proj u b`)
  * `proj_fire`      — **one-step theorem**: the maximal critical term has no
    violator of its own, so `proj` terminates after a single rewrite;
    `proj u b` is either `b` (no fire) or `maxo` of the violators (fire)
  * fire corollaries — `proj_mem_of_fire`, `olt_proj_of_fire`,
    `proj_ub_of_fire`
  * `ins_olt_mono`   — sum insertion is *unconditionally* strictly monotone
    in the tail (absorption needs no side condition: absorb-left implies
    absorb-right via `absorb_mono`)

These give the downstream case analyses the clean shape
`proj u b = if fire then max-violator else b`.
-/
import YAPSS.Nrm
import YAPSS.Seqlex

namespace YAPSS

open Three

/-! ## `maxo` is an upper bound -/

theorem maxo_ub {x : Three} {ys : List Three} : ∀ y ∈ x :: ys, y ≤o maxo x ys := by
  induction ys generalizing x with
  | nil =>
    intro y hy
    rcases List.mem_singleton.1 hy with rfl
    exact Or.inr rfl
  | cons z zs ih =>
    intro y hy
    rw [maxo_cons]
    by_cases h : olt x z
    · rw [if_pos h]
      rcases List.mem_cons.1 hy with rfl | hy'
      · exact ole_trans (Or.inl h) (ih z (List.mem_cons_self ..))
      · exact ih y hy'
    · rw [if_neg h]
      rcases List.mem_cons.1 hy with rfl | hy'
      · exact ih y (List.mem_cons_self ..)
      · rcases List.mem_cons.1 hy' with rfl | hy''
        · have hyx : y ≤o x := by
            rcases olt_total y x with h1 | h1 | h1
            · exact Or.inl h1
            · exact Or.inr h1
            · exact absurd h1 h
          exact ole_trans hyx (ih x (List.mem_cons_self ..))
        · exact ih y (List.mem_cons_of_mem _ hy'')

theorem maxo_ub_mem {gs : List Three} (h : gs ≠ []) :
    ∀ y ∈ gs, y ≤o maxo gs.headI gs.tail := by
  cases gs with
  | nil => exact absurd rfl h
  | cons g gs =>
    intro y hy
    simpa using maxo_ub y (by simpa using hy)

/-! ## Transitivity of the critical-term relation -/

theorem Gterm_trans {u : ℕ} {x g t : Three} (hx : x ∈ Gterm u g)
    (hg : g ∈ Gterm u t) : x ∈ Gterm u t := by
  induction t with
  | Z => simp at hg
  | P a b c ihb ihc =>
    rcases mem_Gterm_P.1 hg with ⟨ha, rfl | hgb⟩ | hgc
    · exact mem_Gterm_P.2 (Or.inl ⟨ha, Or.inr hx⟩)
    · exact mem_Gterm_P.2 (Or.inl ⟨ha, Or.inr (ihb hgb)⟩)
    · exact mem_Gterm_P.2 (Or.inr (ihc hgc))

/-! ## Projection is inflationary -/

/-- Members of the violator list are critical terms of `b`. -/
theorem mem_filter_Gterm {u : ℕ} {b g : Three}
    (h : g ∈ (Glist u b).filter (fun g => ¬ olt g b)) : g ∈ Gterm u b :=
  mem_Glist.1 (List.mem_of_mem_filter h)

/-- Members of the violator list do not lie below `b`. -/
theorem mem_filter_not_olt {u : ℕ} {b g : Three}
    (h : g ∈ (Glist u b).filter (fun g => ¬ olt g b)) : ¬ g <o b := by
  have := List.of_mem_filter h
  simpa using this

theorem proj_ole (u : ℕ) (b : Three) : b ≤o proj u b := by
  generalize hs : tsize b = n
  induction n using Nat.strong_induction_on generalizing b with
  | _ n IH =>
    subst hs
    by_cases h : (Glist u b).filter (fun g => ¬ olt g b) = []
    · rw [proj_id h]
      exact Or.inr rfl
    · rw [proj_rec h]
      have hin := maxo_hdtl_in h
      have hG : maxo ((Glist u b).filter (fun g => ¬ olt g b)).headI
          ((Glist u b).filter (fun g => ¬ olt g b)).tail ∈ Gterm u b :=
        mem_filter_Gterm hin
      have hble : b ≤o maxo ((Glist u b).filter (fun g => ¬ olt g b)).headI
          ((Glist u b).filter (fun g => ¬ olt g b)).tail := by
        rcases olt_total b _ with h1 | h1 | h1
        · exact Or.inl h1
        · exact Or.inr h1
        · exact absurd h1 (mem_filter_not_olt hin)
      exact ole_trans hble (IH (tsize _) (Gterm_tsize hG) _ rfl)

/-! ## The one-step theorem -/

/-- **`proj` fires at most once.**  The maximal violator `m` has no violator
of its own: any `g' ∈ G_u m` with `¬ g' <o m` would lift to a violator of `b`
(by `Gterm_trans` and `b ≤o m ≤o g'`), hence `g' ≤o m` by maximality, hence
`g' = m`, contradicting the size decrease along `Gterm`. -/
theorem proj_fire {u : ℕ} {b : Three}
    (h : (Glist u b).filter (fun g => ¬ olt g b) ≠ []) :
    proj u b = maxo ((Glist u b).filter (fun g => ¬ olt g b)).headI
                    ((Glist u b).filter (fun g => ¬ olt g b)).tail := by
  rw [proj_rec h]
  set m := maxo ((Glist u b).filter (fun g => ¬ olt g b)).headI
               ((Glist u b).filter (fun g => ¬ olt g b)).tail with hm
  have hin : m ∈ (Glist u b).filter (fun g => ¬ olt g b) := maxo_hdtl_in h
  have hmG : m ∈ Gterm u b := mem_filter_Gterm hin
  have hbm : b ≤o m := by
    rcases olt_total b m with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd h1 (mem_filter_not_olt hin)
  apply proj_id
  by_contra hne
  obtain ⟨g', hg'⟩ := List.exists_mem_of_ne_nil _ hne
  have hg'G : g' ∈ Gterm u m := mem_Glist.1 (List.mem_of_mem_filter hg')
  have hg'm : ¬ g' <o m := by
    have := List.of_mem_filter hg'
    simpa using this
  have hg'b : g' ∈ Gterm u b := Gterm_trans hg'G hmG
  have hmg' : m ≤o g' := by
    rcases olt_total m g' with h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd h1 hg'm
  have hg'nb : ¬ g' <o b := by
    intro hlt
    rcases ole_trans hbm hmg' with h1 | h1
    · exact olt_irrefl _ (olt_trans hlt h1)
    · rw [h1] at hlt
      exact olt_irrefl _ (olt_trans hlt (h1 ▸ hlt))
  have hg'mem : g' ∈ (Glist u b).filter (fun g => ¬ olt g b) :=
    List.mem_filter.2 ⟨mem_Glist.2 hg'b, by simpa using hg'nb⟩
  have : g' ≤o m := maxo_ub_mem h g' hg'mem
  have hg'eq : g' = m := by
    rcases this with h1 | h1
    · exact absurd h1 hg'm
    · exact h1
  have := Gterm_tsize hg'G
  rw [hg'eq] at this
  exact lt_irrefl _ this

/-- Under fire, the projection is a critical term of `b`. -/
theorem proj_mem_of_fire {u : ℕ} {b : Three}
    (h : (Glist u b).filter (fun g => ¬ olt g b) ≠ []) :
    proj u b ∈ Gterm u b := by
  rw [proj_fire h]
  exact mem_filter_Gterm (maxo_hdtl_in h)

/-- Under fire, the projection strictly increases. -/
theorem olt_proj_of_fire {u : ℕ} {b : Three}
    (h : (Glist u b).filter (fun g => ¬ olt g b) ≠ []) :
    b <o proj u b := by
  have hmem := proj_mem_of_fire h
  have hne : proj u b ≠ b := by
    intro he
    have := Gterm_tsize hmem
    rw [he] at this
    exact lt_irrefl _ this
  rcases olt_total b (proj u b) with h1 | h1 | h1
  · exact h1
  · exact absurd h1.symm hne
  · rw [proj_fire h] at h1 ⊢
    exact absurd h1 (mem_filter_not_olt (maxo_hdtl_in h))

/-- Under fire, the projection dominates every violator. -/
theorem proj_ub_of_fire {u : ℕ} {b : Three}
    (h : (Glist u b).filter (fun g => ¬ olt g b) ≠ [])
    {g : Three} (hg : g ∈ Gterm u b) (hng : ¬ g <o b) : g ≤o proj u b := by
  rw [proj_fire h]
  exact maxo_ub_mem h g (List.mem_filter.2 ⟨mem_Glist.2 hg, by simpa using hng⟩)

/-! ## The firing predicate and projection submonotonicity -/

/-- `pfire u b`: `b` has a critical term not below itself, so `proj` rewrites. -/
def pfire (u : ℕ) (b : Three) : Prop :=
  (Glist u b).filter (fun g => ¬ olt g b) ≠ []

theorem pfire_iff {u : ℕ} {b : Three} :
    pfire u b ↔ ∃ g ∈ Gterm u b, ¬ g <o b := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := List.exists_mem_of_ne_nil _ h
    exact ⟨g, mem_filter_Gterm hg, mem_filter_not_olt hg⟩
  · rintro ⟨g, hG, hng⟩ he
    have hmem : g ∈ (Glist u b).filter (fun g => ¬ olt g b) :=
      List.mem_filter.2 ⟨mem_Glist.2 hG, by simpa using hng⟩
    rw [he] at hmem
    simp at hmem

theorem proj_nofire {u : ℕ} {b : Three} (h : ¬ pfire u b) : proj u b = b :=
  proj_id (not_not.1 h)

theorem olt_ole_trans {x y z : Three} (h1 : x <o y) (h2 : y ≤o z) : x <o z := by
  rcases h2 with h2 | rfl
  · exact olt_trans h1 h2
  · exact h1

/-- **Projection submonotonicity**: if the critical set of `x` is contained in
that of `y`, `x ≤o y`, and firing transports from `x` to `y`, then the
projections compare.  With `proj_fire` this is almost immediate: either the
fired value of `x` drops below `y` (then inflation of `y` finishes), or it is
itself a violator of `y` and the max-choice dominates it. -/
theorem proj_submono {u : ℕ} {x y : Three}
    (sub : Gterm u x ⊆ Gterm u y) (xy : x ≤o y)
    (fp : pfire u x → pfire u y) :
    proj u x ≤o proj u y := by
  by_cases hx : pfire u x
  · by_cases holt : proj u x <o y
    · exact Or.inl (olt_ole_trans holt (proj_ole u y))
    · exact proj_ub_of_fire (fp hx) (sub (proj_mem_of_fire hx)) holt
  · rw [proj_nofire hx]
    exact ole_trans xy (proj_ole u y)

/-! ## Unconditional strict monotonicity of `ins` in the tail -/

/-- Absorb-left implies absorb-right along `<o`: if the head of `t` already
absorbs `(a, b)` and `t <o t'`, then the head of `t'` absorbs it too. -/
theorem absorb_mono {a e e' : ℕ} {b f f' g g' : Three}
    (habs : a < e ∨ (a = e ∧ b <o f)) (h : P e f g <o P e' f' g') :
    a < e' ∨ (a = e' ∧ b <o f') := by
  rcases olt_P_P.1 h with h2 | ⟨rfl, h2⟩ | ⟨rfl, rfl, h2⟩
  · rcases habs with h1 | ⟨rfl, h1⟩
    · exact Or.inl (h1.trans h2)
    · exact Or.inl h2
  · rcases habs with h1 | ⟨rfl, h1⟩
    · exact Or.inl h1
    · exact Or.inr ⟨rfl, olt_trans h1 h2⟩
  · exact habs

/-- **`ins` is strictly monotone in the tail, with no side condition.**
If absorption fires on the left it fires on the right (`absorb_mono`); if it
fires only on the right, the right head already dominates `(a, b)`; if on
neither, the comparison descends to the tails. -/
theorem ins_olt_mono {a : ℕ} {b t t' : Three} (h : t <o t') :
    ins a b t <o ins a b t' := by
  cases t with
  | Z =>
    cases t' with
    | Z => exact absurd h olt_Z_Z
    | P e f g =>
      rw [ins_Z, ins_P]
      by_cases habs : a < e ∨ (a = e ∧ b <o f)
      · rw [if_pos habs]
        rcases habs with h1 | ⟨rfl, h2⟩
        · exact olt_P_P.2 (Or.inl h1)
        · exact olt_P_P.2 (Or.inr (Or.inl ⟨rfl, h2⟩))
      · rw [if_neg habs]
        exact olt_P_P.2 (Or.inr (Or.inr ⟨rfl, rfl, by simp⟩))
  | P e f g =>
    cases t' with
    | Z => exact absurd h (not_olt_Z _)
    | P e' f' g' =>
      rw [ins_P, ins_P]
      by_cases h1 : a < e ∨ (a = e ∧ b <o f)
      · rw [if_pos h1, if_pos (absorb_mono h1 h)]
        exact h
      · rw [if_neg h1]
        by_cases h2 : a < e' ∨ (a = e' ∧ b <o f')
        · rw [if_pos h2]
          rcases h2 with h3 | ⟨rfl, h3⟩
          · exact olt_P_P.2 (Or.inl h3)
          · exact olt_P_P.2 (Or.inr (Or.inl ⟨rfl, h3⟩))
        · rw [if_neg h2]
          exact olt_P_P.2 (Or.inr (Or.inr ⟨rfl, rfl, h⟩))

/-! ## One-position increase relations

`lext`: one leaf inserted at a `Z`-position (deepest tail end or empty
argument).  `lflip`: one leaf's subscript incremented.  `einc`/`eflip` are
the *end-position* restrictions: along tails to the last summand, then (only
when the tail is already `Z`) into its argument.  These are the shapes
actually produced by appending one column to a standard segment. -/

inductive lext : Three → Three → Prop
  | end_ (w : ℕ) : lext Z (P w Z Z)
  | tail {c c' : Three} (a : ℕ) (b : Three) : lext c c' → lext (P a b c) (P a b c')
  | arg {b b' : Three} (a : ℕ) (c : Three) : lext b b' → lext (P a b c) (P a b' c)

inductive lflip : Three → Three → Prop
  | leaf {w w' : ℕ} : w < w' → lflip (P w Z Z) (P w' Z Z)
  | tail {c c' : Three} (a : ℕ) (b : Three) : lflip c c' → lflip (P a b c) (P a b c')
  | arg {b b' : Three} (a : ℕ) (c : Three) : lflip b b' → lflip (P a b c) (P a b' c)

inductive einc : Three → Three → Prop
  | end_ (w : ℕ) : einc Z (P w Z Z)
  | tail {c c' : Three} (a : ℕ) (b : Three) : einc c c' → einc (P a b c) (P a b c')
  | argZ {b b' : Three} (a : ℕ) : einc b b' → einc (P a b Z) (P a b' Z)

inductive eflip : Three → Three → Prop
  | leaf {w w' : ℕ} : w < w' → eflip (P w Z Z) (P w' Z Z)
  | tail {c c' : Three} (a : ℕ) (b : Three) : eflip c c' → eflip (P a b c) (P a b c')
  | argZ {b b' : Three} (a : ℕ) : eflip b b' → eflip (P a b Z) (P a b' Z)

theorem lext_olt {x y : Three} (h : lext x y) : x <o y := by
  induction h with
  | end_ w => simp
  | tail a b _ ih => exact olt_P_c a b ih
  | arg a c _ ih => exact olt_P_b a c c ih

theorem lflip_olt {x y : Three} (h : lflip x y) : x <o y := by
  induction h with
  | leaf hww' => exact olt_P_P.2 (Or.inl hww')
  | tail a b _ ih => exact olt_P_c a b ih
  | arg a c _ ih => exact olt_P_b a c c ih

theorem einc_lext {x y : Three} (h : einc x y) : lext x y := by
  induction h with
  | end_ w => exact lext.end_ w
  | tail a b _ ih => exact lext.tail a b ih
  | argZ a _ ih => exact lext.arg a Z ih

theorem eflip_lflip {x y : Three} (h : eflip x y) : lflip x y := by
  induction h with
  | leaf hww' => exact lflip.leaf hww'
  | tail a b _ ih => exact lflip.tail a b ih
  | argZ a _ ih => exact lflip.arg a Z ih

theorem einc_olt {x y : Three} (h : einc x y) : x <o y := lext_olt (einc_lext h)

theorem eflip_olt {x y : Three} (h : eflip x y) : x <o y := lflip_olt (eflip_lflip h)

/-! ## The gap lemmas

Nothing of size below `x` separates `x` from its end-increase `x'`: an
order-witness `¬ g <o x` together with `g <o x'` forces the comparison to be
resolved exactly at the modified end position, so `g` contains a copy of all
of `x` before that position. -/

theorem tsize_pos (t : Three) : 1 ≤ tsize t := by
  cases t <;> simp only [tsize] <;> omega

theorem einc_gap {x x' g : Three} (h : einc x x') (hng : ¬ g <o x)
    (hg : g <o x') : tsize x ≤ tsize g := by
  induction h generalizing g with
  | end_ w => exact tsize_pos g
  | @tail c c' a b hcc' ih =>
    cases g with
    | Z => exact absurd (olt_Z_P a b c) hng
    | P e f h' =>
      rw [olt_P_P] at hng hg
      rcases hg with h1 | ⟨rfl, h1⟩ | ⟨rfl, rfl, h1⟩
      · exact absurd (Or.inl h1) hng
      · exact absurd (Or.inr (Or.inl ⟨rfl, h1⟩)) hng
      · have hnh : ¬ h' <o c := fun hc => hng (Or.inr (Or.inr ⟨rfl, rfl, hc⟩))
        have := ih hnh h1
        simp only [tsize]
        omega
  | @argZ b b' a hbb' ih =>
    cases g with
    | Z => exact absurd (olt_Z_P a b Z) hng
    | P e f h' =>
      rw [olt_P_P] at hng hg
      rcases hg with h1 | ⟨rfl, h1⟩ | ⟨rfl, rfl, h1⟩
      · exact absurd (Or.inl h1) hng
      · have hnf : ¬ f <o b := fun hc => hng (Or.inr (Or.inl ⟨rfl, hc⟩))
        have h2 := ih hnf h1
        have h3 := tsize_pos h'
        simp only [tsize]
        omega
      · exact absurd h1 (not_olt_Z _)

theorem eflip_gap {x x' g : Three} (h : eflip x x') (hng : ¬ g <o x)
    (hg : g <o x') : tsize x ≤ tsize g := by
  induction h generalizing g with
  | @leaf w w' hww' =>
    cases g with
    | Z => exact absurd (olt_Z_P w Z Z) hng
    | P e f h' =>
      have h2 := tsize_pos f
      have h3 := tsize_pos h'
      simp only [tsize]
      omega
  | @tail c c' a b hcc' ih =>
    cases g with
    | Z => exact absurd (olt_Z_P a b c) hng
    | P e f h' =>
      rw [olt_P_P] at hng hg
      rcases hg with h1 | ⟨rfl, h1⟩ | ⟨rfl, rfl, h1⟩
      · exact absurd (Or.inl h1) hng
      · exact absurd (Or.inr (Or.inl ⟨rfl, h1⟩)) hng
      · have hnh : ¬ h' <o c := fun hc => hng (Or.inr (Or.inr ⟨rfl, rfl, hc⟩))
        have := ih hnh h1
        simp only [tsize]
        omega
  | @argZ b b' a hbb' ih =>
    cases g with
    | Z => exact absurd (olt_Z_P a b Z) hng
    | P e f h' =>
      rw [olt_P_P] at hng hg
      rcases hg with h1 | ⟨rfl, h1⟩ | ⟨rfl, rfl, h1⟩
      · exact absurd (Or.inl h1) hng
      · have hnf : ¬ f <o b := fun hc => hng (Or.inr (Or.inl ⟨rfl, hc⟩))
        have h2 := ih hnf h1
        have h3 := tsize_pos h'
        simp only [tsize]
        omega
      · exact absurd h1 (not_olt_Z _)

/-! ## Critical sets under one-position increase

No critical term is lost: every critical of `b` either survives in `b'` or
has a pointwise `lext`/`lflip`-partner among the criticals of `b'`. -/

theorem Gterm_lext_sup {b b' : Three} (h : lext b b') {u : ℕ} :
    ∀ g ∈ Gterm u b, g ∈ Gterm u b' ∨ ∃ g' ∈ Gterm u b', lext g g' := by
  induction h with
  | end_ w => intro g hg; simp at hg
  | @tail c c' a b0 hcc' ih =>
    intro g hg
    rcases mem_Gterm_P.1 hg with ⟨ha, hgb⟩ | hgc
    · exact Or.inl (mem_Gterm_P.2 (Or.inl ⟨ha, hgb⟩))
    · rcases ih g hgc with h1 | ⟨g', hg', h2⟩
      · exact Or.inl (mem_Gterm_P.2 (Or.inr h1))
      · exact Or.inr ⟨g', mem_Gterm_P.2 (Or.inr hg'), h2⟩
  | @arg b0 b0' a c hbb' ih =>
    intro g hg
    rcases mem_Gterm_P.1 hg with ⟨ha, rfl | hgb⟩ | hgc
    · exact Or.inr ⟨b0', mem_Gterm_P.2 (Or.inl ⟨ha, Or.inl rfl⟩), hbb'⟩
    · rcases ih g hgb with h1 | ⟨g', hg', h2⟩
      · exact Or.inl (mem_Gterm_P.2 (Or.inl ⟨ha, Or.inr h1⟩))
      · exact Or.inr ⟨g', mem_Gterm_P.2 (Or.inl ⟨ha, Or.inr hg'⟩), h2⟩
    · exact Or.inl (mem_Gterm_P.2 (Or.inr hgc))

theorem Gterm_lflip_sup {b b' : Three} (h : lflip b b') {u : ℕ} :
    ∀ g ∈ Gterm u b, g ∈ Gterm u b' ∨ ∃ g' ∈ Gterm u b', lflip g g' := by
  induction h with
  | @leaf w w' hww' =>
    intro g hg
    rcases mem_Gterm_P.1 hg with ⟨hw, rfl | hgb⟩ | hgc
    · exact Or.inl (mem_Gterm_P.2 (Or.inl ⟨hw.trans hww'.le, Or.inl rfl⟩))
    · simp at hgb
    · simp at hgc
  | @tail c c' a b0 hcc' ih =>
    intro g hg
    rcases mem_Gterm_P.1 hg with ⟨ha, hgb⟩ | hgc
    · exact Or.inl (mem_Gterm_P.2 (Or.inl ⟨ha, hgb⟩))
    · rcases ih g hgc with h1 | ⟨g', hg', h2⟩
      · exact Or.inl (mem_Gterm_P.2 (Or.inr h1))
      · exact Or.inr ⟨g', mem_Gterm_P.2 (Or.inr hg'), h2⟩
  | @arg b0 b0' a c hbb' ih =>
    intro g hg
    rcases mem_Gterm_P.1 hg with ⟨ha, rfl | hgb⟩ | hgc
    · exact Or.inr ⟨b0', mem_Gterm_P.2 (Or.inl ⟨ha, Or.inl rfl⟩), hbb'⟩
    · rcases ih g hgb with h1 | ⟨g', hg', h2⟩
      · exact Or.inl (mem_Gterm_P.2 (Or.inl ⟨ha, Or.inr h1⟩))
      · exact Or.inr ⟨g', mem_Gterm_P.2 (Or.inl ⟨ha, Or.inr hg'⟩), h2⟩
    · exact Or.inl (mem_Gterm_P.2 (Or.inr hgc))

/-! ## Fire transport

A collapse witness of `x` yields one for any end-increase of `x`: by the gap
lemma the old witness cannot have fallen strictly below `x'` (it is too
small), and by `Gterm_*_sup` it (or a pointwise partner above it) is still a
critical term of `x'`. -/

theorem fire_transport {x x' g : Three} {u : ℕ}
    (hR : einc x x' ∨ eflip x x')
    (hg : g ∈ Gterm u x) (hng : ¬ g <o x) :
    ∃ g' ∈ Gterm u x', ¬ g' <o x' := by
  have hsz : tsize g < tsize x := Gterm_tsize hg
  have hngx' : ¬ g <o x' := by
    intro hlt
    have : tsize x ≤ tsize g := by
      rcases hR with h | h
      · exact einc_gap h hng hlt
      · exact eflip_gap h hng hlt
    omega
  rcases hR with h | h
  · rcases Gterm_lext_sup (einc_lext h) g hg with h1 | ⟨g', hg', h2⟩
    · exact ⟨g, h1, hngx'⟩
    · exact ⟨g', hg', fun hlt => hngx' (olt_trans (lext_olt h2) hlt)⟩
  · rcases Gterm_lflip_sup (eflip_lflip h) g hg with h1 | ⟨g', hg', h2⟩
    · exact ⟨g, h1, hngx'⟩
    · exact ⟨g', hg', fun hlt => hngx' (olt_trans (lflip_olt h2) hlt)⟩

/-! ## Small computation lemmas -/

@[simp] theorem translate_nil : translate [] = Z := by rw [translate]

theorem translate_cons (p : ℕ × ℕ) (rest : PairSeq) :
    translate (p :: rest) =
      P p.2 (translate (rest.takeWhile fun r => p.1 < r.1))
            (translate (rest.dropWhile fun r => p.1 < r.1)) := by
  rw [translate]

theorem translate_single (q : ℕ × ℕ) : translate [q] = P q.2 Z Z := by
  simp [translate]

@[simp] theorem proj_Z (u : ℕ) : proj u Z = Z := proj_id (by simp)

theorem nrm_leaf (w : ℕ) : nrm (P w Z Z) = P w Z Z := by
  rw [nrm_P, nrm_Z, proj_Z, ins_Z]

/-! ## The snoc condition bundle and main induction

`snocok C q`: the conditions along the recursive decomposition of `C` under
which appending `q` strictly increases the normalized image.  Thanks to
`ins_olt_mono` the bundle degenerates to a single condition at the innermost
dominated run: when `q` extends the argument (`p.1 < q.1`), the projected
argument must strictly increase.  Deriving the bundle from standardness of
the host is the remaining class obligation (`ST_snocok`, future work). -/

def snocok : PairSeq → ℕ × ℕ → Prop
  | [], _ => False
  | p :: rest, q =>
    if (rest.dropWhile fun r => p.1 < r.1) = [] then
      p.1 < q.1 →
        proj p.2 (nrm (translate rest)) <o proj p.2 (nrm (translate (rest ++ [q])))
    else snocok (rest.dropWhile fun r => p.1 < r.1) q
  termination_by C _ => C.length
  decreasing_by
    exact Nat.lt_succ_of_le (List.length_dropWhile_le _ rest)

@[simp] theorem snocok_nil (q : ℕ × ℕ) : ¬ snocok [] q := by
  rw [snocok]
  exact id

theorem snocok_cons (p : ℕ × ℕ) (rest : PairSeq) (q : ℕ × ℕ) :
    snocok (p :: rest) q =
      (if (rest.dropWhile fun r => p.1 < r.1) = [] then
        p.1 < q.1 →
          proj p.2 (nrm (translate rest)) <o proj p.2 (nrm (translate (rest ++ [q])))
      else snocok (rest.dropWhile fun r => p.1 < r.1) q) := by
  rw [snocok]

/-- **Snoc main induction**: under the condition bundle, appending one column
strictly increases the normalized image.  Case (A) (new summand) is an
instance of `ins_olt_mono` with `Z <o` a leaf; case (B) (tail extension)
is `ins_olt_mono` on the recursive call; case (C) (argument extension)
is the bundled condition itself. -/
theorem nrm_snoc_seg : ∀ {C : PairSeq} {q : ℕ × ℕ}, snocok C q → C ≠ [] →
    nrm (translate C) <o nrm (translate (C ++ [q]))
  | [], _, _, hne => absurd rfl hne
  | p :: rest, q, hsok, _ => by
    by_cases hT : (rest.dropWhile fun r => p.1 < r.1) = []
    · have Kall : (rest.takeWhile fun r => p.1 < r.1) = rest :=
        List.takeWhile_eq_self_iff.2 (List.dropWhile_eq_nil_iff.1 hT)
      have nCs : nrm (translate (p :: rest))
          = P p.2 (proj p.2 (nrm (translate rest))) Z := by
        rw [translate_cons, Kall, hT, translate_nil, nrm_P, nrm_Z, ins_Z]
      rw [snocok_cons, if_pos hT] at hsok
      by_cases qd : p.1 < q.1
      · -- (C) argument extension
        have tw' : ((rest ++ [q]).takeWhile fun r => p.1 < r.1) = rest ++ [q] := by
          rw [takeWhile_append_all (List.dropWhile_eq_nil_iff.1 hT)]
          simp [qd]
        have dw' : ((rest ++ [q]).dropWhile fun r => p.1 < r.1) = [] := by
          rw [dropWhile_append_all (List.dropWhile_eq_nil_iff.1 hT)]
          simp [qd]
        have nC' : nrm (translate ((p :: rest) ++ [q]))
            = P p.2 (proj p.2 (nrm (translate (rest ++ [q])))) Z := by
          rw [List.cons_append, translate_cons, tw', dw', translate_nil,
              nrm_P, nrm_Z, ins_Z]
        rw [nCs, nC']
        exact olt_P_b p.2 Z Z (hsok qd)
      · -- (A) new summand
        have tw' : ((rest ++ [q]).takeWhile fun r => p.1 < r.1) = rest := by
          rw [takeWhile_append_all (List.dropWhile_eq_nil_iff.1 hT)]
          simp [qd]
        have dw' : ((rest ++ [q]).dropWhile fun r => p.1 < r.1) = [q] := by
          rw [dropWhile_append_all (List.dropWhile_eq_nil_iff.1 hT)]
          simp [qd]
        have nC' : nrm (translate ((p :: rest) ++ [q]))
            = ins p.2 (proj p.2 (nrm (translate rest))) (P q.2 Z Z) := by
          rw [List.cons_append, translate_cons, tw', dw', translate_single,
              nrm_P, nrm_leaf]
        have nCz : nrm (translate (p :: rest))
            = ins p.2 (proj p.2 (nrm (translate rest))) Z := by
          rw [translate_cons, Kall, hT, translate_nil, nrm_P, nrm_Z]
        rw [nCz, nC']
        exact ins_olt_mono (by simp)
    · -- (B) tail extension
      obtain ⟨w, win, wnp⟩ : ∃ w ∈ rest, ¬ p.1 < w.1 := by
        by_contra hall
        push Not at hall
        exact hT (List.dropWhile_eq_nil_iff.2 (by
          intro x hx
          simpa using hall x hx))
      have tw' : ((rest ++ [q]).takeWhile fun r => p.1 < r.1)
          = rest.takeWhile fun r => p.1 < r.1 :=
        takeWhile_append_not win (by simpa using wnp)
      have dw' : ((rest ++ [q]).dropWhile fun r => p.1 < r.1)
          = (rest.dropWhile fun r => p.1 < r.1) ++ [q] :=
        dropWhile_append_not win (by simpa using wnp)
      have nC : nrm (translate (p :: rest))
          = ins p.2 (proj p.2 (nrm (translate (rest.takeWhile fun r => p.1 < r.1))))
                (nrm (translate (rest.dropWhile fun r => p.1 < r.1))) := by
        rw [translate_cons, nrm_P]
      have nC' : nrm (translate ((p :: rest) ++ [q]))
          = ins p.2 (proj p.2 (nrm (translate (rest.takeWhile fun r => p.1 < r.1))))
                (nrm (translate ((rest.dropWhile fun r => p.1 < r.1) ++ [q]))) := by
        rw [List.cons_append, translate_cons, tw', dw', nrm_P]
      rw [snocok_cons, if_neg hT] at hsok
      rw [nC, nC']
      exact ins_olt_mono (nrm_snoc_seg hsok hT)
  termination_by C _ _ _ => C.length
  decreasing_by
    exact Nat.lt_succ_of_le (List.length_dropWhile_le _ rest)

/-- Wiring for the `Pred` case of the expansion step: dropping the last
column strictly decreases the normalized image, provided the condition
bundle holds for the dropped column. -/
theorem nrm_dropLast_olt {M : PairSeq} (hM : M ≠ []) (hd : M.dropLast ≠ [])
    (hsok : snocok M.dropLast (M.getLast hM)) :
    nrm (translate M.dropLast) <o nrm (translate M) := by
  have h := nrm_snoc_seg hsok hd
  rwa [List.dropLast_append_getLast hM] at h

/-! ## The max-row1 suffix (sequence side of the E6 machinery)

`msfx S` is the suffix of `S` starting at the *first* column whose row-1
value is maximal.  Empirically (E6): on standard dominated segments the
host-level projection, when it fires, evaluates to `nrm (translate (msfx S))`.
This section provides the pure sequence laws of `maxr1`/`msfx`. -/

/-- Maximal row-1 value of a segment (`0` on the empty segment). -/
def maxr1 (S : PairSeq) : ℕ := S.foldr (fun c m => max c.2 m) 0

@[simp] theorem maxr1_nil : maxr1 [] = 0 := rfl

theorem maxr1_cons (c : ℕ × ℕ) (S : PairSeq) :
    maxr1 (c :: S) = max c.2 (maxr1 S) := rfl

/-- The suffix from the first maximal-row-1 column. -/
def msfx (S : PairSeq) : PairSeq := S.dropWhile fun c => c.2 < maxr1 S

theorem le_maxr1 {S : PairSeq} : ∀ c ∈ S, c.2 ≤ maxr1 S := by
  induction S with
  | nil => simp
  | cons d S ih =>
    intro c hc
    rw [maxr1_cons]
    rcases List.mem_cons.1 hc with rfl | hc
    · exact le_max_left ..
    · exact le_trans (ih c hc) (le_max_right ..)

theorem maxr1_mem {S : PairSeq} (h : S ≠ []) : ∃ c ∈ S, c.2 = maxr1 S := by
  induction S with
  | nil => exact absurd rfl h
  | cons d S ih =>
    rw [maxr1_cons]
    by_cases hS : S = []
    · subst hS
      exact ⟨d, List.mem_cons_self .., by simp⟩
    · obtain ⟨c, hc, hce⟩ := ih hS
      rcases Nat.le_total (maxr1 S) d.2 with h1 | h1
      · exact ⟨d, List.mem_cons_self .., (max_eq_left h1).symm⟩
      · exact ⟨c, List.mem_cons_of_mem _ hc, by rw [hce, max_eq_right h1]⟩

theorem maxr1_foldr (S : PairSeq) (m : ℕ) :
    S.foldr (fun c m => max c.2 m) m = max (maxr1 S) m := by
  induction S with
  | nil => simp
  | cons d S ih => simp [List.foldr_cons, maxr1_cons, ih, max_assoc]

theorem maxr1_append (S T : PairSeq) :
    maxr1 (S ++ T) = max (maxr1 S) (maxr1 T) := by
  unfold maxr1
  rw [List.foldr_append]
  exact maxr1_foldr S _

theorem maxr1_snoc (S : PairSeq) (q : ℕ × ℕ) :
    maxr1 (S ++ [q]) = max (maxr1 S) q.2 := by
  rw [maxr1_append, maxr1_cons, maxr1_nil]
  simp

theorem msfx_ne_nil {S : PairSeq} (h : S ≠ []) : msfx S ≠ [] := by
  intro he
  obtain ⟨c, hc, hce⟩ := maxr1_mem h
  have := List.dropWhile_eq_nil_iff.1 he c hc
  simp [hce] at this

theorem head_msfx_not_lt {S : PairSeq}
    (w : (S.dropWhile fun c => c.2 < maxr1 S) ≠ []) :
    ¬ ((S.dropWhile fun c => c.2 < maxr1 S).head w).2 < maxr1 S := by
  have h1 := List.head_dropWhile_not (fun c : ℕ × ℕ => decide (c.2 < maxr1 S)) w
  simpa using h1

/-- The first column of `msfx S` realizes the maximum. -/
theorem msfx_head_snd {S : PairSeq} (h : S ≠ []) :
    ((msfx S).head (msfx_ne_nil h)).2 = maxr1 S := by
  have h2 := head_msfx_not_lt (S := S) (msfx_ne_nil h)
  have h3 : (msfx S).head (msfx_ne_nil h) ∈ S :=
    (List.dropWhile_sublist _).subset (List.head_mem _)
  exact le_antisymm (le_maxr1 _ h3) (Nat.le_of_not_lt h2)

/-- Same-cut append law: a column not exceeding the maximum extends the
maximal suffix. -/
theorem msfx_snoc_le {S : PairSeq} {q : ℕ × ℕ} (hS : S ≠ [])
    (h : q.2 ≤ maxr1 S) : msfx (S ++ [q]) = msfx S ++ [q] := by
  have hm : maxr1 (S ++ [q]) = maxr1 S := by
    rw [maxr1_snoc]
    exact max_eq_left h
  unfold msfx
  rw [hm]
  obtain ⟨c, hc, hce⟩ := maxr1_mem hS
  exact dropWhile_append_not hc (by simp [hce])

/-- Cut append law: a column exceeding the maximum restarts the suffix. -/
theorem msfx_snoc_gt {S : PairSeq} {q : ℕ × ℕ} (h : maxr1 S < q.2) :
    msfx (S ++ [q]) = [q] := by
  have hm : maxr1 (S ++ [q]) = q.2 := by
    rw [maxr1_snoc]
    exact max_eq_right (le_of_lt h)
  unfold msfx
  rw [hm]
  rw [dropWhile_append_all (by
    intro c hc
    simpa using lt_of_le_of_lt (le_maxr1 c hc) h)]
  simp

/-! ## Row-1 discipline `r1ok`

Every column at positive level has a row-0 parent (the nearest preceding
column one level below, with no dip in between) whose row-1 value it exceeds
by at most one.  Empirically exact on all standard hosts (14,558 columns).
This is the foundation for arithmetizing the row-level facts of the E6
campaign. -/

def r1ok (M : PairSeq) : Prop :=
  ∀ j, j < M.length → 0 < (M.getD j (0,0)).1 →
    ∃ k, k < j ∧ (M.getD k (0,0)).1 + 1 = (M.getD j (0,0)).1
      ∧ (∀ l, k < l → l < j → (M.getD j (0,0)).1 ≤ (M.getD l (0,0)).1)
      ∧ (M.getD j (0,0)).2 ≤ (M.getD k (0,0)).2 + 1

theorem diagSeq0_length (v : ℕ) : (diagSeq 0 v).length = v + 1 := by
  unfold diagSeq
  rw [List.length_map, List.length_range']
  omega

theorem diagSeq0_getD {v i : ℕ} (hi : i < v + 1) :
    (diagSeq 0 v).getD i (0,0) = (i, i) := by
  unfold diagSeq
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range' (by simpa using hi)]
  simp

theorem r1ok_diagSeq (v : ℕ) : r1ok (diagSeq 0 v) := by
  intro j hj hpos
  rw [diagSeq0_length] at hj
  rw [diagSeq0_getD hj] at hpos
  have hj0 : 0 < j := by simpa using hpos
  refine ⟨j - 1, by omega, ?_, ?_, ?_⟩
  · rw [diagSeq0_getD hj, diagSeq0_getD (show j - 1 < v + 1 by omega)]
    show j - 1 + 1 = j
    omega
  · intro l hl1 hl2
    omega
  · rw [diagSeq0_getD hj, diagSeq0_getD (show j - 1 < v + 1 by omega)]
    show j ≤ (j - 1) + 1
    omega

theorem getD_take {M : PairSeq} {m j : ℕ} (h : j < m) :
    (M.take m).getD j (0,0) = M.getD j (0,0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take, if_pos h]

theorem r1ok_take {M : PairSeq} (h : r1ok M) (m : ℕ) : r1ok (M.take m) := by
  intro j hj hpos
  rw [List.length_take] at hj
  have hjm : j < m := lt_of_lt_of_le hj (min_le_left _ _)
  have hjM : j < M.length := lt_of_lt_of_le hj (min_le_right _ _)
  rw [getD_take hjm] at hpos
  obtain ⟨k, hk, he, hbetween, hsnd⟩ := h j hjM hpos
  refine ⟨k, hk, ?_, ?_, ?_⟩
  · rw [getD_take (lt_trans hk hjm), getD_take hjm]
    exact he
  · intro l hl1 hl2
    rw [getD_take hjm, getD_take (lt_trans hl2 hjm)]
    exact hbetween l hl1 hl2
  · rw [getD_take hjm, getD_take (lt_trans hk hjm)]
    exact hsnd

theorem r1ok_dropLast {M : PairSeq} (h : r1ok M) : r1ok M.dropLast := by
  rw [List.dropLast_eq_take]
  exact r1ok_take h _


/-! ## Index bookkeeping for the copy decomposition

`oper_bad_blocks` presents the expansion as `G ++ (range n).flatMap (copy k)`;
these lemmas convert positions `k * |B| + q` of the flat copy region to the
source block, and decompose an arbitrary region index. -/

theorem getD_append_left {G X : PairSeq} {i : ℕ} (h : i < G.length) :
    (G ++ X).getD i (0,0) = G.getD i (0,0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left h]

theorem getD_append_right {G X : PairSeq} {i : ℕ} (h : G.length ≤ i) :
    (G ++ X).getD i (0,0) = X.getD (i - G.length) (0,0) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right h]

theorem index_decomp {i L n : ℕ} (hL : 0 < L) (hi : i < n * L) :
    ∃ k q, k < n ∧ q < L ∧ i = k * L + q := by
  refine ⟨i / L, i % L, ?_, Nat.mod_lt _ hL, ?_⟩
  · exact (Nat.div_lt_iff_lt_mul hL).2 hi
  · calc i = L * (i / L) + i % L := (Nat.div_add_mod i L).symm
    _ = i / L * L + i % L := by rw [Nat.mul_comm]

theorem copies_map_length (B : PairSeq) (f : ℕ → ℕ × ℕ → ℕ × ℕ) (n : ℕ) :
    ((List.range n).flatMap fun k => B.map (f k)).length = n * B.length := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    simp [ih, Nat.succ_mul]

theorem copies_map_getD {B : PairSeq} {n k q : ℕ} {f : ℕ → ℕ × ℕ → ℕ × ℕ}
    (hk : k < n) (hq : q < B.length) :
    ((List.range n).flatMap fun k => B.map (f k)).getD (k * B.length + q) (0,0)
      = f k (B.getD q (0,0)) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append]
    by_cases hkn : k < n
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left,
          ← List.getD_eq_getElem?_getD]
      · exact ih hkn
      · rw [copies_map_length]
        calc k * B.length + q < k * B.length + B.length := by omega
        _ = (k + 1) * B.length := (Nat.succ_mul k B.length).symm
        _ ≤ n * B.length := Nat.mul_le_mul_right _ hkn
    · have hk_eq : k = n := by omega
      subst hk_eq
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right
            (by rw [copies_map_length]; exact Nat.le_add_right _ _),
          copies_map_length, Nat.add_sub_cancel_left]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [List.getElem?_map, List.getElem?_eq_getElem hq]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
      rfl


/-! ## Row-1 discipline under the copy expansion

`copyExp G B d0 n` abstracts the bad branch of `oper` (`oper_bad_blocks`):
prefix `G` followed by `n` copies of the block `B`, the `k`-th copy shifted
in row 0 by `k * d0`.  `r1ok_copyExp` proves the three unconditional witness
cases (prefix transfer, identity copy, same-copy translation); the
level-minimal case (witness in the previous copy, the `r1ok_climb` core) is
the explicit hypothesis `hmin`. -/

/-- The copy expansion shape produced by the bad branch of `oper`. -/
def copyExp (G B : PairSeq) (d0 n : ℕ) : PairSeq :=
  G ++ (List.range n).flatMap fun k => B.map fun p => (p.1 + k * d0, p.2)

theorem copyExp_length (G B : PairSeq) (d0 n : ℕ) :
    (copyExp G B d0 n).length = G.length + n * B.length := by
  unfold copyExp
  rw [List.length_append, copies_map_length]

theorem copyExp_getD_pre {G B : PairSeq} {d0 n i : ℕ} (h : i < G.length) :
    (copyExp G B d0 n).getD i (0,0) = G.getD i (0,0) :=
  getD_append_left h

theorem copyExp_getD_copy {G B : PairSeq} {d0 n k q : ℕ}
    (hk : k < n) (hq : q < B.length) :
    (copyExp G B d0 n).getD (G.length + (k * B.length + q)) (0,0)
      = ((B.getD q (0,0)).1 + k * d0, (B.getD q (0,0)).2) := by
  unfold copyExp
  rw [getD_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      copies_map_getD hk hq]

theorem hostM_getD_pre {G B : PairSeq} {lp : ℕ × ℕ} {i : ℕ} (h : i < G.length) :
    (G ++ B ++ [lp]).getD i (0,0) = G.getD i (0,0) := by
  rw [getD_append_left (by simp; omega), getD_append_left h]

theorem hostM_getD_blk {G B : PairSeq} {lp : ℕ × ℕ} {q : ℕ} (hq : q < B.length) :
    (G ++ B ++ [lp]).getD (G.length + q) (0,0) = B.getD q (0,0) := by
  rw [getD_append_left (by simp; omega),
      getD_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem hostM_length (G B : PairSeq) (lp : ℕ × ℕ) :
    (G ++ B ++ [lp]).length = G.length + B.length + 1 := by
  simp
  omega

theorem r1ok_copyExp {G B : PairSeq} {lp : ℕ × ℕ} {n d0 : ℕ}
    (hr : r1ok (G ++ B ++ [lp]))
    (hmin : ∀ k q, 0 < k → k < n → q < B.length →
      (∀ r, r < q → (B.getD q (0,0)).1 ≤ (B.getD r (0,0)).1) →
      0 < (B.getD q (0,0)).1 + k * d0 →
      ∃ p, p < G.length + (k * B.length + q) ∧
        ((copyExp G B d0 n).getD p (0,0)).1 + 1 = (B.getD q (0,0)).1 + k * d0 ∧
        (∀ l, p < l → l < G.length + (k * B.length + q) →
          (B.getD q (0,0)).1 + k * d0 ≤ ((copyExp G B d0 n).getD l (0,0)).1) ∧
        (B.getD q (0,0)).2 ≤ ((copyExp G B d0 n).getD p (0,0)).2 + 1) :
    r1ok (copyExp G B d0 n) := by
  intro j hj hpos
  rw [copyExp_length] at hj
  by_cases hjL : j < G.length + B.length
  · -- transfer region: `copyExp` agrees with the host on `[0, |G| + |B|)`
    have hagree : ∀ i, i ≤ j → (copyExp G B d0 n).getD i (0,0)
        = (G ++ B ++ [lp]).getD i (0,0) := by
      intro i hi
      by_cases hig : i < G.length
      · rw [copyExp_getD_pre hig, hostM_getD_pre hig]
      · push Not at hig
        have hiL : i - G.length < B.length := by omega
        have hn0 : 0 < n := by
          cases n with
          | zero =>
            rw [Nat.zero_mul] at hj
            omega
          | succ m => exact Nat.succ_pos m
        have e1 : (copyExp G B d0 n).getD i (0,0)
            = ((B.getD (i - G.length) (0,0)).1 + 0 * d0,
               (B.getD (i - G.length) (0,0)).2) := by
          have hieq : i = G.length + (0 * B.length + (i - G.length)) := by
            rw [Nat.zero_mul]
            omega
          conv_lhs => rw [hieq]
          rw [copyExp_getD_copy hn0 hiL]
        have e2 : (G ++ B ++ [lp]).getD i (0,0) = B.getD (i - G.length) (0,0) := by
          have hieq : i = G.length + (i - G.length) := by omega
          conv_lhs => rw [hieq]
          rw [hostM_getD_blk hiL]
        rw [e1, e2]
        simp
    have hjM : j < (G ++ B ++ [lp]).length := by
      rw [hostM_length]
      omega
    have hposM : 0 < ((G ++ B ++ [lp]).getD j (0,0)).1 := by
      rw [← hagree j le_rfl]
      exact hpos
    obtain ⟨p, hp, he, hnd, hs⟩ := hr j hjM hposM
    refine ⟨p, hp, ?_, ?_, ?_⟩
    · rw [hagree p (le_of_lt hp), hagree j le_rfl]
      exact he
    · intro l hl1 hl2
      rw [hagree j le_rfl, hagree l (le_of_lt hl2)]
      exact hnd l hl1 hl2
    · rw [hagree j le_rfl, hagree p (le_of_lt hp)]
      exact hs
  · -- copy region with `k ≥ 1`
    push Not at hjL
    have hL : 0 < B.length := by
      by_contra hB0
      push Not at hB0
      have hB0' : B.length = 0 := by omega
      rw [hB0', Nat.mul_zero] at hj
      omega
    obtain ⟨k, q, hk, hq, hdec⟩ :=
      index_decomp hL (show j - G.length < n * B.length by omega)
    have hk1 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · rw [Nat.zero_mul] at hdec
        omega
      · exact h
    have hjeq : j = G.length + (k * B.length + q) := by omega
    subst hjeq
    rw [copyExp_getD_copy hk hq] at hpos ⊢
    by_cases hPM : ∀ r, r < q → (B.getD q (0,0)).1 ≤ (B.getD r (0,0)).1
    · -- level-minimal: previous-copy witness, by hypothesis
      exact hmin k q hk1 hk hq hPM hpos
    · -- in-block dip: the host witness lies in the block; translate it
      push Not at hPM
      obtain ⟨r, hrq, hrdip⟩ := hPM
      have hposB : 0 < (B.getD q (0,0)).1 := by omega
      have hjMq : G.length + q < (G ++ B ++ [lp]).length := by
        rw [hostM_length]
        omega
      have hposMq : 0 < ((G ++ B ++ [lp]).getD (G.length + q) (0,0)).1 := by
        rw [hostM_getD_blk hq]
        exact hposB
      obtain ⟨p, hp, he, hnd, hs⟩ := hr (G.length + q) hjMq hposMq
      have hpg : G.length + r ≤ p := by
        by_contra hcon
        push Not at hcon
        have hh := hnd (G.length + r) (by omega) (by omega)
        rw [hostM_getD_blk hq, hostM_getD_blk (lt_trans hrq hq)] at hh
        omega
      obtain ⟨r', rfl⟩ : ∃ r', p = G.length + r' := ⟨p - G.length, by omega⟩
      have hr'q : r' < q := by omega
      have hr'B : r' < B.length := lt_trans hr'q hq
      rw [hostM_getD_blk hr'B, hostM_getD_blk hq] at he hs
      refine ⟨G.length + (k * B.length + r'), by omega, ?_, ?_, ?_⟩
      · rw [copyExp_getD_copy hk hr'B]
        show (B.getD r' (0,0)).1 + k * d0 + 1 = (B.getD q (0,0)).1 + k * d0
        omega
      · intro l hl1 hl2
        obtain ⟨rr, hrr1, hrr2, rfl⟩ :
            ∃ rr, r' < rr ∧ rr < q ∧ l = G.length + (k * B.length + rr) :=
          ⟨l - G.length - k * B.length, by omega, by omega, by omega⟩
        rw [copyExp_getD_copy hk (lt_trans hrr2 hq)]
        show (B.getD q (0,0)).1 + k * d0 ≤ (B.getD rr (0,0)).1 + k * d0
        have hh := hnd (G.length + rr) (by omega) (by omega)
        rw [hostM_getD_blk hq, hostM_getD_blk (lt_trans hrr2 hq)] at hh
        omega
      · rw [copyExp_getD_copy hk hr'B]
        show (B.getD q (0,0)).2 ≤ (B.getD r' (0,0)).2 + 1
        exact hs


/-! ## The previous-copy witness: `q = 0` degeneration and the `d0 = 0` case

In `oper_bad_blocks` the block is *strictly* dominated (every later element
exceeds the root level `v0`), so the only level-minimal offset is the block
root itself (`dominated_PM_zero`).  For exact copies (`d0 = 0`) the host
witness of the root serves every copy unchanged. -/

theorem getD_mem {l : List (ℕ × ℕ)} {i : ℕ} (h : i < l.length) :
    l.getD i (0,0) ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem h

/-- In the strictly dominated block of `oper_bad_blocks`, the only
level-minimal offset is `q = 0`: any later offset has the dip `r = 0`. -/
theorem dominated_PM_zero {v0 w0 : ℕ} {R : PairSeq} {q : ℕ}
    (hdom : ∀ x ∈ R, v0 < x.1) (hq : q < ((v0,w0) :: R).length)
    (hPM : ∀ r, r < q →
      (((v0,w0) :: R).getD q (0,0)).1 ≤ (((v0,w0) :: R).getD r (0,0)).1) :
    q = 0 := by
  by_contra hq0
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have hq' : q' < R.length := by simpa using hq
  have hmem : R.getD q' (0,0) ∈ R := getD_mem hq'
  have hv : v0 < (R.getD q' (0,0)).1 := hdom _ hmem
  have h0 := hPM 0 (by omega)
  rw [List.getD_cons_zero, List.getD_cons_succ] at h0
  have h0' : (R.getD q' (0,0)).1 ≤ v0 := h0
  omega

/-- The previous-copy witness case for `d0 = 0`: the host witness of the
block root lies in the prefix and serves every copy (all copy levels stay
at or above `v0`). -/
theorem r1ok_min_d0zero {G B : PairSeq} {lp : ℕ × ℕ} {n v0 w0 : ℕ} {R : PairSeq}
    (hB : B = (v0, w0) :: R) (hdom : ∀ x ∈ R, v0 < x.1)
    (hr : r1ok (G ++ B ++ [lp]))
    {k q : ℕ} (_hk1 : 0 < k) (hk : k < n) (hq : q < B.length)
    (hPM : ∀ r, r < q → (B.getD q (0,0)).1 ≤ (B.getD r (0,0)).1)
    (hpos : 0 < (B.getD q (0,0)).1 + k * 0) :
    ∃ p, p < G.length + (k * B.length + q) ∧
      ((copyExp G B 0 n).getD p (0,0)).1 + 1 = (B.getD q (0,0)).1 + k * 0 ∧
      (∀ l, p < l → l < G.length + (k * B.length + q) →
        (B.getD q (0,0)).1 + k * 0 ≤ ((copyExp G B 0 n).getD l (0,0)).1) ∧
      (B.getD q (0,0)).2 ≤ ((copyExp G B 0 n).getD p (0,0)).2 + 1 := by
  subst hB
  have hq0 : q = 0 := dominated_PM_zero hdom hq hPM
  subst hq0
  have hposv : 0 < v0 := by simpa using hpos
  have hMg : (G ++ ((v0,w0) :: R) ++ [lp]).getD G.length (0,0) = (v0, w0) := by
    have h := hostM_getD_blk (G := G) (lp := lp)
      (show 0 < ((v0,w0) :: R).length by simp)
    rw [Nat.add_zero] at h
    rw [h, List.getD_cons_zero]
  have hjM : G.length < (G ++ ((v0,w0) :: R) ++ [lp]).length := by
    rw [hostM_length]
    omega
  have hposM : 0 < ((G ++ ((v0,w0) :: R) ++ [lp]).getD G.length (0,0)).1 := by
    rw [hMg]
    exact hposv
  obtain ⟨p, hp, he, hnd, hs⟩ := hr G.length hjM hposM
  rw [hostM_getD_pre hp, hMg] at he hs
  have he' : (G.getD p (0,0)).1 + 1 = v0 := he
  have hs' : w0 ≤ (G.getD p (0,0)).2 + 1 := hs
  refine ⟨p, by omega, ?_, ?_, ?_⟩
  · rw [copyExp_getD_pre hp]
    show (G.getD p (0,0)).1 + 1 = v0 + k * 0
    omega
  · intro l hl1 hl2
    show v0 + k * 0 ≤ ((copyExp G ((v0,w0) :: R) 0 n).getD l (0,0)).1
    by_cases hlg : l < G.length
    · rw [copyExp_getD_pre hlg]
      have hh := hnd l hl1 hlg
      rw [hostM_getD_pre hlg, hMg] at hh
      have hh' : v0 ≤ (G.getD l (0,0)).1 := hh
      omega
    · push Not at hlg
      have hmul : k * ((v0,w0) :: R).length ≤ n * ((v0,w0) :: R).length :=
        Nat.mul_le_mul_right _ (le_of_lt hk)
      have hlX : l - G.length < n * ((v0,w0) :: R).length := by omega
      obtain ⟨k', r, hk', hrL, hldec⟩ :=
        index_decomp (show 0 < ((v0,w0) :: R).length by simp) hlX
      obtain rfl : l = G.length + (k' * ((v0,w0) :: R).length + r) := by omega
      rw [copyExp_getD_copy hk' hrL]
      show v0 + k * 0 ≤ (((v0,w0) :: R).getD r (0,0)).1 + k' * 0
      have hbase : v0 ≤ (((v0,w0) :: R).getD r (0,0)).1 := by
        cases r with
        | zero => simp
        | succ r' =>
          rw [List.getD_cons_succ]
          exact le_of_lt (hdom _ (getD_mem (by simpa using hrL)))
      omega
  · rw [copyExp_getD_pre hp]
    show w0 ≤ (G.getD p (0,0)).2 + 1
    exact hs'

/-- The previous-copy witness case for `d0 ≥ 1`: the witness is the *last*
block offset at level `v0 + d0 - 1` in the previous copy.  Exactness of the
level and the no-dip property are forced by the `≤ +1` step discipline and
maximality; only the row-1 bound (`hclimb`) is a class fact. -/
theorem r1ok_min_d0pos {G B : PairSeq} {lp : ℕ × ℕ} {n v0 w0 d0 : ℕ} {R : PairSeq}
    (hB : B = (v0, w0) :: R) (hdom : ∀ x ∈ R, v0 < x.1)
    (hd0 : 0 < d0) (hlp : lp.1 = v0 + d0)
    (hstep : ∀ r, r + 1 < B.length →
      (B.getD (r+1) (0,0)).1 ≤ (B.getD r (0,0)).1 + 1)
    (hlpstep : lp.1 ≤ (B.getD (B.length - 1) (0,0)).1 + 1)
    (hclimb : ∀ r', r' < B.length → (B.getD r' (0,0)).1 = v0 + d0 - 1 →
      (∀ rr, r' < rr → rr < B.length → v0 + d0 ≤ (B.getD rr (0,0)).1) →
      w0 ≤ (B.getD r' (0,0)).2 + 1)
    {k q : ℕ} (hk1 : 0 < k) (hk : k < n) (hq : q < B.length)
    (hPM : ∀ r, r < q → (B.getD q (0,0)).1 ≤ (B.getD r (0,0)).1)
    (_hpos : 0 < (B.getD q (0,0)).1 + k * d0) :
    ∃ p, p < G.length + (k * B.length + q) ∧
      ((copyExp G B d0 n).getD p (0,0)).1 + 1 = (B.getD q (0,0)).1 + k * d0 ∧
      (∀ l, p < l → l < G.length + (k * B.length + q) →
        (B.getD q (0,0)).1 + k * d0 ≤ ((copyExp G B d0 n).getD l (0,0)).1) ∧
      (B.getD q (0,0)).2 ≤ ((copyExp G B d0 n).getD p (0,0)).2 + 1 := by
  have hq0 : q = 0 := by
    subst hB
    exact dominated_PM_zero hdom hq hPM
  subst hq0
  have hL : 0 < B.length := by
    subst hB
    simp
  have hB0 : B.getD 0 (0,0) = (v0, w0) := by
    subst hB
    rfl
  -- the candidate set and its greatest element
  set P : ℕ → Prop := fun r => (B.getD r (0,0)).1 ≤ v0 + d0 - 1 with hP
  have hP0 : P 0 := by
    rw [hP]
    simp only [hB0]
    show v0 ≤ v0 + d0 - 1
    omega
  set r' := Nat.findGreatest P (B.length - 1) with hr'def
  have hPr' : P r' := Nat.findGreatest_spec (Nat.zero_le _) hP0
  have hr'L : r' ≤ B.length - 1 := Nat.findGreatest_le _
  have hgreat : ∀ rr, r' < rr → rr ≤ B.length - 1 → ¬ P rr := by
    intro rr h1 h2
    exact Nat.findGreatest_is_greatest h1 h2
  have hgreat' : ∀ rr, r' < rr → rr < B.length →
      v0 + d0 ≤ (B.getD rr (0,0)).1 := by
    intro rr h1 h2
    have := hgreat rr h1 (by omega)
    rw [hP] at this
    simp only [not_le] at this
    omega
  -- level exactness at the witness
  have rexact : (B.getD r' (0,0)).1 = v0 + d0 - 1 := by
    have hub : (B.getD r' (0,0)).1 ≤ v0 + d0 - 1 := hPr'
    rcases Nat.lt_or_ge r' (B.length - 1) with hlt | hge
    · have hnP := hgreat (r' + 1) (Nat.lt_succ_self _) (by omega)
      rw [hP] at hnP
      simp only [not_le] at hnP
      have := hstep r' (by omega)
      omega
    · have hr'eq : r' = B.length - 1 := by omega
      rw [hlp] at hlpstep
      rw [hr'eq]
      rw [hr'eq] at hub
      omega
  -- multiplication bookkeeping
  have hkL : k * B.length = (k - 1) * B.length + B.length := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Nat.succ_mul]
    simp
  have hkd : k * d0 = (k - 1) * d0 + d0 := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    rw [Nat.succ_mul]
    simp
  have hk1n : k - 1 < n := by omega
  have hr'B : r' < B.length := by omega
  refine ⟨G.length + ((k - 1) * B.length + r'), by omega, ?_, ?_, ?_⟩
  · rw [copyExp_getD_copy hk1n hr'B]
    show (B.getD r' (0,0)).1 + (k - 1) * d0 + 1 = (B.getD 0 (0,0)).1 + k * d0
    rw [hB0, rexact]
    show v0 + d0 - 1 + (k - 1) * d0 + 1 = v0 + k * d0
    omega
  · intro l hl1 hl2
    have hmul : k * B.length ≤ n * B.length :=
      Nat.mul_le_mul_right _ (le_of_lt hk)
    have hlX : l - G.length < n * B.length := by omega
    obtain ⟨k'', rr, hk'', hrrL, hldec⟩ := index_decomp hL hlX
    -- the in-between positions live in copy `k - 1`, beyond `r'`
    have hk''eq : k'' = k - 1 := by
      rcases Nat.lt_trichotomy k'' (k - 1) with h | h | h
      · exfalso
        have : k'' + 1 ≤ k - 1 := by omega
        have hmul2 : (k'' + 1) * B.length ≤ (k - 1) * B.length :=
          Nat.mul_le_mul_right _ this
        rw [Nat.succ_mul] at hmul2
        omega
      · exact h
      · exfalso
        have : k ≤ k'' := by omega
        have hmul2 : k * B.length ≤ k'' * B.length :=
          Nat.mul_le_mul_right _ this
        omega
    subst hk''eq
    have hrr1 : r' < rr := by omega
    obtain rfl : l = G.length + ((k - 1) * B.length + rr) := by omega
    rw [copyExp_getD_copy hk1n hrrL]
    show (B.getD 0 (0,0)).1 + k * d0 ≤ (B.getD rr (0,0)).1 + (k - 1) * d0
    rw [hB0]
    have := hgreat' rr hrr1 hrrL
    show v0 + k * d0 ≤ (B.getD rr (0,0)).1 + (k - 1) * d0
    omega
  · rw [copyExp_getD_copy hk1n hr'B]
    show (B.getD 0 (0,0)).2 ≤ (B.getD r' (0,0)).2 + 1
    rw [hB0]
    exact hclimb r' hr'B rexact hgreat'


/-! ## Assembly: `r1ok` is preserved by `oper`, hence holds on `ST_PS`

All branches of the expansion step are wired: identity (short), `Pred`
(dropLast), and the bad branch through `oper_bad_blocks` → `copyExp`.
The step facts `hstep`/`hlpstep` come from the `steps1` component of
`blockok_ST_PS`.  The sole remaining obligation is the class fact
`climbok` (the `r1ok_climb` of the Isabelle campaign, open there too). -/

theorem hostM_getD_lp {G B : PairSeq} {lp : ℕ × ℕ} :
    (G ++ B ++ [lp]).getD (G.length + B.length) (0,0) = lp := by
  have e : (G ++ B).length = G.length + B.length := by simp
  rw [getD_append_right (by omega), e, Nat.sub_self]
  rfl

theorem r1ok_Pred {M : PairSeq} (h : r1ok M) : r1ok (Pred M) := by
  unfold Pred
  by_cases hl : M.length ≤ 1
  · rw [if_pos hl]
    exact h
  · rw [if_neg hl]
    exact r1ok_dropLast h

/-- **The climb bound.**  At a bad-branch decomposition with strictly
ascending copies (`d0 ≥ 1`, so the parent is in row 1), the last block column
`r'` at the parent level `v0 + d0 - 1` is a row-0 ancestor of the last
column; the maximality clause of `nextrel1` therefore forces its row-1 value
to be at least `lp.2 > w0`.  (This closes the `r1ok_climb` core: the `q = 0`
reduction `dominated_PM_zero` ties the witness to the *parent structure* of
the last column, where row-1 parenthood is decisive.) -/
theorem climb_bound {M G : PairSeq} {v0 w0 d0 : ℕ} {R : PairSeq} {lp : ℕ × ℕ}
    (hM : M = G ++ ((v0,w0) :: R) ++ [lp])
    (hd0 : 0 < d0) (hlp1 : lp.1 = v0 + d0) (hwlt : w0 < lp.2)
    (hnl1 : nextrel1 M G.length (M.length - 1))
    {r' : ℕ} (hr' : r' < ((v0,w0) :: R).length)
    (hlev : (((v0,w0) :: R).getD r' (0,0)).1 = v0 + d0 - 1)
    (hafter : ∀ rr, r' < rr → rr < ((v0,w0) :: R).length →
      v0 + d0 ≤ (((v0,w0) :: R).getD rr (0,0)).1) :
    w0 ≤ (((v0,w0) :: R).getD r' (0,0)).2 + 1 := by
  subst hM
  rcases Nat.eq_zero_or_pos r' with rfl | hr'pos
  · rw [List.getD_cons_zero]
    omega
  · have hlen : (G ++ ((v0,w0) :: R) ++ [lp]).length
        = G.length + ((v0,w0) :: R).length + 1 := hostM_length ..
    have hj1 : (G ++ ((v0,w0) :: R) ++ [lp]).length - 1
        = G.length + ((v0,w0) :: R).length := by omega
    have e0r : entry (G ++ ((v0,w0) :: R) ++ [lp]) 0 (G.length + r')
        = v0 + d0 - 1 := by
      unfold entry
      rw [if_pos rfl, hostM_getD_blk hr']
      exact hlev
    have e0j1 : entry (G ++ ((v0,w0) :: R) ++ [lp]) 0
        (G.length + ((v0,w0) :: R).length) = v0 + d0 := by
      unfold entry
      rw [if_pos rfl, hostM_getD_lp]
      exact hlp1
    have hn0 : nextrel0 (G ++ ((v0,w0) :: R) ++ [lp]) (G.length + r')
        (G.length + ((v0,w0) :: R).length) := by
      refine ⟨by omega, by omega, by omega, ?_, ?_⟩
      · rw [e0r, e0j1]
        omega
      · intro j hj
        obtain ⟨rr, hrr1, hrr2, rfl⟩ : ∃ rr, r' < rr
            ∧ rr < ((v0,w0) :: R).length ∧ j = G.length + rr :=
          ⟨j - G.length, by omega, by omega, by omega⟩
        rw [e0j1]
        unfold entry
        rw [if_pos rfl, hostM_getD_blk hrr2]
        exact hafter rr hrr1 hrr2
    have hle0 : le0 (G ++ ((v0,w0) :: R) ++ [lp]) (G.length + r')
        (G.length + ((v0,w0) :: R).length) :=
      ⟨by omega, by omega, Relation.ReflTransGen.single hn0⟩
    have hmax := hnl1.2.2.2.2.2 (G.length + r')
      ⟨by omega, by rw [hj1]; exact hle0⟩
    rw [hj1] at hmax
    have e1j1 : entry (G ++ ((v0,w0) :: R) ++ [lp]) 1
        (G.length + ((v0,w0) :: R).length) = lp.2 := by
      unfold entry
      rw [if_neg one_ne_zero, hostM_getD_lp]
    have e1r : entry (G ++ ((v0,w0) :: R) ++ [lp]) 1 (G.length + r')
        = (((v0,w0) :: R).getD r' (0,0)).2 := by
      unfold entry
      rw [if_neg one_ne_zero, hostM_getD_blk hr']
    rw [e1j1, e1r] at hmax
    omega

/-- **Row-1 discipline is preserved by the expansion step.** -/
theorem r1ok_oper {M : PairSeq} {n : ℕ} (hn : 1 ≤ n) (hr : r1ok M)
    (hst : steps1 M) : r1ok (M⟦n⟧) := by
  by_cases hL0 : M.length - 1 = 0
  · rw [oper_eq_self_of_short n hL0]
    exact hr
  by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0
  · rw [oper_eq_pred_of_zero n hL0 hz]
    exact r1ok_Pred hr
  by_cases hp : hasParent M (idx1 M (M.length - 1)) (M.length - 1)
  case neg =>
    rw [oper_eq_pred_of_noParent n hL0 hz hp]
    exact r1ok_Pred hr
  case pos =>
    obtain ⟨G, v0, w0, R, d0, lp, hM, hX, hdom, _hlpgt, hd0⟩ :=
      oper_bad_blocks (by omega) hz hp hn
    rw [hX]
    have hrM : r1ok (G ++ ((v0,w0) :: R) ++ [lp]) := hM ▸ hr
    have hstM : steps1 (G ++ ((v0,w0) :: R) ++ [lp]) := hM ▸ hst
    have hstep : ∀ r, r + 1 < ((v0,w0) :: R).length →
        ((((v0,w0) :: R)).getD (r+1) (0,0)).1
          ≤ ((((v0,w0) :: R)).getD r (0,0)).1 + 1 := by
      intro r hr1
      have hs := steps1_iff.1 hstM (G.length + r)
        (by rw [hostM_length]; omega)
      rw [show G.length + r + 1 = G.length + (r+1) by omega] at hs
      rw [hostM_getD_blk hr1, hostM_getD_blk (by omega)] at hs
      exact hs
    have hlpstep : lp.1
        ≤ ((((v0,w0) :: R)).getD (((v0,w0) :: R).length - 1) (0,0)).1 + 1 := by
      have hBlen : 0 < ((v0,w0) :: R).length := by simp
      have hs := steps1_iff.1 hstM (G.length + (((v0,w0) :: R).length - 1))
        (by rw [hostM_length]; omega)
      rw [show G.length + (((v0,w0) :: R).length - 1) + 1
            = G.length + ((v0,w0) :: R).length by omega] at hs
      rw [hostM_getD_lp, hostM_getD_blk (by omega)] at hs
      exact hs
    show r1ok (copyExp G ((v0,w0) :: R) d0 n)
    refine r1ok_copyExp hrM ?_
    intro k q hk1 hk hq hPM hpos
    rcases hd0 with hd00 | ⟨hd0p, hwlt, hlpe, hnl1⟩
    · subst hd00
      exact r1ok_min_d0zero rfl hdom hrM hk1 hk hq hPM hpos
    · exact r1ok_min_d0pos rfl hdom hd0p hlpe hstep hlpstep
        (fun r' hr' hlev hafter => climb_bound hM hd0p hlpe hwlt hnl1 hr' hlev hafter)
        hk1 hk hq hPM hpos

/-- **Row-1 discipline of standard sequences.** -/
theorem r1ok_ST_PS {M : PairSeq} (hM : ST_PS M) : r1ok M := by
  induction hM with
  | diag v => exact r1ok_diagSeq v
  | oper hN hn ih => exact r1ok_oper hn ih (blockok_ST_PS hN).2.2

end YAPSS
