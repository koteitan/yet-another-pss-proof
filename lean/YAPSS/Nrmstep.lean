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


/-! ## The innermost dominated run and the `ST_snocok` interface -/

/-- The innermost dominated run of a segment: follow the `snocok` descent
(drop the dominated prefix run repeatedly) to the final stage `(p, rest)`
with `rest` entirely dominated by `p`. -/
def innermost : PairSeq → (ℕ × ℕ) × PairSeq
  | [] => ((0, 0), [])
  | p :: rest =>
    if (rest.dropWhile fun r => p.1 < r.1) = [] then (p, rest)
    else innermost (rest.dropWhile fun r => p.1 < r.1)
  termination_by C => C.length
  decreasing_by
    exact Nat.lt_succ_of_le (List.length_dropWhile_le _ rest)

theorem innermost_cons (p : ℕ × ℕ) (rest : PairSeq) :
    innermost (p :: rest) =
      if (rest.dropWhile fun r => p.1 < r.1) = [] then (p, rest)
      else innermost (rest.dropWhile fun r => p.1 < r.1) := by
  rw [innermost]

/-- `snocok` says exactly: the argument-extension condition holds at the
innermost dominated run. -/
theorem snocok_iff_innermost : ∀ {C : PairSeq} (q : ℕ × ℕ), C ≠ [] →
    (snocok C q ↔
      ((innermost C).1.1 < q.1 →
        proj (innermost C).1.2 (nrm (translate (innermost C).2))
          <o proj (innermost C).1.2 (nrm (translate ((innermost C).2 ++ [q])))))
  | [], _, hne => absurd rfl hne
  | p :: rest, q, _ => by
    rw [snocok_cons, innermost_cons]
    by_cases hT : (rest.dropWhile fun r => p.1 < r.1) = []
    · rw [if_pos hT, if_pos hT]
    · rw [if_neg hT, if_neg hT]
      exact snocok_iff_innermost q hT
  termination_by C _ _ => C.length
  decreasing_by
    exact Nat.lt_succ_of_le (List.length_dropWhile_le _ rest)

theorem innermost_suffix : ∀ {C : PairSeq}, C ≠ [] →
    ((innermost C).1 :: (innermost C).2) <:+ C
  | [], hne => absurd rfl hne
  | p :: rest, _ => by
    rw [innermost_cons]
    by_cases hT : (rest.dropWhile fun r => p.1 < r.1) = []
    · rw [if_pos hT]
    · rw [if_neg hT]
      exact (innermost_suffix hT).trans
        ((List.dropWhile_suffix _).trans (List.suffix_cons p rest))
  termination_by C _ => C.length
  decreasing_by
    exact Nat.lt_succ_of_le (List.length_dropWhile_le _ rest)

theorem innermost_dom : ∀ {C : PairSeq}, C ≠ [] →
    ∀ r ∈ (innermost C).2, (innermost C).1.1 < r.1
  | [], hne => absurd rfl hne
  | p :: rest, _ => by
    rw [innermost_cons]
    by_cases hT : (rest.dropWhile fun r => p.1 < r.1) = []
    · rw [if_pos hT]
      intro r hr
      have := List.dropWhile_eq_nil_iff.1 hT r hr
      simpa using this
    · rw [if_neg hT]
      exact innermost_dom hT
  termination_by C _ => C.length
  decreasing_by
    exact Nat.lt_succ_of_le (List.length_dropWhile_le _ rest)

/-- **The `ST_snocok` interface**: `snocok C q` follows once the
argument-extension condition holds at every dominated suffix run of `C`.
This is the precise remaining obligation (`ST_snoc_C`) of the Pred-case
campaign: prove it for standard hosts `C ++ [q] ∈ ST_PS`. -/
theorem snocok_of_C {C : PairSeq} {q : ℕ × ℕ} (hne : C ≠ [])
    (hC : ∀ p rest, (p :: rest) <:+ C → (∀ r ∈ rest, p.1 < r.1) →
      p.1 < q.1 →
      proj p.2 (nrm (translate rest)) <o proj p.2 (nrm (translate (rest ++ [q])))) :
    snocok C q := by
  rw [snocok_iff_innermost q hne]
  exact hC _ _ (innermost_suffix hne) (innermost_dom hne)


/-! ## Case combinators for `ST_snoc_C` -/

/-- Case combinator for `ST_snoc_C`: if the base side does not fire, the
strict increase passes straight through the projections. -/
theorem proj_olt_of_nofire {u : ℕ} {x x' : Three} (hnf : ¬ pfire u x)
    (hlt : x <o x') : proj u x <o proj u x' := by
  rw [proj_nofire hnf]
  exact olt_ole_trans hlt (proj_ole u x')

/-- Case combinator for `ST_snoc_C`: a fire on the base side transports to
the end-increased side, so "base fires, extension does not" cannot occur. -/
theorem pfire_transport {u : ℕ} {x x' : Three}
    (hR : einc x x' ∨ eflip x x') (hf : pfire u x) : pfire u x' := by
  obtain ⟨g, hg, hng⟩ := pfire_iff.1 hf
  obtain ⟨g', hg', hng'⟩ := fire_transport hR hg hng
  exact pfire_iff.2 ⟨g', hg', hng'⟩


/-! ## Structural layer: the `einc ∪ eflip` snoc characterization

Where `nrm_snoc_seg` records only the strict `olt` increase, the structural
bundle `snocokS` pins the exact shape: appending one column performs one
end-position increase on the normalized image.  This is the input to
`pfire_transport` (a base-side fire survives the append), which excludes the
"base fires, extension does not" case of `ST_snoc_C`. -/

/-- Head argument of a term (`Z` on `Z`). -/
def hdarg : Three → Three
  | Z => Z
  | P _ b _ => b

@[simp] theorem hdarg_Z : hdarg Z = Z := rfl
@[simp] theorem hdarg_P (a : ℕ) (b c : Three) : hdarg (P a b c) = b := rfl

/-- The no-absorption condition for `ins a b t`. -/
def noabsorb (a : ℕ) (b t : Three) : Prop :=
  ¬ (a < lead t ∨ (a = lead t ∧ b <o hdarg t))

theorem ins_noabsorb {a : ℕ} {b t : Three} (h : noabsorb a b t) :
    ins a b t = P a b t := by
  cases t with
  | Z => rfl
  | P e f g =>
    rw [ins_P, if_neg]
    intro hab
    exact h (by simpa using hab)

/-- One-position end increase: insertion of one end leaf or one end-leaf
subscript flip. -/
def Einc (x y : Three) : Prop := einc x y ∨ eflip x y

theorem Einc_olt {x y : Three} (h : Einc x y) : x <o y := by
  rcases h with h | h
  · exact einc_olt h
  · exact eflip_olt h

/-- The structural snoc condition bundle: as `snocok`, but recording the
`Einc` shape at the argument extension, the row-1 bound at the new summand,
and the two no-absorption conditions along the tail descent. -/
def snocokS : PairSeq → ℕ × ℕ → Prop
  | [], _ => False
  | p :: rest, q =>
    if (rest.dropWhile fun r => p.1 < r.1) = [] then
      if p.1 < q.1 then
        Einc (proj p.2 (nrm (translate rest)))
             (proj p.2 (nrm (translate (rest ++ [q]))))
      else q.2 ≤ p.2
    else
      snocokS (rest.dropWhile fun r => p.1 < r.1) q ∧
      noabsorb p.2 (proj p.2 (nrm (translate (rest.takeWhile fun r => p.1 < r.1))))
        (nrm (translate (rest.dropWhile fun r => p.1 < r.1))) ∧
      noabsorb p.2 (proj p.2 (nrm (translate (rest.takeWhile fun r => p.1 < r.1))))
        (nrm (translate ((rest.dropWhile fun r => p.1 < r.1) ++ [q])))
  termination_by C _ => C.length
  decreasing_by
    exact Nat.lt_succ_of_le (List.length_dropWhile_le _ rest)

theorem snocokS_cons (p : ℕ × ℕ) (rest : PairSeq) (q : ℕ × ℕ) :
    snocokS (p :: rest) q =
      (if (rest.dropWhile fun r => p.1 < r.1) = [] then
        if p.1 < q.1 then
          Einc (proj p.2 (nrm (translate rest)))
               (proj p.2 (nrm (translate (rest ++ [q]))))
        else q.2 ≤ p.2
      else
        snocokS (rest.dropWhile fun r => p.1 < r.1) q ∧
        noabsorb p.2 (proj p.2 (nrm (translate (rest.takeWhile fun r => p.1 < r.1))))
          (nrm (translate (rest.dropWhile fun r => p.1 < r.1))) ∧
        noabsorb p.2 (proj p.2 (nrm (translate (rest.takeWhile fun r => p.1 < r.1))))
          (nrm (translate ((rest.dropWhile fun r => p.1 < r.1) ++ [q])))) := by
  rw [snocokS]

/-- **Structural snoc characterization**: under the structural bundle,
appending one column changes the normalized image by exactly one
end-position increase (`einc` or `eflip`). -/
theorem nrm_snoc_str : ∀ {C : PairSeq} {q : ℕ × ℕ}, snocokS C q → C ≠ [] →
    Einc (nrm (translate C)) (nrm (translate (C ++ [q])))
  | [], _, _, hne => absurd rfl hne
  | p :: rest, q, hsok, _ => by
    by_cases hT : (rest.dropWhile fun r => p.1 < r.1) = []
    · have Kall : (rest.takeWhile fun r => p.1 < r.1) = rest :=
        List.takeWhile_eq_self_iff.2 (List.dropWhile_eq_nil_iff.1 hT)
      have nCs : nrm (translate (p :: rest))
          = P p.2 (proj p.2 (nrm (translate rest))) Z := by
        rw [translate_cons, Kall, hT, translate_nil, nrm_P, nrm_Z, ins_Z]
      rw [snocokS_cons, if_pos hT] at hsok
      by_cases qd : p.1 < q.1
      · -- (C) argument extension
        rw [if_pos qd] at hsok
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
        rcases hsok with he | hf
        · exact Or.inl (einc.argZ p.2 he)
        · exact Or.inr (eflip.argZ p.2 hf)
      · -- (A) new summand
        rw [if_neg qd] at hsok
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
        have noab : ins p.2 (proj p.2 (nrm (translate rest))) (P q.2 Z Z)
            = P p.2 (proj p.2 (nrm (translate rest))) (P q.2 Z Z) := by
          apply ins_noabsorb
          intro hab
          rcases hab with h1 | ⟨h1, h2⟩
      
          · simp at h1
            omega
          · exact absurd h2 (by simp)
        rw [nCs, nC', noab]
        exact Or.inl (einc.tail p.2 _ (einc.end_ q.2))
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
      rw [snocokS_cons, if_neg hT] at hsok
      obtain ⟨sokT, na, na'⟩ := hsok
      have IH := nrm_snoc_str sokT hT
      rw [nC, nC', ins_noabsorb na, ins_noabsorb na']
      rcases IH with he | hf
      · exact Or.inl (einc.tail p.2 _ he)
      · exact Or.inr (eflip.tail p.2 _ hf)
  termination_by C _ _ _ => C.length
  decreasing_by
    exact Nat.lt_succ_of_le (List.length_dropWhile_le _ rest)


/-! ## Both-fire reduction and the subscript chain -/

/-- Reduction of `ST_snoc_C` to the both-fire case: with the structural
shape `Einc x x'`, only the simultaneous-fire comparison remains. -/
theorem proj_olt_of_Einc {u : ℕ} {x x' : Three} (hE : Einc x x')
    (hboth : pfire u x → pfire u x' → proj u x <o proj u x') :
    proj u x <o proj u x' := by
  by_cases hf : pfire u x
  · exact hboth hf (pfire_transport hE hf)
  · exact proj_olt_of_nofire hf (Einc_olt hE)

/-! ## The subscript chain: criticals, projections and `nrm` never invent
subscripts -/

theorem subs_P' (a : ℕ) (b c : Three) :
    subs (P a b c) = insert a (subs b ∪ subs c) := rfl

theorem Gterm_subs {u : ℕ} {g t : Three} (hg : g ∈ Gterm u t) :
    subs g ⊆ subs t := by
  induction t with
  | Z => simp at hg
  | P a b c ihb ihc =>
    rw [subs_P']
    rcases mem_Gterm_P.1 hg with ⟨_, rfl | hgb⟩ | hgc
    · exact fun x hx => Set.mem_insert_iff.2 (Or.inr (Set.mem_union_left _ hx))
    · exact fun x hx =>
        Set.mem_insert_iff.2 (Or.inr (Set.mem_union_left _ (ihb hgb hx)))
    · exact fun x hx =>
        Set.mem_insert_iff.2 (Or.inr (Set.mem_union_right _ (ihc hgc hx)))

theorem proj_subs (u : ℕ) (b : Three) : subs (proj u b) ⊆ subs b := by
  by_cases h : (Glist u b).filter (fun g => ¬ olt g b) = []
  · rw [proj_id h]
  · exact Gterm_subs (proj_mem_of_fire h)

theorem ins_subs (a : ℕ) (b t : Three) :
    subs (ins a b t) ⊆ insert a (subs b ∪ subs t) := by
  cases t with
  | Z =>
    rw [ins_Z, subs_P']
  | P e f g =>
    rw [ins_P]
    by_cases h : a < e ∨ (a = e ∧ b <o f)
    · rw [if_pos h]
      exact fun x hx => Set.mem_insert_iff.2 (Or.inr (Set.mem_union_right _ hx))
    · rw [if_neg h, subs_P']

theorem nrm_subs (t : Three) : subs (nrm t) ⊆ subs t := by
  induction t with
  | Z => simp [nrm_Z]
  | P a b c ihb ihc =>
    rw [nrm_P, subs_P']
    refine (ins_subs _ _ _).trans ?_
    intro x hx
    rcases Set.mem_insert_iff.1 hx with rfl | hx
    · exact Set.mem_insert _ _
    · rcases (Set.mem_union _ _ _).1 hx with hx | hx
      · exact Set.mem_insert_iff.2
          (Or.inr (Set.mem_union_left _ (ihb ((proj_subs a (nrm b)) hx))))
      · exact Set.mem_insert_iff.2 (Or.inr (Set.mem_union_right _ (ihc hx)))

theorem NT_subs (S : PairSeq) : subs (nrm (translate S)) ⊆ sndSet S :=
  (nrm_subs _).trans (subs_translate S)

/-! ## Head-subscript facts for normalized images -/

theorem ins_neZ (a : ℕ) (b t : Three) : ins a b t ≠ Z := by
  cases t with
  | Z => simp [ins_Z]
  | P e f g =>
    rw [ins_P]
    by_cases h : a < e ∨ (a = e ∧ b <o f)
    · rw [if_pos h]
      simp
    · rw [if_neg h]
      simp

theorem NT_neZ {p : ℕ × ℕ} {rest : PairSeq} :
    nrm (translate (p :: rest)) ≠ Z := by
  rw [translate_cons, nrm_P]
  exact ins_neZ _ _ _

/-- `ins` can only raise the head subscript. -/
theorem ins_lead_ge (a : ℕ) (b t : Three) : a ≤ lead (ins a b t) := by
  cases t with
  | Z => simp [ins_Z]
  | P e f g =>
    rw [ins_P]
    by_cases h : a < e ∨ (a = e ∧ b <o f)
    · rw [if_pos h]
      rcases h with h | ⟨rfl, _⟩
      · simp
        omega
      · simp
    · rw [if_neg h]
      simp

theorem NT_lead_ge (p : ℕ × ℕ) (rest : PairSeq) :
    p.2 ≤ lead (nrm (translate (p :: rest))) := by
  rw [translate_cons, nrm_P]
  exact ins_lead_ge ..

theorem lead_mem_subs {t : Three} (h : t ≠ Z) : lead t ∈ subs t := by
  cases t with
  | Z => exact absurd rfl h
  | P a b c =>
    rw [lead_P, subs_P']
    exact Set.mem_insert _ _

/-- **Head subscript of the normalized maximal suffix** = the maximal row-1
value: from below by the head column, from above by the subscript chain. -/
theorem NT_msfx_lead {S : PairSeq} (h : S ≠ []) :
    lead (nrm (translate (msfx S))) = maxr1 S := by
  obtain ⟨d, D, hdD⟩ : ∃ d D, msfx S = d :: D := by
    cases hm : msfx S with
    | nil => exact absurd hm (msfx_ne_nil h)
    | cons d D => exact ⟨d, D, rfl⟩
  have hd_eq : (msfx S).head (msfx_ne_nil h) = d := by
    have h1 : (msfx S).head? = some ((msfx S).head (msfx_ne_nil h)) :=
      List.head?_eq_some_head _
    have h2 : (msfx S).head? = some d := by
      rw [hdD]
      rfl
    exact Option.some.inj (h1.symm.trans h2)
  have hd2 : d.2 = maxr1 S := by
    have := msfx_head_snd h
    rw [hd_eq] at this
    exact this
  refine le_antisymm ?_ ?_
  · -- ≤ : the head subscript is a subscript of the image, hence a row-1 value
    have h1 : lead (nrm (translate (msfx S))) ∈ subs (nrm (translate (msfx S))) := by
      rw [hdD]
      exact lead_mem_subs NT_neZ
    have h2 := NT_subs (msfx S) h1
    obtain ⟨c, hc, hce⟩ := mem_sndSet.1 h2
    have hcS : c ∈ S := (List.dropWhile_suffix _).subset hc
    rw [← hce]
    exact le_maxr1 c hcS
  · rw [hdD, ← hd2]
    exact NT_lead_ge d D


/-! ## Low-subscript dominance -/

/-- A nonzero term is a principal term headed by its lead. -/
theorem eq_P_lead {t : Three} (h : t ≠ Z) : ∃ b c, t = P (lead t) b c := by
  cases t with
  | Z => exact absurd rfl h
  | P a b c => exact ⟨b, c, rfl⟩

/-- Low-subscript dominance: any term whose head subscript stays below
`maxr1 S` is strictly below the normalized maximal suffix. -/
theorem olt_NT_msfx_of_lead_lt {S : PairSeq} (h : S ≠ []) {g : Three}
    (hg : g = Z ∨ lead g < maxr1 S) :
    g <o nrm (translate (msfx S)) := by
  obtain ⟨d, D, hdD⟩ : ∃ d D, msfx S = d :: D := by
    cases hm : msfx S with
    | nil => exact absurd hm (msfx_ne_nil h)
    | cons d D => exact ⟨d, D, rfl⟩
  have hne : nrm (translate (msfx S)) ≠ Z := by
    rw [hdD]
    exact NT_neZ
  obtain ⟨b, c, hP⟩ := eq_P_lead hne
  rw [hP, NT_msfx_lead h]
  exact olt_P_of_lead_lt b c hg

/-- Critical terms of a normalized image never exceed the maximal row-1
value in head subscript. -/
theorem Gterm_NT_lead_le {S : PairSeq} {u : ℕ} {g : Three}
    (hg : g ∈ Gterm u (nrm (translate S))) (hne : g ≠ Z) :
    lead g ≤ maxr1 S := by
  have h1 : lead g ∈ subs g := lead_mem_subs hne
  have h2 : lead g ∈ sndSet S := NT_subs S (Gterm_subs hg h1)
  obtain ⟨c, hc, hce⟩ := mem_sndSet.1 h2
  rw [← hce]
  exact le_maxr1 c hc

/-! ## The dominated-segment classes

`dseg u S`: `S` is a nonempty, entirely dominated standard sub-segment whose
enclosing head has row-1 value `u`.  `fbseg` relaxes the left boundary by a
skipped `mid` whose levels stay at or above the head of `S` (the forest
boundary condition); it is closed under both descents of the translate
recursion. -/

def dseg (u : ℕ) (S : PairSeq) : Prop :=
  S ≠ [] ∧ ∃ pre pp post, ST_PS (pre ++ (pp :: S) ++ post)
    ∧ (∀ r ∈ S, pp.1 < r.1) ∧ u = pp.2

def fbseg (u : ℕ) (S : PairSeq) : Prop :=
  S ≠ [] ∧ ∃ pre pp mid post, ST_PS (pre ++ (pp :: (mid ++ S)) ++ post)
    ∧ (∀ r ∈ mid ++ S, pp.1 < r.1)
    ∧ (∀ r ∈ mid, S.headI.1 ≤ r.1) ∧ u = pp.2

theorem dseg_fbseg {u : ℕ} {S : PairSeq} (h : dseg u S) : fbseg u S := by
  obtain ⟨hne, pre, pp, post, hst, hdom, hu⟩ := h
  exact ⟨hne, pre, pp, [], post, by simpa using hst, by simpa using hdom,
    by simp, hu⟩

/-- Descent into the argument (the dominated run after the head column). -/
theorem fbseg_K_desc {u : ℕ} {c : ℕ × ℕ} {rest : PairSeq}
    (h : fbseg u (c :: rest))
    (hne : (rest.takeWhile fun r => c.1 < r.1) ≠ []) :
    fbseg c.2 (rest.takeWhile fun r => c.1 < r.1) := by
  obtain ⟨-, pre, pp, mid, post, hst, -, -, -⟩ := h
  refine ⟨hne, pre ++ (pp :: mid), c, [],
    (rest.dropWhile fun r => c.1 < r.1) ++ post, ?_, ?_, by simp, rfl⟩
  · have heq : (pre ++ (pp :: mid))
        ++ (c :: ([] ++ (rest.takeWhile fun r => c.1 < r.1)))
        ++ ((rest.dropWhile fun r => c.1 < r.1) ++ post)
        = pre ++ (pp :: (mid ++ (c :: rest))) ++ post := by
      simp only [List.cons_append, List.append_assoc, List.nil_append]
      rw [← List.append_assoc (rest.takeWhile fun r => c.1 < r.1),
          List.takeWhile_append_dropWhile]
    rw [heq]
    exact hst
  · intro r hr
    have := List.mem_takeWhile_imp (by simpa using hr)
    simpa using this

/-- Descent into the tail (the rest after the dominated run), keeping the
same enclosing head. -/
theorem fbseg_T_desc {u : ℕ} {c : ℕ × ℕ} {rest : PairSeq}
    (h : fbseg u (c :: rest))
    (hne : (rest.dropWhile fun r => c.1 < r.1) ≠ []) :
    fbseg u (rest.dropWhile fun r => c.1 < r.1) := by
  obtain ⟨-, pre, pp, mid, post, hst, hdom, hfb, hu⟩ := h
  obtain ⟨t0, T', hT0⟩ : ∃ t0 T',
      (rest.dropWhile fun r => c.1 < r.1) = t0 :: T' := by
    cases hTc : rest.dropWhile fun r => c.1 < r.1 with
    | nil => exact absurd hTc hne
    | cons t0 T' => exact ⟨t0, T', rfl⟩
  have ht0 : ¬ c.1 < t0.1 := by
    have h1 := List.head_dropWhile_not (fun r : ℕ × ℕ => decide (c.1 < r.1)) hne
    have h2 : (rest.dropWhile fun r => c.1 < r.1).head hne = t0 := by
      have ha : (rest.dropWhile fun r => c.1 < r.1).head?
          = some ((rest.dropWhile fun r => c.1 < r.1).head hne) :=
        List.head?_eq_some_head _
      have hb : (rest.dropWhile fun r => c.1 < r.1).head? = some t0 := by
        rw [hT0]
        rfl
      exact Option.some.inj (ha.symm.trans hb)
    rw [h2] at h1
    simpa using h1
  refine ⟨hne, pre, pp, mid ++ (c :: (rest.takeWhile fun r => c.1 < r.1)),
    post, ?_, ?_, ?_, hu⟩
  · have heq : pre ++ (pp :: ((mid ++ (c :: (rest.takeWhile fun r => c.1 < r.1)))
        ++ (rest.dropWhile fun r => c.1 < r.1))) ++ post
        = pre ++ (pp :: (mid ++ (c :: rest))) ++ post := by
      simp only [List.cons_append, List.append_assoc]
      rw [← List.append_assoc (rest.takeWhile fun r => c.1 < r.1),
          List.takeWhile_append_dropWhile]
    rw [heq]
    exact hst
  · intro r hr
    apply hdom
    simp only [List.mem_append, List.mem_cons] at hr ⊢
    rcases hr with (hm | rfl | hK) | hT'
    · exact Or.inl hm
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ((List.takeWhile_sublist _).subset hK))
    · exact Or.inr (Or.inr ((List.dropWhile_sublist _).subset hT'))
  · intro r hr
    rw [hT0, List.headI_cons]
    simp only [List.mem_append, List.mem_cons] at hr
    rcases hr with hm | rfl | hK
    · have := hfb r hm
      rw [List.headI_cons] at this
      omega
    · omega
    · have := List.mem_takeWhile_imp hK
      simp at this
      omega


/-! ## The forest-boundary level squeeze -/

theorem getD_middle {pre X post : PairSeq} {i : ℕ} (h : i < X.length) :
    (pre ++ X ++ post).getD (pre.length + i) (0,0) = X.getD i (0,0) := by
  rw [getD_append_left (by simp; omega),
      getD_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- **Level squeeze at the forest boundary**: in an `fbseg`, the head of the
segment sits exactly one level above the enclosing head, and so does the
head of any sum-adjacent tail; hence the two heads tie in row 0. -/
theorem fbseg_hd_level {u : ℕ} {c : ℕ × ℕ} {rest : PairSeq}
    (h : fbseg u (c :: rest)) {t0 : ℕ × ℕ} {T' : PairSeq}
    (hT0 : (rest.dropWhile fun r => c.1 < r.1) = t0 :: T') :
    t0.1 = c.1 := by
  obtain ⟨-, pre, pp, mid, post, hst, hdom, hfb, -⟩ := h
  have hsteps := steps1_iff.1 (blockok_ST_PS hst).2.2
  have hlen : (pre ++ (pp :: (mid ++ (c :: rest))) ++ post).length
      = pre.length + (mid.length + rest.length + 2) + post.length := by
    simp
    omega
  -- the column right after `pp`
  have hpp : (pre ++ (pp :: (mid ++ (c :: rest))) ++ post).getD pre.length (0,0)
      = pp := by
    have h0 := getD_middle (pre := pre) (X := pp :: (mid ++ (c :: rest)))
      (post := post) (i := 0) (by simp)
    rw [Nat.add_zero, List.getD_cons_zero] at h0
    exact h0
  have hstep0 := hsteps pre.length (by omega)
  rw [show pre.length + 1 = pre.length + 1 from rfl, hpp] at hstep0
  have hnext : (pre ++ (pp :: (mid ++ (c :: rest))) ++ post).getD
      (pre.length + 1) (0,0) = (mid ++ (c :: rest)).getD 0 (0,0) := by
    have := getD_middle (pre := pre) (X := pp :: (mid ++ (c :: rest)))
      (post := post) (i := 1) (by simp)
    simpa using this
  rw [hnext] at hstep0
  -- squeeze: fst c = fst pp + 1
  have hc_eq : c.1 = pp.1 + 1 := by
    have hc_gt : pp.1 < c.1 := hdom c (by simp)
    cases mid with
    | nil =>
      rw [List.nil_append, List.getD_cons_zero] at hstep0
      omega
    | cons m0 mid' =>
      have hm0 : ((m0 :: mid') ++ (c :: rest)).getD 0 (0,0) = m0 := by
        rw [List.cons_append, List.getD_cons_zero]
      rw [hm0] at hstep0
      have hbd := hfb m0 (List.mem_cons_self ..)
      rw [List.headI_cons] at hbd
      omega
  -- t0 is dominated by pp and not by c
  have ht0_gt : pp.1 < t0.1 := by
    refine hdom t0 ?_
    have ht0rest : t0 ∈ rest :=
      (List.dropWhile_sublist _).subset (hT0 ▸ List.mem_cons_self ..)
    simp [ht0rest]
  have ht0_le : ¬ c.1 < t0.1 := by
    have h1 := List.head_dropWhile_not (fun r : ℕ × ℕ => decide (c.1 < r.1))
      (l := rest) (by rw [hT0]; simp)
    have h2 : (rest.dropWhile fun r => c.1 < r.1).head (by rw [hT0]; simp)
        = t0 := by
      have ha := List.head?_eq_some_head
        (l := rest.dropWhile fun r => c.1 < r.1) (by rw [hT0]; simp)
      have hb : (rest.dropWhile fun r => c.1 < r.1).head? = some t0 := by
        rw [hT0]
        rfl
      exact Option.some.inj (ha.symm.trans hb)
    rw [h2] at h1
    simpa using h1
  omega

/-- Upper bound on the head subscript of any normalized segment image. -/
theorem NT_lead_le {S : PairSeq} (hne : S ≠ []) :
    lead (nrm (translate S)) ≤ maxr1 S := by
  obtain ⟨p, rest, rfl⟩ : ∃ p rest, S = p :: rest := by
    cases S with
    | nil => exact absurd rfl hne
    | cons p rest => exact ⟨p, rest, rfl⟩
  have h1 : lead (nrm (translate (p :: rest))) ∈ subs (nrm (translate (p :: rest))) :=
    lead_mem_subs NT_neZ
  obtain ⟨c, hc, hce⟩ := mem_sndSet.1 (NT_subs _ h1)
  rw [← hce]
  exact le_maxr1 c hc


/-! ## Sum-adjacent row-1 non-increase (F1)

The CNF adjacency clause of the host translate, extracted at an arbitrary
column by walking the translate recursion: the head of the sum-adjacent
tail (at level at least the column's) has row-1 value at most the column's.
This is the engine behind the no-absorption facts of the C1 chain. -/

theorem cnf_P_arg {a : ℕ} {b t : Three} (h : cnf (P a b t)) : cnf b := by
  cases t with
  | Z => exact h
  | P e f g => exact h.1

theorem cnf_P_tail {a : ℕ} {b t : Three} (h : cnf (P a b t)) : cnf t := by
  cases t with
  | Z => trivial
  | P e f g => exact h.2.2

theorem dropWhile_cons_head_not {α : Type*} {p : α → Bool} {l : List α}
    {a : α} {t : List α} (h : l.dropWhile p = a :: t) : p a = false := by
  have hne : l.dropWhile p ≠ [] := by
    rw [h]
    simp
  have h1 := List.head_dropWhile_not p hne
  have h2 : (l.dropWhile p).head hne = a := by
    have ha := List.head?_eq_some_head (l := l.dropWhile p) hne
    have hb : (l.dropWhile p).head? = some a := by
      rw [h]
      rfl
    exact Option.some.inj (ha.symm.trans hb)
  rw [h2] at h1
  exact h1

/-- **The full CNF adjacency clause at an arbitrary column**: a column and
the head of its sum-adjacent tail (at level at least the column's) compare
as non-increasing principal terms — subscripts first, then the raw translate
arguments at a tie. -/
theorem cnf_adjacent_full : ∀ {W : PairSeq} {c t0 : ℕ × ℕ} {Zs T' : PairSeq},
    cnf (translate W) → (c :: Zs) <:+ W →
    (Zs.dropWhile fun r => c.1 < r.1) = t0 :: T' →
    c.1 ≤ t0.1 →
    ¬ (P c.2 (translate (Zs.takeWhile fun r => c.1 < r.1)) Z
        <o P t0.2 (translate (T'.takeWhile fun r => t0.1 < r.1)) Z)
  | [], c, t0, Zs, T', _, hsuf, _, _ => by
    have := hsuf.length_le
    simp at this
  | w :: W', c, t0, Zs, T', hcnf, hsuf, hT0, hge => by
    rcases List.suffix_cons_iff.1 hsuf with heq | hsuf'
    · injection heq with h1 h2
      subst h1
      subst h2
      rw [translate_cons, hT0, translate_cons] at hcnf
      exact (cnf_P_P.1 hcnf).2.1
    · rw [translate_cons] at hcnf
      have hsplit := List.suffix_or_suffix_of_suffix hsuf'
        (List.dropWhile_suffix (l := W') (fun r => decide (w.1 < r.1)))
      rcases hsplit with hin | hout
      · exact cnf_adjacent_full (cnf_P_tail hcnf) hin hT0 hge
      · rcases List.suffix_cons_iff.1 hout with hTeq | hTZ
        · exact cnf_adjacent_full (cnf_P_tail hcnf) (by rw [hTeq]) hT0 hge
        · obtain ⟨Zk, hZk⟩ := hTZ
          have hcZk : (c :: Zk) <:+ (W'.takeWhile fun r => w.1 < r.1) := by
            obtain ⟨s, hs⟩ := hsuf'
            refine ⟨s, ?_⟩
            have hsplit2 : (s ++ (c :: Zk)) ++ (W'.dropWhile fun r => w.1 < r.1)
                = (W'.takeWhile fun r => w.1 < r.1)
                  ++ (W'.dropWhile fun r => w.1 < r.1) := by
              rw [List.takeWhile_append_dropWhile, List.append_assoc,
                  List.cons_append, hZk, hs]
            exact List.append_cancel_right hsplit2
          have hcK : w.1 < c.1 := by
            have hcmem : c ∈ W'.takeWhile fun r => w.1 < r.1 :=
              hcZk.subset (List.mem_cons_self ..)
            have := List.mem_takeWhile_imp hcmem
            simpa using this
          cases hZkd : Zk.dropWhile fun r => c.1 < r.1 with
          | nil =>
            exfalso
            have hdw : Zs.dropWhile (fun r => c.1 < r.1)
                = (W'.dropWhile fun r => w.1 < r.1).dropWhile
                    (fun r => c.1 < r.1) := by
              conv_lhs => rw [← hZk]
              exact dropWhile_append_all (List.dropWhile_eq_nil_iff.1 hZkd)
            cases hTc : (W'.dropWhile fun r => w.1 < r.1) with
            | nil =>
              rw [hTc] at hdw
              rw [hdw] at hT0
              simp at hT0
            | cons h0 T0' =>
              have hh0 : ¬ w.1 < h0.1 := by
                have := dropWhile_cons_head_not hTc
                simpa using this
              have hfail : ¬ c.1 < h0.1 := by omega
              rw [hTc, List.dropWhile_cons, if_neg (by simpa using hfail)] at hdw
              rw [hdw] at hT0
              injection hT0 with h1 h2
              subst h1
              omega
          | cons d D =>
            have hdmem : d ∈ Zk :=
              (List.dropWhile_sublist _).subset (hZkd ▸ List.mem_cons_self ..)
            have hdfail : ¬ c.1 < d.1 := by
              have := dropWhile_cons_head_not hZkd
              simpa using this
            have hdw : Zs.dropWhile (fun r => c.1 < r.1)
                = (Zk.dropWhile fun r => c.1 < r.1)
                  ++ (W'.dropWhile fun r => w.1 < r.1) := by
              conv_lhs => rw [← hZk]
              exact dropWhile_append_not hdmem (by simpa using hdfail)
            rw [hZkd, List.cons_append] at hdw
            rw [hdw] at hT0
            injection hT0 with h1 h2
            subst h1
            -- run equalities: the conclusion's runs match the recursive ones
            have hKeq : Zs.takeWhile (fun r => c.1 < r.1)
                = Zk.takeWhile (fun r => c.1 < r.1) := by
              conv_lhs => rw [← hZk]
              exact takeWhile_append_not hdmem (by simpa using hdfail)
            have hT'eq : T'.takeWhile (fun r => d.1 < r.1)
                = D.takeWhile (fun r => d.1 < r.1) := by
              rw [← h2]
              have hd_gt : w.1 < d.1 := by
                have hdK0 : d ∈ (W'.takeWhile fun r => w.1 < r.1) :=
                  hcZk.subset (List.mem_cons_of_mem _ hdmem)
                have := List.mem_takeWhile_imp hdK0
                simpa using this
              cases hDd : D.dropWhile fun r => d.1 < r.1 with
              | nil =>
                rw [takeWhile_append_all (List.dropWhile_eq_nil_iff.1 hDd),
                    List.takeWhile_eq_self_iff.2 (List.dropWhile_eq_nil_iff.1 hDd)]
                cases hTc : (W'.dropWhile fun r => w.1 < r.1) with
                | nil =>
                  simp
                | cons h0 T0' =>
                  have hh0 : ¬ w.1 < h0.1 := by
                    have := dropWhile_cons_head_not hTc
                    simpa using this
                  rw [List.takeWhile_cons,
                      if_neg (by simpa using (show ¬ d.1 < h0.1 by omega))]
                  simp
              | cons e E =>
                have hemem : e ∈ D :=
                  (List.dropWhile_sublist _).subset (hDd ▸ List.mem_cons_self ..)
                have hefail : ¬ d.1 < e.1 := by
                  have := dropWhile_cons_head_not hDd
                  simpa using this
                exact takeWhile_append_not hemem (by simpa using hefail)
            rw [hKeq, hT'eq]
            exact cnf_adjacent_full (cnf_P_arg hcnf) hcZk hZkd hge
  termination_by W _ _ _ _ _ _ _ _ => W.length
  decreasing_by
  · exact Nat.lt_succ_of_le (List.length_dropWhile_le _ W')
  · exact Nat.lt_succ_of_le (List.length_dropWhile_le _ W')
  · exact Nat.lt_succ_of_le (List.takeWhile_sublist _).length_le

/-- Sum-adjacent row-1 non-increase (the subscript half of
`cnf_adjacent_full`). -/
theorem cnf_adjacent_snd_le {W : PairSeq} {c t0 : ℕ × ℕ} {Zs T' : PairSeq}
    (hcnf : cnf (translate W)) (hsuf : (c :: Zs) <:+ W)
    (hT0 : (Zs.dropWhile fun r => c.1 < r.1) = t0 :: T')
    (hge : c.1 ≤ t0.1) : t0.2 ≤ c.2 := by
  have h := cnf_adjacent_full hcnf hsuf hT0 hge
  rw [olt_P_P] at h
  push Not at h
  omega


/-! ## Dominated runs by position (toward `SIB_prefix`) -/

/-- The dominated run of position `j`: the maximal block of strictly higher
columns immediately after `j`. -/
def runAt (M : PairSeq) (j : ℕ) : PairSeq :=
  (M.drop (j + 1)).takeWhile fun r => (M.getD j (0,0)).1 < r.1

theorem runAt_cons_zero (p : ℕ × ℕ) (rest : PairSeq) :
    runAt (p :: rest) 0 = rest.takeWhile fun r => p.1 < r.1 := by
  unfold runAt
  rw [List.drop_succ_cons, List.drop_zero, List.getD_cons_zero]

theorem runAt_cons_succ (p : ℕ × ℕ) (rest : PairSeq) (j : ℕ) :
    runAt (p :: rest) (j + 1) = runAt rest j := by
  unfold runAt
  rw [List.drop_succ_cons, List.getD_cons_succ]

/-- `runAt` only sees the suffix from `j`: stable under prefix extension. -/
theorem runAt_append_left {G M : PairSeq} {j : ℕ} :
    runAt (G ++ M) (G.length + j) = runAt M j := by
  unfold runAt
  rw [getD_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      show G.length + j + 1 = G.length + (j + 1) by omega,
      List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
      Nat.add_sub_cancel_left]

/-- `takeWhile` over an append never enters the second part when its head
fails the predicate. -/
theorem takeWhile_append_head_stop {α : Type*} {p : α → Bool}
    {l1 l2 : List α} (h : ∀ a ∈ l2.head?, p a = false) :
    (l1 ++ l2).takeWhile p = l1.takeWhile p := by
  rw [List.takeWhile_append]
  by_cases hl : (l1.takeWhile p).length = l1.length
  · rw [if_pos hl]
    have hself : l1.takeWhile p = l1 :=
      (List.takeWhile_sublist _).eq_of_length hl
    cases l2 with
    | nil => simp [hself]
    | cons a t =>
      have ha : p a = false := h a rfl
      rw [List.takeWhile_cons, if_neg (by simp [ha])]
      simp [hself]
  · rw [if_neg hl]


/-! ## The constant-copy region and its drop decomposition -/

/-- The constant-copy region (`d0 = 0`): `n` literal repetitions of `B`. -/
def repB (B : PairSeq) : ℕ → PairSeq
  | 0 => []
  | n + 1 => B ++ repB B n

@[simp] theorem repB_zero (B : PairSeq) : repB B 0 = [] := rfl
theorem repB_succ (B : PairSeq) (n : ℕ) : repB B (n + 1) = B ++ repB B n := rfl

theorem flatMap_const_eq_repB (B : PairSeq) :
    ∀ n, ((List.range n).flatMap fun _ => B) = repB B n
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ_eq_map, List.flatMap_cons, repB_succ,
        ← flatMap_const_eq_repB B n]
    congr 1
    rw [List.flatMap_map]

/-- Dropping into the `k`-th repetition exposes the block suffix followed by
the remaining repetitions. -/
theorem repB_drop (B : PairSeq) :
    ∀ (k n q : ℕ), k < n → q < B.length →
      (repB B n).drop (k * B.length + (q + 1))
        = B.drop (q + 1) ++ repB B (n - k - 1)
  | 0, 0, q, hk, _ => absurd hk (by omega)
  | 0, n + 1, q, _, hq => by
    rw [repB_succ, Nat.zero_mul, Nat.zero_add,
        List.drop_append_of_le_length (by omega)]
    simp
  | k + 1, 0, q, hk, _ => absurd hk (by omega)
  | k + 1, n + 1, q, hk, hq => by
    rw [show n + 1 - (k + 1) - 1 = n - k - 1 by omega]
    rw [repB_succ, List.drop_append, List.drop_eq_nil_of_le (by
        have : B.length ≤ (k + 1) * B.length := by
          calc B.length = 1 * B.length := (Nat.one_mul _).symm
          _ ≤ (k + 1) * B.length := Nat.mul_le_mul_right _ (by omega)
        omega),
      List.nil_append,
      show (k + 1) * B.length + (q + 1) - B.length
          = k * B.length + (q + 1) by
        rw [Nat.succ_mul]
        omega,
      repB_drop B k n q (by omega) hq]

theorem repB_getD (B : PairSeq) :
    ∀ (k n q : ℕ), k < n → q < B.length →
      (repB B n).getD (k * B.length + q) (0,0) = B.getD q (0,0)
  | 0, 0, q, hk, _ => absurd hk (by omega)
  | 0, n + 1, q, _, hq => by
    rw [repB_succ, Nat.zero_mul, Nat.zero_add, getD_append_left hq]
  | k + 1, 0, q, hk, _ => absurd hk (by omega)
  | k + 1, n + 1, q, hk, hq => by
    rw [repB_succ, getD_append_right (by
        have : B.length ≤ (k + 1) * B.length := by
          calc B.length = 1 * B.length := (Nat.one_mul _).symm
          _ ≤ (k + 1) * B.length := Nat.mul_le_mul_right _ (by omega)
        omega),
      show (k + 1) * B.length + q - B.length = k * B.length + q by
        rw [Nat.succ_mul]
        omega,
      repB_getD B k n q (by omega) hq]

/-- **Runs in the constant-copy region never cross a copy boundary**: at the
copy position `(k, q)` the dominated run is exactly the block's own run at
`q` (the next copy's root level is at most every block level). -/
theorem repB_runAt {v0 w0 : ℕ} {R : PairSeq} (hdom : ∀ x ∈ R, v0 < x.1)
    {k n q : ℕ} (hk : k < n) (hq : q < ((v0,w0) :: R).length) :
    runAt (repB ((v0,w0) :: R) n) (k * ((v0,w0) :: R).length + q)
      = runAt ((v0,w0) :: R) q := by
  have hroot : v0 ≤ (((v0,w0) :: R).getD q (0,0)).1 := by
    cases q with
    | zero => simp
    | succ q' =>
      rw [List.getD_cons_succ]
      exact le_of_lt (hdom _ (getD_mem (by simpa using hq)))
  unfold runAt
  rw [show k * ((v0,w0) :: R).length + q + 1
        = k * ((v0,w0) :: R).length + (q + 1) by omega,
      repB_drop _ k n q hk hq, repB_getD _ k n q hk hq,
      takeWhile_append_head_stop (by
        intro a ha
        cases hm : n - k - 1 with
        | zero =>
          rw [hm] at ha
          simp at ha
        | succ m =>
          rw [hm, repB_succ, List.cons_append] at ha
          simp only [List.head?_cons, Option.mem_some_iff] at ha
          subst ha
          simp only [decide_eq_false_iff_not, not_lt]
          exact hroot)]


/-! ## Runs are blockok segments -/

/-- `steps1` restricts to any contiguous infix. -/
theorem steps1_infix {l1 l2 l3 : PairSeq} (h : steps1 (l1 ++ l2 ++ l3)) :
    steps1 l2 := by
  rw [steps1_iff] at h ⊢
  intro j hj
  have hh := h (l1.length + j) (by simp; omega)
  rwa [show l1.length + j + 1 = l1.length + (j + 1) by omega,
       getD_middle (by omega), getD_middle (by omega)] at hh

/-- A dominated run inside a `steps1` host is a `blockok` segment one level
above its base column. -/
theorem runAt_blockok {M : PairSeq} {j : ℕ} (hst : steps1 M)
    (hj : j < M.length) :
    blockok ((M.getD j (0,0)).1 + 1) (runAt M j) := by
  have hdecomp : M = M.take (j + 1) ++ runAt M j
      ++ (M.drop (j + 1)).dropWhile (fun r => (M.getD j (0,0)).1 < r.1) := by
    conv_lhs => rw [← List.take_append_drop (j + 1) M]
    rw [List.append_assoc]
    congr 1
    exact (List.takeWhile_append_dropWhile).symm
  refine ⟨?_, ?_, ?_⟩
  · -- head of the run sits exactly one level above
    intro hne
    obtain ⟨r0, R', hr0⟩ : ∃ r0 R', runAt M j = r0 :: R' := by
      cases hrc : runAt M j with
      | nil => exact absurd hrc hne
      | cons r0 R' => exact ⟨r0, R', rfl⟩
    rw [hr0, List.headI_cons]
    obtain ⟨rest, hrest⟩ :=
      List.takeWhile_prefix (l := M.drop (j + 1))
        (p := fun r => decide ((M.getD j (0,0)).1 < r.1))
    have hr0' : (M.drop (j + 1)).takeWhile
        (fun r => decide ((M.getD j (0,0)).1 < r.1)) = r0 :: R' := hr0
    rw [hr0'] at hrest
    have hdrop : M.drop (j + 1) = r0 :: (R' ++ rest) := by
      rw [← hrest]
      rfl
    have hjlen : j + 1 < M.length := by
      have := congrArg List.length hdrop
      simp [List.length_drop] at this
      omega
    have h0 : (M.drop (j + 1))[0]? = some r0 := by
      rw [hdrop]
      rfl
    rw [List.getElem?_drop] at h0
    simp only [Nat.add_zero] at h0
    have hr0M : M.getD (j + 1) (0,0) = r0 := by
      rw [List.getD_eq_getElem?_getD, h0]
      rfl
    have hdom : (M.getD j (0,0)).1 < r0.1 := by
      have hmem : r0 ∈ runAt M j := by
        rw [hr0]
        exact List.mem_cons_self ..
      have := List.mem_takeWhile_imp hmem
      simpa using this
    have hstep := steps1_iff.1 hst j hjlen
    rw [hr0M] at hstep
    omega
  · -- all run elements are above the base level
    intro p hp
    have := List.mem_takeWhile_imp hp
    simp only [decide_eq_true_eq] at this
    omega
  · -- steps within the run
    exact steps1_infix (hdecomp ▸ hst)

/-- Raw translate strictly increases along any proper prefix extension. -/
theorem translate_prefix_olt {D : PairSeq} (hD : D ≠ []) :
    ∀ C, translate C <o translate (C ++ D) := by
  induction D with
  | nil => exact absurd rfl hD
  | cons d D' ih =>
    intro C
    have h1 := translate_snoc_increase C d
    cases D' with
    | nil => simpa using h1
    | cons e E =>
      have h2 := ih (by simp) (C ++ [d])
      rw [List.append_assoc] at h2
      exact olt_trans h1 (by simpa using h2)

/-- Runs commute with the row-0 shift. -/
theorem runAt_shiftr0 (d : ℕ) (B : PairSeq) {q : ℕ} (hq : q < B.length) :
    runAt (shiftr0 d B) q = shiftr0 d (runAt B q) := by
  unfold runAt shiftr0
  have hget : ((B.map fun p => (p.1 + d, p.2)).getD q (0,0))
      = ((B.getD q (0,0)).1 + d, (B.getD q (0,0)).2) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hq, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hq]
    rfl
  rw [hget, ← List.map_drop, List.takeWhile_map]
  congr 1
  congr 1
  funext r
  simp only [Function.comp]
  exact decide_eq_decide.2 (by omega)


/-! ## The tie-sibling run dichotomy (SIB without generation induction) -/

/-- Position bookkeeping: the run of the head of a suffix. -/
theorem runAt_suffix {W : PairSeq} {c : ℕ × ℕ} {Zs : PairSeq}
    (hsuf : (c :: Zs) <:+ W) :
    ∃ j, j < W.length ∧ W.getD j (0,0) = c ∧
      runAt W j = Zs.takeWhile fun r => c.1 < r.1 := by
  obtain ⟨s, hs⟩ := hsuf
  refine ⟨s.length, ?_, ?_, ?_⟩
  · rw [← hs]
    simp
  · rw [← hs]
    have h := getD_middle (pre := s) (X := c :: Zs) (post := []) (i := 0)
      (by simp)
    rw [List.append_nil, Nat.add_zero, List.getD_cons_zero] at h
    exact h
  · rw [← hs]
    have h := runAt_append_left (G := s) (M := c :: Zs) (j := 0)
    rw [Nat.add_zero] at h
    rw [h, runAt_cons_zero]

/-- **Tie-sibling run dichotomy**: at a full tie, the sum-adjacent sibling's
run is the run itself or lexicographically below it.  No generation
induction needed: CNF adjacency excludes the ascending case through the
order isomorphism on blockok segments. -/
theorem tie_sibling_seqlex {W : PairSeq} {c t0 : ℕ × ℕ} {Zs T' : PairSeq}
    (hcnf : cnf (translate W)) (hst : steps1 W) (hsuf : (c :: Zs) <:+ W)
    (hT0 : (Zs.dropWhile fun r => c.1 < r.1) = t0 :: T')
    (htie0 : c.1 = t0.1) (htie1 : c.2 = t0.2) :
    (T'.takeWhile fun r => t0.1 < r.1) = (Zs.takeWhile fun r => c.1 < r.1)
    ∨ seqlex (T'.takeWhile fun r => t0.1 < r.1)
        (Zs.takeWhile fun r => c.1 < r.1) := by
  have hadj := cnf_adjacent_full hcnf hsuf hT0 (le_of_eq htie0)
  have hnolt : ¬ (translate (Zs.takeWhile fun r => c.1 < r.1)
      <o translate (T'.takeWhile fun r => t0.1 < r.1)) := by
    intro hlt
    exact hadj (olt_P_P.2 (Or.inr (Or.inl ⟨htie1, hlt⟩)))
  -- both runs are blockok segments at level `c.1 + 1`
  obtain ⟨j, hjW, hjc, hjrun⟩ := runAt_suffix hsuf
  have hsufT : (t0 :: T') <:+ W := by
    have h1 : (t0 :: T') <:+ Zs := hT0 ▸ List.dropWhile_suffix _
    exact (h1.trans (List.suffix_cons c Zs)).trans hsuf
  obtain ⟨j', hj'W, hj't0, hj'run⟩ := runAt_suffix hsufT
  have bK : blockok (c.1 + 1) (Zs.takeWhile fun r => c.1 < r.1) := by
    have h := runAt_blockok hst hjW
    rw [hjc, hjrun] at h
    exact h
  have bK1 : blockok (c.1 + 1) (T'.takeWhile fun r => t0.1 < r.1) := by
    rw [htie0]
    have h := runAt_blockok hst hj'W
    rw [hj't0, hj'run] at h
    exact h
  rcases seqlex_total (T'.takeWhile fun r => t0.1 < r.1)
      (Zs.takeWhile fun r => c.1 < r.1) with heq | hlt | hgt
  · exact Or.inl heq
  · exact Or.inr hlt
  · exact absurd (seqlex_imp_olt (c.1 + 1) _ _ bK bK1 hgt) hnolt

/-- A head-maximal segment is its own maximal suffix. -/
theorem msfx_eq_self_of_headmax {s0 : ℕ × ℕ} {S' : PairSeq}
    (h : s0.2 = maxr1 (s0 :: S')) : msfx (s0 :: S') = s0 :: S' := by
  unfold msfx
  rw [List.dropWhile_cons, if_neg]
  simp only [decide_eq_true_eq]
  omega


/-! ## The NT_tie combinator -/

/-- **`NT_tie` combinator**: given the run dichotomy (proved:
`tie_sibling_seqlex`), the master order-preservation at shorter pairs, and
no-fire on both runs (the head-maximality class fact), the earlier sibling's
projection is never below the later's. -/
theorem NT_tie_of {u : ℕ} {K K1 : PairSeq}
    (hdich : K1 = K ∨ seqlex K1 K)
    (hmaster : seqlex K1 K → nrm (translate K1) <o nrm (translate K))
    (hnf : ¬ pfire u (nrm (translate K)))
    (hnf1 : ¬ pfire u (nrm (translate K1))) :
    ¬ (proj u (nrm (translate K)) <o proj u (nrm (translate K1))) := by
  rw [proj_nofire hnf, proj_nofire hnf1]
  rcases hdich with rfl | hsl
  · exact olt_irrefl _
  · intro hlt
    exact olt_irrefl _ (olt_trans (hmaster hsl) hlt)

/-- Head-maximality survives truncation of the tail. -/
theorem headmax_prefix {s0 : ℕ × ℕ} {S' D : PairSeq}
    (h : s0.2 = maxr1 (s0 :: (S' ++ D))) : s0.2 = maxr1 (s0 :: S') := by
  have h1 : s0.2 ≤ maxr1 (s0 :: S') := le_maxr1 s0 (List.mem_cons_self ..)
  have h2 : maxr1 (s0 :: S') ≤ maxr1 (s0 :: (S' ++ D)) := by
    rw [show s0 :: (S' ++ D) = (s0 :: S') ++ D by simp, maxr1_append]
    exact le_max_left ..
  omega


/-! ## The HM⁺ discipline (head-maximality under low closure)

Mined exact on standard hosts (0/19030): whenever a run is closed by a
column whose row-1 value does not exceed the base's, every run based at or
inside the region is head-maximal.  This subsumes the head-maximality of
tie-closed sibling runs (the no-fire input of `NT_tie_of`) and of `i1 = 0`
block tails. -/

/-- A segment is head-maximal if its head realizes its maximal row-1 value. -/
def headmax (K : PairSeq) : Prop := K = [] ∨ K.headI.2 = maxr1 K

/-- The stop position of the run of `a` (first later position not above). -/
def stopAt (M : PairSeq) (a : ℕ) : ℕ := a + 1 + (runAt M a).length

/-- **The HM⁺ discipline** (mined exact, 0/19030): whenever the run of `a`
is closed by a column whose row-1 value does not exceed `a`'s, every run
based at or inside that region is head-maximal. -/
def hmok (M : PairSeq) : Prop :=
  ∀ a, a < M.length → stopAt M a < M.length →
    (M.getD (stopAt M a) (0,0)).2 ≤ (M.getD a (0,0)).2 →
    ∀ p, a ≤ p → p < stopAt M a → headmax (runAt M p)

theorem runAt_diagSeq0 (v a : ℕ) (ha : a < v + 1) :
    (runAt (diagSeq 0 v) a).length = v - a := by
  unfold runAt
  rw [diagSeq0_getD ha]
  have hdrop : (diagSeq 0 v).drop (a + 1)
      = (List.range' (a + 1) (v - a)).map fun j => (j, j) := by
    unfold diagSeq
    rw [← List.map_drop]
    congr 1
    rw [List.drop_range']
    congr 1 <;> omega
  rw [hdrop, List.takeWhile_eq_self_iff.2 (by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    obtain ⟨i, hi, rfl⟩ := List.mem_range'.1 hj
    simp
    omega)]
  rw [List.length_map, List.length_range']

theorem hmok_diagSeq (v : ℕ) : hmok (diagSeq 0 v) := by
  intro a ha hstop
  rw [diagSeq0_length] at ha hstop
  unfold stopAt at hstop
  rw [runAt_diagSeq0 v a ha] at hstop
  omega


/-! ## HM⁺ under truncation -/

theorem takeWhile_length_le_of_fail {α : Type*} {pr : α → Bool} {L : List α}
    {i : ℕ} (hi : i < L.length) (hf : pr L[i] = false) :
    (L.takeWhile pr).length ≤ i := by
  by_contra hcon
  push Not at hcon
  have h1 : (L.takeWhile pr)[i] = L[i] :=
    (List.takeWhile_prefix pr).getElem hcon
  have h2 := List.mem_takeWhile_imp (List.getElem_mem hcon)
  rw [h1, hf] at h2
  exact Bool.false_ne_true h2

theorem runAt_take_length {M : PairSeq} {m a : ℕ} (ha : a < m) :
    (runAt (M.take m) a).length = min (m - (a + 1)) (runAt M a).length := by
  unfold runAt
  rw [getD_take ha, List.drop_take, ← List.take_takeWhile, List.length_take]

theorem runAt_take_eq {M : PairSeq} {m a : ℕ} (ha : a < m)
    (hstop : stopAt (M.take m) a < m) :
    runAt (M.take m) a = runAt M a := by
  unfold stopAt at hstop
  rw [runAt_take_length ha] at hstop
  have hle : (runAt M a).length ≤ m - (a + 1) := by omega
  unfold runAt
  rw [getD_take ha, List.drop_take, ← List.take_takeWhile]
  exact List.take_of_length_le (le_trans hle (by omega))



theorem prefix_getD_eq {α : Type*} {l1 l2 : List α}
    (h : l1 <+: l2) {i : ℕ} (hi : i < l1.length) (d : α) :
    l1.getD i d = l2.getD i d := by
  rw [getD_eq_getElem' _ _ hi,
      getD_eq_getElem' _ _ (lt_of_lt_of_le hi h.length_le)]
  exact h.getElem hi


theorem getD_drop {α : Type*} {L : List α} {n i : ℕ} (d : α) :
    (L.drop n).getD i d = L.getD (n + i) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_drop]

/-- The column at the stop position fails the run predicate. -/
theorem stop_col_fails {pr : (ℕ × ℕ) → Bool} {L : List (ℕ × ℕ)}
    (h : (L.takeWhile pr).length < L.length) :
    pr (L.getD (L.takeWhile pr).length (0,0)) = false := by
  have hdec : L.takeWhile pr ++ L.dropWhile pr = L :=
    List.takeWhile_append_dropWhile
  have hne : L.dropWhile pr ≠ [] := by
    intro he
    have hlen := congrArg List.length hdec
    rw [he] at hlen
    simp at hlen
    omega
  obtain ⟨d, D, hdD⟩ : ∃ d D, L.dropWhile pr = d :: D := by
    cases hc : L.dropWhile pr with
    | nil => exact absurd hc hne
    | cons d D => exact ⟨d, D, rfl⟩
  have hdrop : L.drop (L.takeWhile pr).length = L.dropWhile pr := by
    nth_rewrite 2 [← hdec]
    exact List.drop_left
  have hd : L.getD (L.takeWhile pr).length (0,0) = d := by
    calc L.getD (L.takeWhile pr).length (0,0)
        = (L.drop (L.takeWhile pr).length).getD 0 (0,0) := by
          rw [getD_drop, Nat.add_zero]
    _ = d := by rw [hdrop, hdD, List.getD_cons_zero]
  rw [hd]
  exact dropWhile_cons_head_not hdD

/-- Positions strictly inside a run region carry the run's elements. -/
theorem getD_run_region {M : PairSeq} {a p : ℕ} (hp1 : a < p)
    (hp2 : p < stopAt M a) :
    M.getD p (0,0) = (runAt M a).getD (p - (a + 1)) (0,0) := by
  unfold stopAt at hp2
  have hidx : p - (a + 1) < (runAt M a).length := by omega
  unfold runAt at hidx ⊢
  rw [prefix_getD_eq (List.takeWhile_prefix _) hidx, getD_drop]
  congr 1
  omega

/-- Run members sit strictly above the base level. -/
theorem run_region_gt {M : PairSeq} {a p : ℕ} (hp1 : a < p)
    (hp2 : p < stopAt M a) :
    (M.getD a (0,0)).1 < (M.getD p (0,0)).1 := by
  unfold stopAt at hp2
  have hidx : p - (a + 1) < (runAt M a).length := by omega
  have hmem : (runAt M a).getD (p - (a + 1)) (0,0) ∈ runAt M a := by
    rw [getD_eq_getElem' _ _ hidx]
    exact List.getElem_mem hidx
  have hpass := List.mem_takeWhile_imp hmem
  rw [getD_run_region hp1 hp2]
  simpa using hpass

theorem stopAt_col_le {M : PairSeq} {a : ℕ} (hs : stopAt M a < M.length) :
    (M.getD (stopAt M a) (0,0)).1 ≤ (M.getD a (0,0)).1 := by
  have hlen : (((M.drop (a + 1)).takeWhile
      fun r => decide ((M.getD a (0,0)).1 < r.1))).length
      < (M.drop (a + 1)).length := by
    unfold stopAt runAt at hs
    rw [List.length_drop]
    omega
  have hfail := stop_col_fails hlen
  rw [getD_drop] at hfail
  have hidx : a + 1 + ((M.drop (a + 1)).takeWhile
      fun r => decide ((M.getD a (0,0)).1 < r.1)).length = stopAt M a := rfl
  rw [hidx] at hfail
  simpa using hfail

/-- **HM⁺ survives truncation**: under the closure premise the stop column
survives, the runs coincide, and the interior runs are untouched. -/
theorem hmok_take {M : PairSeq} (h : hmok M) (m : ℕ) : hmok (M.take m) := by
  intro a ha hstop hclo p hp1 hp2
  rw [List.length_take] at ha hstop
  have ham : a < m := lt_of_lt_of_le ha (min_le_left _ _)
  have haM : a < M.length := lt_of_lt_of_le ha (min_le_right _ _)
  have hsm : stopAt (M.take m) a < m := lt_of_lt_of_le hstop (min_le_left _ _)
  have hrun : runAt (M.take m) a = runAt M a := runAt_take_eq ham hsm
  have hseq : stopAt (M.take m) a = stopAt M a := by
    unfold stopAt
    rw [hrun]
  have hsm' : stopAt M a < m := hseq ▸ hsm
  have hsM : stopAt M a < M.length :=
    hseq ▸ (lt_of_lt_of_le hstop (min_le_right _ _))
  rw [hseq] at hp2
  rw [getD_take hsm, hseq, getD_take ham] at hclo
  have hint := h a haM hsM hclo p hp1 hp2
  have hpm : p < m := by omega
  have hpfail : stopAt (M.take m) p < m := by
    rcases Nat.eq_or_lt_of_le hp1 with rfl | hpa'
    · exact hsm
    · have hidx : stopAt M a - (p + 1) < ((M.take m).drop (p + 1)).length := by
        rw [List.length_drop, List.length_take]
        omega
      have hcolfail : (fun r => decide (((M.take m).getD p (0,0)).1 < r.1))
          (((M.take m).drop (p + 1))[stopAt M a - (p + 1)]) = false := by
        have he : ((M.take m).drop (p + 1))[stopAt M a - (p + 1)]
            = M.getD (stopAt M a) (0,0) := by
          rw [← getD_eq_getElem' _ (0,0) hidx, getD_drop,
              show p + 1 + (stopAt M a - (p + 1)) = stopAt M a by omega,
              getD_take hsm']
        rw [he, getD_take hpm]
        simp only [decide_eq_false_iff_not, not_lt]
        exact le_trans (stopAt_col_le hsM) (le_of_lt (run_region_gt hpa' hp2))
      have hbound := takeWhile_length_le_of_fail
        (pr := fun r => decide (((M.take m).getD p (0,0)).1 < r.1)) hidx hcolfail
      unfold stopAt runAt
      omega
  rw [runAt_take_eq hpm hpfail]
  exact hint

theorem hmok_dropLast {M : PairSeq} (h : hmok M) : hmok M.dropLast := by
  rw [List.dropLast_eq_take]
  exact hmok_take h _

theorem hmok_Pred {M : PairSeq} (h : hmok M) : hmok (Pred M) := by
  unfold Pred
  by_cases hl : M.length ≤ 1
  · rw [if_pos hl]
    exact h
  · rw [if_neg hl]
    exact hmok_dropLast h


/-! ## The final-block discipline `tailok` -/

/-- Hereditary head-maximality of a standalone segment: the segment and
every dominated run inside it are head-maximal. -/
def hhm (S : PairSeq) : Prop :=
  headmax S ∧ ∀ p, p < S.length → headmax (runAt S p)

/-- **The final-block discipline** `tailok`: if the last column has a
parent, then — always when the parent row is 0, and under the trigger
(a block column at the last column's level with row-1 value at least the
parent's) when the parent row is 1 — the block between parent and last
column is hereditarily head-maximal.  (Mined exact: 0/543 for row 0,
0/265 for triggered row 1; general row-1 blocks fail 224/642, so the
trigger is essential.) -/
def tailok (M : PairSeq) : Prop :=
  ∀ j0, j0 + 1 < M.length →
    nextR M (idx1 M (M.length - 1)) j0 (M.length - 1) →
    (idx1 M (M.length - 1) = 1 →
      ∃ b, j0 < b ∧ b + 1 < M.length ∧
        (M.getD (M.length - 1) (0,0)).1 ≤ (M.getD b (0,0)).1 ∧
        (M.getD j0 (0,0)).2 ≤ (M.getD b (0,0)).2) →
    hhm ((M.take (M.length - 1)).drop (j0 + 1))

/-- On the diagonal the trigger is refutable: the block sits strictly below
the last column's level. -/
theorem tailok_diagSeq (v : ℕ) : tailok (diagSeq 0 v) := by
  intro j0 hj0 _hnext htrig
  rw [diagSeq0_length] at hj0
  have hv : 1 ≤ v := by omega
  have hi1 : idx1 (diagSeq 0 v) ((diagSeq 0 v).length - 1) = 1 := by
    have he : entry (diagSeq 0 v) 1 ((diagSeq 0 v).length - 1) = v := by
      unfold entry
      rw [if_neg one_ne_zero, diagSeq0_length, show v + 1 - 1 = v by omega,
          diagSeq0_getD (by omega)]
    unfold idx1
    rw [he, if_pos (by omega)]
  obtain ⟨b, hb1, hb2, hb3, -⟩ := htrig hi1
  rw [diagSeq0_length] at hb2 hb3
  rw [show v + 1 - 1 = v by omega, diagSeq0_getD (by omega),
      diagSeq0_getD (by omega)] at hb3
  have : v ≤ b := by simpa using hb3
  omega

/-- **The all-column block discipline** `tailokA` (mined exact, 0/440):
for every column `j` with a row-`idx1 j` parent `j0`, the block between
them is hereditarily head-maximal — unconditionally for row 0, under the
trigger for row 1. -/
def tailokA (M : PairSeq) : Prop :=
  ∀ j j0, j < M.length → j0 < j →
    nextR M (idx1 M j) j0 j →
    (idx1 M j = 1 →
      ∃ b, j0 < b ∧ b < j ∧
        (M.getD j (0,0)).1 ≤ (M.getD b (0,0)).1 ∧
        (M.getD j0 (0,0)).2 ≤ (M.getD b (0,0)).2) →
    hhm ((M.take j).drop (j0 + 1))

theorem tailokA_diagSeq (v : ℕ) : tailokA (diagSeq 0 v) := by
  intro j j0 hj hj0 _hnext htrig
  rw [diagSeq0_length] at hj
  have hj1 : 1 ≤ j := by omega
  have hi1 : idx1 (diagSeq 0 v) j = 1 := by
    have he : entry (diagSeq 0 v) 1 j = j := by
      unfold entry
      rw [if_neg one_ne_zero, diagSeq0_getD (by omega)]
    unfold idx1
    rw [he, if_pos (by omega)]
  obtain ⟨b, hb1, hb2, hb3, -⟩ := htrig hi1
  rw [diagSeq0_getD (by omega), diagSeq0_getD (by omega)] at hb3
  have : j ≤ b := by simpa using hb3
  omega

/-! ## Take-transfer for the parent relations -/

theorem entry_take {M : PairSeq} {m i j : ℕ} (h : j < m) :
    entry (M.take m) i j = entry M i j := by
  unfold entry
  rw [getD_take h]

theorem nextrel0_lt {M : PairSeq} {a b : ℕ} (h : nextrel0 M a b) : a < b :=
  h.2.2.1

theorem nextrel0_bound {M : PairSeq} {a b : ℕ} (h : nextrel0 M a b) :
    b < M.length := h.2.1

theorem nextrel0_take_iff {M : PairSeq} {m j0 j : ℕ} (hj : j < m)
    (hjM : j < M.length) :
    nextrel0 (M.take m) j0 j ↔ nextrel0 M j0 j := by
  unfold nextrel0
  rw [List.length_take]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨by omega, hjM, h3, ?_, ?_⟩
    · rwa [entry_take (by omega), entry_take hj] at h4
    · intro l hl
      have h6 := h5 l hl
      rwa [entry_take hj, entry_take (by omega)] at h6
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨by omega, by omega, h3, ?_, ?_⟩
    · rwa [entry_take (by omega), entry_take hj]
    · intro l hl
      have h6 := h5 l hl
      rwa [entry_take hj, entry_take (by omega)]

theorem rtg_nextrel0_of_take {M : PairSeq} {m : ℕ} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 (M.take m)) a b) :
    Relation.ReflTransGen (nextrel0 M) a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih =>
    have hb := nextrel0_bound hs
    rw [List.length_take] at hb
    exact ih.tail ((nextrel0_take_iff (by omega) (by omega)).1 hs)

theorem rtg_nextrel0_to_take {M : PairSeq} {m : ℕ} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 M) a b) (hb : b < m) :
    Relation.ReflTransGen (nextrel0 (M.take m)) a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hc hs ih =>
    have hlt := nextrel0_lt hs
    have hbM := nextrel0_bound hs
    exact (ih (by omega)).tail ((nextrel0_take_iff hb hbM).2 hs)

theorem le0_le {M : PairSeq} {a b : ℕ} (h : le0 M a b) : a ≤ b := by
  obtain ⟨-, -, hch⟩ := h
  induction hch with
  | refl => exact le_rfl
  | tail _ hs ih => exact le_trans ih (le_of_lt (nextrel0_lt hs))

theorem le0_take_iff {M : PairSeq} {m j0 j : ℕ} (hj : j < m)
    (hjM : j < M.length) :
    le0 (M.take m) j0 j ↔ le0 M j0 j := by
  unfold le0
  rw [List.length_take]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, hjM, rtg_nextrel0_of_take h3⟩
  · rintro ⟨h1, h2, h3⟩
    have hj0j : j0 ≤ j := le0_le ⟨h1, h2, h3⟩
    exact ⟨by omega, by omega, rtg_nextrel0_to_take h3 hj⟩

theorem nextrel1_take_iff {M : PairSeq} {m j0 j : ℕ} (hj : j < m)
    (hjM : j < M.length) :
    nextrel1 (M.take m) j0 j ↔ nextrel1 M j0 j := by
  unfold nextrel1
  rw [List.length_take]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨by omega, hjM, h3, ?_, (le0_take_iff hj hjM).1 h5, ?_⟩
    · rwa [entry_take (by omega), entry_take hj] at h4
    · intro l hl
      have hlj : l ≤ j := le0_le hl.2
      have h7 := h6 l ⟨hl.1, (le0_take_iff hj hjM).2 hl.2⟩
      rwa [entry_take hj, entry_take (by omega)] at h7
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨by omega, by omega, h3, ?_, (le0_take_iff hj hjM).2 h5, ?_⟩
    · rwa [entry_take (by omega), entry_take hj]
    · intro l hl
      have hl0 := (le0_take_iff hj hjM).1 hl.2
      have hlj : l ≤ j := le0_le hl0
      have h7 := h6 l ⟨hl.1, hl0⟩
      rwa [entry_take hj, entry_take (by omega)]

theorem idx1_take {M : PairSeq} {m j : ℕ} (h : j < m) :
    idx1 (M.take m) j = idx1 M j := by
  unfold idx1
  rw [entry_take h]

theorem nextR_take_iff {M : PairSeq} {m i j0 j : ℕ} (hj : j < m)
    (hjM : j < M.length) :
    nextR (M.take m) i j0 j ↔ nextR M i j0 j := by
  unfold nextR
  by_cases hi : i = 0
  · rw [if_pos hi, if_pos hi]
    exact nextrel0_take_iff hj hjM
  · rw [if_neg hi, if_neg hi]
    exact nextrel1_take_iff hj hjM

/-- `tailokA` is inherited by truncation: every instance is fully interior. -/
theorem tailokA_take {M : PairSeq} (h : tailokA M) (m : ℕ) :
    tailokA (M.take m) := by
  intro j j0 hj hj0 hnext htrig
  rw [List.length_take] at hj
  have hjm : j < m := lt_of_lt_of_le hj (min_le_left _ _)
  have hjM : j < M.length := lt_of_lt_of_le hj (min_le_right _ _)
  rw [idx1_take hjm, nextR_take_iff hjm hjM] at hnext
  have htrig' : idx1 M j = 1 →
      ∃ b, j0 < b ∧ b < j ∧
        (M.getD j (0,0)).1 ≤ (M.getD b (0,0)).1 ∧
        (M.getD j0 (0,0)).2 ≤ (M.getD b (0,0)).2 := by
    intro hi
    obtain ⟨b, hb1, hb2, hb3, hb4⟩ := htrig (by rwa [idx1_take hjm])
    refine ⟨b, hb1, hb2, ?_, ?_⟩
    · rwa [getD_take hjm, getD_take (by omega)] at hb3
    · rwa [getD_take (by omega), getD_take (by omega)] at hb4
  have hres := h j j0 hjM hj0 hnext htrig'
  have heq : ((M.take m).take j).drop (j0 + 1) = (M.take j).drop (j0 + 1) := by
    rw [List.take_take, min_eq_left (le_of_lt hjm)]
  rwa [heq]

theorem tailokA_dropLast {M : PairSeq} (h : tailokA M) : tailokA M.dropLast := by
  rw [List.dropLast_eq_take]
  exact tailokA_take h _

theorem tailokA_Pred {M : PairSeq} (h : tailokA M) : tailokA (Pred M) := by
  unfold Pred
  by_cases hl : M.length ≤ 1
  · rw [if_pos hl]
    exact h
  · rw [if_neg hl]
    exact tailokA_dropLast h


/-! ## H1: closures below the shared base transfer through the truncation -/

/-- Interior runs end no later than the closure stop. -/
theorem stopAt_interior_le {X : PairSeq} {a p : ℕ}
    (hstopX : stopAt X a < X.length) (hp1 : a ≤ p) (hp2 : p < stopAt X a) :
    stopAt X p ≤ stopAt X a := by
  rcases Nat.eq_or_lt_of_le hp1 with rfl | hpa
  · exact le_rfl
  · have hsfail : (X.getD (stopAt X a) (0,0)).1 ≤ (X.getD a (0,0)).1 :=
      stopAt_col_le hstopX
  
    have hgt : (X.getD a (0,0)).1 < (X.getD p (0,0)).1 :=
      run_region_gt hpa hp2
    have hidx : stopAt X a - (p + 1) < (X.drop (p + 1)).length := by
      rw [List.length_drop]
      omega
    have hfail : (fun r => decide ((X.getD p (0,0)).1 < r.1))
        ((X.drop (p + 1))[stopAt X a - (p + 1)]) = false := by
      have he : (X.drop (p + 1))[stopAt X a - (p + 1)]
          = X.getD (stopAt X a) (0,0) := by
        rw [← getD_eq_getElem' _ (0,0) hidx, getD_drop,
            show p + 1 + (stopAt X a - (p + 1)) = stopAt X a by omega]
      rw [he]
      simp only [decide_eq_false_iff_not, not_lt]
      omega
    have hbound0 := takeWhile_length_le_of_fail
      (pr := fun r => decide ((X.getD p (0,0)).1 < r.1)) hidx hfail
    have hbound : (runAt X p).length ≤ stopAt X a - (p + 1) := hbound0
    have h1 : stopAt X p = p + 1 + (runAt X p).length := rfl
    omega

/-- Conclusions of an `hmok` instance whose stop falls below `m` transfer
from `hmok` of the truncation. -/
theorem hmok_of_take {X : PairSeq} {m : ℕ} (hT : hmok (X.take m)) :
    ∀ a, a < X.length → stopAt X a < X.length → stopAt X a < m →
      (X.getD (stopAt X a) (0,0)).2 ≤ (X.getD a (0,0)).2 →
      ∀ p, a ≤ p → p < stopAt X a → headmax (runAt X p) := by
  intro a ha hstopX hstop hclo p hp1 hp2
  have ham : a < m := by
    unfold stopAt at hstop
    omega
  have hlen := runAt_take_length (M := X) (m := m) ham
  have hstopT : stopAt (X.take m) a < m := by
    unfold stopAt at hstop ⊢
    rw [hlen]
    omega
  have hrun : runAt (X.take m) a = runAt X a := runAt_take_eq ham hstopT
  have hseq : stopAt (X.take m) a = stopAt X a := by
    unfold stopAt
    rw [hrun]
  have hpm : p < m := by omega
  have hps : stopAt X p ≤ stopAt X a := stopAt_interior_le hstopX hp1 hp2
  have hplen := runAt_take_length (M := X) (m := m) hpm
  have hpstopT : stopAt (X.take m) p < m := by
    unfold stopAt at hps hstop ⊢
    rw [hplen]
    omega
  have hprun : runAt (X.take m) p = runAt X p := runAt_take_eq hpm hpstopT
  have hres := hT a (by rw [List.length_take]; omega)
    (by rw [List.length_take, hseq]; omega)
    (by rw [hseq, getD_take hstop, getD_take ham]; exact hclo)
    p hp1 (by rw [hseq]; exact hp2)
  rwa [hprun] at hres

/-- The shared base: `copyExp` and the host agree up to the end of copy 0. -/
theorem copyExp_take_base {G B : PairSeq} {lp : ℕ × ℕ} {d0 n : ℕ}
    (hn : 1 ≤ n) :
    (copyExp G B d0 n).take (G.length + B.length)
      = (G ++ B ++ [lp]).take (G.length + B.length) := by
  unfold copyExp
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [List.range_succ_eq_map, List.flatMap_cons]
  have hB0 : B.map (fun p => (p.1 + 0 * d0, p.2)) = B := by
    simp
  rw [hB0, ← List.append_assoc]
  rw [show G.length + B.length = (G ++ B).length by simp,
      List.take_left, List.take_left]


/-! ## Drop decomposition of the general copy region -/

theorem copies_map_drop {B : PairSeq} (f : ℕ → ℕ × ℕ → ℕ × ℕ) :
    ∀ (k n q : ℕ), k < n → q < B.length →
      ((List.range n).flatMap fun i => B.map (f i)).drop (k * B.length + (q + 1))
        = (B.map (f k)).drop (q + 1)
          ++ ((List.range (n - (k + 1))).flatMap fun i => B.map (f (i + (k + 1))))
  | 0, 0, q, hk, _ => absurd hk (by omega)
  | 0, n + 1, q, _, hq => by
    rw [List.range_succ_eq_map, List.flatMap_cons, Nat.zero_mul, Nat.zero_add,
        List.drop_append_of_le_length (by rw [List.length_map]; omega),
        List.flatMap_map]
    simp only [Nat.add_sub_cancel]
  | k + 1, 0, q, hk, _ => absurd hk (by omega)
  | k + 1, n + 1, q, hk, hq => by
    rw [List.range_succ_eq_map, List.flatMap_cons, List.drop_append,
        List.drop_eq_nil_of_le (by
          rw [List.length_map]
          calc B.length = 1 * B.length := (Nat.one_mul _).symm
          _ ≤ (k + 1) * B.length + (q + 1) := by
              have := Nat.mul_le_mul_right B.length (show 1 ≤ k + 1 by omega)
              omega),
        List.nil_append, List.length_map,
        show (k + 1) * B.length + (q + 1) - B.length
            = k * B.length + (q + 1) by
          rw [Nat.succ_mul]
          omega,
        List.flatMap_map]
    have hrec := copies_map_drop (B := B) (fun i => f (i + 1)) k n q (by omega) hq
    simp only [Nat.succ_eq_add_one]
    have hfn : (fun i => B.map (f (i + (k + 1 + 1))))
        = (fun i => B.map (f (i + (k + 1) + 1))) := by
      funext i
      congr 2
    rw [hfn, show n + 1 - (k + 1 + 1) = n - (k + 1) by omega]
    exact hrec


/-! ## Run characterization at copy positions -/

/-- The shifted-suffix takeWhile core shared by the run lemmas. -/
theorem takeWhile_shift_core (d : ℕ) (B : PairSeq) (q : ℕ) :
    ((B.map fun p => (p.1 + d, p.2)).drop (q + 1)).takeWhile
        (fun r => decide ((B.getD q (0,0)).1 + d < r.1))
      = (runAt B q).map fun p => (p.1 + d, p.2) := by
  rw [← List.map_drop, List.takeWhile_map]
  unfold runAt
  congr 1
  congr 1
  funext r
  simp only [Function.comp]
  exact decide_eq_decide.2 (by omega)

/-- The drop decomposition of `copyExp` at a copy position. -/
theorem copyExp_drop_at {G B : PairSeq} {d0 n k q : ℕ}
    (hk : k < n) (hq : q < B.length) :
    (copyExp G B d0 n).drop (G.length + (k * B.length + q) + 1)
      = (B.map fun p => (p.1 + k * d0, p.2)).drop (q + 1)
        ++ ((List.range (n - (k + 1))).flatMap
            fun i => B.map fun p => (p.1 + (i + (k + 1)) * d0, p.2)) := by
  unfold copyExp
  rw [show G.length + (k * B.length + q) + 1
        = G.length + (k * B.length + (q + 1)) by omega,
      List.drop_append, List.drop_eq_nil_of_le (by omega), List.nil_append,
      Nat.add_sub_cancel_left]
  exact copies_map_drop (fun i p => (p.1 + i * d0, p.2)) k n q hk hq

/-- **Within-copy runs are shifted block runs** (when the block run closes
inside the block). -/
theorem copyExp_runAt_within {G B : PairSeq} {d0 n k q : ℕ}
    (hk : k < n) (hq : q < B.length) (hin : stopAt B q < B.length) :
    runAt (copyExp G B d0 n) (G.length + (k * B.length + q))
      = (runAt B q).map fun p => (p.1 + k * d0, p.2) := by
  have hg1 : ((copyExp G B d0 n).getD (G.length + (k * B.length + q)) (0,0)).1
      = (B.getD q (0,0)).1 + k * d0 := by
    rw [copyExp_getD_copy hk hq]
  unfold runAt
  rw [hg1, copyExp_drop_at hk hq, List.takeWhile_append, if_neg,
      takeWhile_shift_core]
  · unfold runAt
    rfl
  · intro he
    rw [takeWhile_shift_core, List.length_map, List.length_drop,
        List.length_map] at he
    unfold stopAt at hin
    omega

/-- **Open block runs at copy positions above the next root stop exactly
there**: the run is the whole shifted block suffix. -/
theorem copyExp_runAt_root {G : PairSeq} {v0 w0 : ℕ} {R : PairSeq}
    {d0 n k q : ℕ} (hk : k < n) (hq : q < ((v0,w0) :: R).length)
    (hopen : ((v0,w0) :: R).length ≤ stopAt ((v0,w0) :: R) q)
    (hroot : v0 + d0 ≤ (((v0,w0) :: R).getD q (0,0)).1) :
    runAt (copyExp G ((v0,w0) :: R) d0 n) (G.length + (k * ((v0,w0) :: R).length + q))
      = (((v0,w0) :: R).drop (q + 1)).map fun p => (p.1 + k * d0, p.2) := by
  have hself : runAt ((v0,w0) :: R) q = ((v0,w0) :: R).drop (q + 1) := by
    have hle : (runAt ((v0,w0) :: R) q).length
        ≤ (((v0,w0) :: R).drop (q + 1)).length :=
      (List.takeWhile_sublist _).length_le
    have hlen : (runAt ((v0,w0) :: R) q).length
        = (((v0,w0) :: R).drop (q + 1)).length := by
      unfold stopAt at hopen
      rw [List.length_drop] at hle ⊢
      omega
    exact (List.takeWhile_prefix _).eq_of_length hlen
  have hg1 : ((copyExp G ((v0,w0) :: R) d0 n).getD
      (G.length + (k * ((v0,w0) :: R).length + q)) (0,0)).1
      = (((v0,w0) :: R).getD q (0,0)).1 + k * d0 := by
    rw [copyExp_getD_copy hk hq]
  unfold runAt
  rw [hg1, copyExp_drop_at hk hq,
      takeWhile_append_head_stop (by
        intro a ha
        cases hm : n - (k + 1) with
        | zero =>
          rw [hm] at ha
          simp at ha
        | succ m =>
          rw [hm, List.range_succ_eq_map, List.flatMap_cons,
              List.map_cons, List.cons_append] at ha
          simp only [List.head?_cons, Option.mem_some_iff] at ha
          subst ha
          simp only [decide_eq_false_iff_not, not_lt]
          show v0 + (0 + (k + 1)) * d0 ≤ (((v0,w0) :: R).getD q (0,0)).1 + k * d0
          have : (0 + (k + 1)) * d0 = k * d0 + d0 := by
            rw [Nat.zero_add, Nat.succ_mul]
          omega),
      takeWhile_shift_core, hself]


/-! ## Assembly helpers for `hmok` under the copy expansion -/

theorem maxr1_map_shift (d : ℕ) :
    ∀ L : PairSeq, maxr1 (L.map fun p => (p.1 + d, p.2)) = maxr1 L
  | [] => rfl
  | x :: L => by
    rw [List.map_cons, maxr1_cons]
    show max x.2 (maxr1 (L.map fun p => (p.1 + d, p.2))) = _
    rw [maxr1_map_shift d L, maxr1_cons]

/-- `headmax` is invariant under row-0 shifts. -/
theorem headmax_shift {K : PairSeq} {d : ℕ}
    (h : headmax K) : headmax (K.map fun p => (p.1 + d, p.2)) := by
  rcases h with rfl | h
  · exact Or.inl rfl
  · cases K with
    | nil => exact Or.inl rfl
    | cons k0 K' =>
      right
      show ((k0.1 + d, k0.2) :: K'.map fun p => (p.1 + d, p.2)).headI.2
        = maxr1 ((k0 :: K').map fun p => (p.1 + d, p.2))
      rw [List.headI_cons, maxr1_map_shift]
      rw [List.headI_cons] at h
      exact h

/-- The root's run inside the block is the whole dominated tail. -/
theorem runAt_root_block {v0 w0 : ℕ} {R : PairSeq}
    (hdom : ∀ x ∈ R, v0 < x.1) :
    runAt ((v0,w0) :: R) 0 = R := by
  rw [runAt_cons_zero]
  exact List.takeWhile_eq_self_iff.2 (by
    intro x hx
    simpa using hdom x hx)

/-- Host runs at block positions with an in-block stop are the block runs. -/
theorem hostM_runAt_within {G B : PairSeq} {lp : ℕ × ℕ} {q : ℕ}
    (hq : q < B.length) (hin : stopAt B q < B.length) :
    runAt (G ++ B ++ [lp]) (G.length + q) = runAt B q := by
  have hg1 : ((G ++ B ++ [lp]).getD (G.length + q) (0,0)).1
      = (B.getD q (0,0)).1 := by
    rw [hostM_getD_blk hq]
  have hdrop : (G ++ B ++ [lp]).drop (G.length + q + 1)
      = B.drop (q + 1) ++ [lp] := by
    rw [List.append_assoc, List.drop_append, List.drop_eq_nil_of_le (by omega),
        List.nil_append, show G.length + q + 1 - G.length = q + 1 by omega,
        List.drop_append_of_le_length (by omega)]
  unfold runAt
  rw [hg1, hdrop, List.takeWhile_append, if_neg]
  intro he
  have h2 : (runAt B q).length = (B.drop (q + 1)).length := he
  rw [List.length_drop] at h2
  unfold stopAt at hin
  omega

/-- When the block run is open and the next root is not low enough, the
copy-position run swallows the whole remainder: no stop exists. -/
theorem copyExp_stop_open {G : PairSeq} {v0 w0 : ℕ} {R : PairSeq}
    {d0 n k q : ℕ} (hk : k < n) (hq : q < ((v0,w0) :: R).length)
    (hdom : ∀ x ∈ R, v0 < x.1)
    (hopen : ((v0,w0) :: R).length ≤ stopAt ((v0,w0) :: R) q)
    (hnroot : (((v0,w0) :: R).getD q (0,0)).1 < v0 + d0) :
    stopAt (copyExp G ((v0,w0) :: R) d0 n)
        (G.length + (k * ((v0,w0) :: R).length + q))
      = (copyExp G ((v0,w0) :: R) d0 n).length := by
  have hself : runAt ((v0,w0) :: R) q = ((v0,w0) :: R).drop (q + 1) := by
    have hle : (runAt ((v0,w0) :: R) q).length
        ≤ (((v0,w0) :: R).drop (q + 1)).length :=
      (List.takeWhile_sublist _).length_le
    have hlen : (runAt ((v0,w0) :: R) q).length
        = (((v0,w0) :: R).drop (q + 1)).length := by
      unfold stopAt at hopen
      rw [List.length_drop] at hle ⊢
      omega
    exact (List.takeWhile_prefix _).eq_of_length hlen
  have hpass : ∀ y ∈ ((v0,w0) :: R).drop (q + 1),
      (((v0,w0) :: R).getD q (0,0)).1 < y.1 := by
    intro y hy
    rw [← hself] at hy
    have := List.mem_takeWhile_imp hy
    simpa using this
  have hg1 : ((copyExp G ((v0,w0) :: R) d0 n).getD
      (G.length + (k * ((v0,w0) :: R).length + q)) (0,0)).1
      = (((v0,w0) :: R).getD q (0,0)).1 + k * d0 := by
    rw [copyExp_getD_copy hk hq]
  have hbase : ∀ x ∈ ((v0,w0) :: R), v0 ≤ x.1 := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_rfl
    · exact le_of_lt (hdom x hx)
  have hrunself : runAt (copyExp G ((v0,w0) :: R) d0 n)
      (G.length + (k * ((v0,w0) :: R).length + q))
      = ((((v0,w0) :: R).map fun p => (p.1 + k * d0, p.2)).drop (q + 1))
        ++ ((List.range (n - (k + 1))).flatMap
            fun i => ((v0,w0) :: R).map fun p => (p.1 + (i + (k + 1)) * d0, p.2)) := by
    unfold runAt
    rw [hg1, copyExp_drop_at hk hq]
    apply List.takeWhile_eq_self_iff.2
    intro x hx
    simp only [decide_eq_true_eq]
    rcases List.mem_append.1 hx with hx | hx
    · rw [← List.map_drop] at hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
      have := hpass y hy
      omega
    · obtain ⟨i, hi, hx2⟩ := List.mem_flatMap.1 hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx2
      have h1 := hbase y hy
      have h2 : v0 + (i + (k + 1)) * d0 ≤ y.1 + (i + (k + 1)) * d0 := by omega
      have h3 : v0 + (k + 1) * d0 ≤ v0 + (i + (k + 1)) * d0 := by
        have := Nat.mul_le_mul_right d0 (show k + 1 ≤ i + (k + 1) by omega)
        omega
      have h4 : (k + 1) * d0 = k * d0 + d0 := Nat.succ_mul k d0
      show (((v0,w0) :: R).getD q (0,0)).1 + k * d0 < y.1 + (i + (k + 1)) * d0
      omega
  unfold stopAt
  rw [hrunself, copyExp_length, List.length_append, List.length_drop,
      List.length_map, copies_map_length]
  have h4 : (k + 1) * ((v0,w0) :: R).length
      = k * ((v0,w0) :: R).length + ((v0,w0) :: R).length :=
    Nat.succ_mul _ _
  have h5 : (k + 1 + (n - (k + 1))) * ((v0,w0) :: R).length
      = n * ((v0,w0) :: R).length := by
    congr 1
    omega
  rw [Nat.add_mul] at h5
  omega


/-! ## `hmok` survives the copy expansion -/

/-- All block runs are head-maximal under `hhm` of the dominated tail. -/
theorem headmax_runAt_block {v0 w0 : ℕ} {R : PairSeq}
    (hdom : ∀ x ∈ R, v0 < x.1) (hR : hhm R) :
    ∀ r, r < ((v0,w0) :: R).length → headmax (runAt ((v0,w0) :: R) r) := by
  intro r hr
  cases r with
  | zero =>
    rw [runAt_root_block hdom]
    exact hR.1
  | succ r' =>
    rw [runAt_cons_succ]
    exact hR.2 r' (by simpa using hr)

/-- **`hmok` survives the copy expansion**, given `hmok` of the host and the
final-block fact (conditioned on the trigger, which every next-root closure
supplies). -/
theorem hmok_copyExp {G : PairSeq} {v0 w0 : ℕ} {R : PairSeq} {lp : ℕ × ℕ}
    {d0 n : ℕ} (hn : 1 ≤ n)
    (hdom : ∀ x ∈ R, v0 < x.1)
    (hM : hmok (G ++ ((v0,w0) :: R) ++ [lp]))
    (htail : (∃ q, q < ((v0,w0) :: R).length
        ∧ v0 + d0 ≤ (((v0,w0) :: R).getD q (0,0)).1
        ∧ w0 ≤ (((v0,w0) :: R).getD q (0,0)).2) → hhm R) :
    hmok (copyExp G ((v0,w0) :: R) d0 n) := by
  have hL : 0 < ((v0,w0) :: R).length := by simp
  have hbaseL : ∀ x ∈ ((v0,w0) :: R), v0 ≤ x.1 := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact le_rfl
    · exact le_of_lt (hdom x hx)
  intro a ha hstop hclo p hp1 hp2
  rw [copyExp_length] at ha hstop
  by_cases hcase : stopAt (copyExp G ((v0,w0) :: R) d0 n) a
      < G.length + ((v0,w0) :: R).length
  · -- H1: the closure lives in the shared base
    have hbase := copyExp_take_base (G := G) (B := (v0,w0) :: R)
      (lp := lp) (d0 := d0) hn
    have hT : hmok ((copyExp G ((v0,w0) :: R) d0 n).take
        (G.length + ((v0,w0) :: R).length)) := by
      rw [hbase]
      exact hmok_take hM _
    exact hmok_of_take hT a (by rw [copyExp_length]; omega)
      (by rw [copyExp_length]; omega) hcase hclo p hp1 hp2
  · push Not at hcase
    -- the base lies in the copy region
    have hag : G.length ≤ a := by
      by_contra hcon
      push Not at hcon
      have h1 := run_region_gt (M := copyExp G ((v0,w0) :: R) d0 n)
        (a := a) (p := G.length) hcon (by omega)
      have hgv : ((copyExp G ((v0,w0) :: R) d0 n).getD G.length (0,0)).1 = v0 := by
        have h2 := copyExp_getD_copy (G := G) (B := (v0,w0) :: R)
          (d0 := d0) (n := n) (k := 0) (q := 0) (by omega) (by simp)
        rw [show G.length + (0 * ((v0,w0) :: R).length + 0) = G.length
              by omega] at h2
        rw [h2]
        simp
      have hsle := stopAt_col_le
        (M := copyExp G ((v0,w0) :: R) d0 n) (a := a)
        (by rw [copyExp_length]; omega)
      obtain ⟨ks, qs, hks, hqs, hdec⟩ := index_decomp hL
        (show stopAt (copyExp G ((v0,w0) :: R) d0 n) a - G.length
            < n * ((v0,w0) :: R).length by omega)
      have hslevel : v0 ≤ ((copyExp G ((v0,w0) :: R) d0 n).getD
          (stopAt (copyExp G ((v0,w0) :: R) d0 n) a) (0,0)).1 := by
        rw [show stopAt (copyExp G ((v0,w0) :: R) d0 n) a
              = G.length + (ks * ((v0,w0) :: R).length + qs) by omega,
            copyExp_getD_copy hks hqs]
        have := hbaseL _ (getD_mem hqs)
        omega
      rw [hgv] at h1
      omega
    obtain ⟨k', q, hk', hq, hadec⟩ := index_decomp hL
      (show a - G.length < n * ((v0,w0) :: R).length by omega)
    have haeq : a = G.length + (k' * ((v0,w0) :: R).length + q) := by omega
    subst haeq
    -- the interior offset of p
    have hple : p < stopAt (copyExp G ((v0,w0) :: R) d0 n)
        (G.length + (k' * ((v0,w0) :: R).length + q)) := hp2
    by_cases hin : stopAt ((v0,w0) :: R) q < ((v0,w0) :: R).length
    · -- H2: within-copy closure, inherited from the host block closure
      have hrun := copyExp_runAt_within (G := G) (d0 := d0) (n := n) hk' hq hin
      have hseq : stopAt (copyExp G ((v0,w0) :: R) d0 n)
          (G.length + (k' * ((v0,w0) :: R).length + q))
          = G.length + (k' * ((v0,w0) :: R).length + stopAt ((v0,w0) :: R) q) := by
        unfold stopAt
        rw [hrun, List.length_map]
        have : stopAt ((v0,w0) :: R) q = q + 1 + (runAt ((v0,w0) :: R) q).length :=
          rfl
        omega
      have hMrun := hostM_runAt_within (G := G) (lp := lp) hq hin
      have hMseq : stopAt (G ++ ((v0,w0) :: R) ++ [lp]) (G.length + q)
          = G.length + stopAt ((v0,w0) :: R) q := by
        unfold stopAt
        rw [hMrun]
        have : stopAt ((v0,w0) :: R) q = q + 1 + (runAt ((v0,w0) :: R) q).length :=
          rfl
        omega
      have hMlen : (G ++ ((v0,w0) :: R) ++ [lp]).length
          = G.length + ((v0,w0) :: R).length + 1 := hostM_length ..
      -- the closure premise transfers to the host
      have hcloM : ((G ++ ((v0,w0) :: R) ++ [lp]).getD
            (stopAt (G ++ ((v0,w0) :: R) ++ [lp]) (G.length + q)) (0,0)).2
          ≤ ((G ++ ((v0,w0) :: R) ++ [lp]).getD (G.length + q) (0,0)).2 := by
        rw [hMseq, hostM_getD_blk hin, hostM_getD_blk hq]
        rw [hseq, copyExp_getD_copy hk' hin, copyExp_getD_copy hk' hq] at hclo
        exact hclo
      -- offsets
      have hr : p - G.length - k' * ((v0,w0) :: R).length < ((v0,w0) :: R).length := by
        rw [hseq] at hple
        omega
      have hpeq : p = G.length
          + (k' * ((v0,w0) :: R).length
            + (p - G.length - k' * ((v0,w0) :: R).length)) := by omega
      have hrq : q ≤ p - G.length - k' * ((v0,w0) :: R).length := by omega
      have hrs : p - G.length - k' * ((v0,w0) :: R).length
          < stopAt ((v0,w0) :: R) q := by
        rw [hseq] at hple
        omega
      -- the host conclusion at the corresponding offset
      have hres := hM (G.length + q) (by omega)
        (by rw [hMseq]; omega) hcloM
        (G.length + (p - G.length - k' * ((v0,w0) :: R).length))
        (by omega) (by rw [hMseq]; omega)
      -- interior block runs close inside the block
      have hinr : stopAt ((v0,w0) :: R)
          (p - G.length - k' * ((v0,w0) :: R).length)
          ≤ stopAt ((v0,w0) :: R) q :=
        stopAt_interior_le (by omega) hrq hrs
      have hMrun' := hostM_runAt_within (G := G) (lp := lp) hr (by omega)
      have hXrun' := copyExp_runAt_within (G := G) (d0 := d0) (n := n)
        hk' hr (by omega)
      rw [hMrun'] at hres
      rw [hpeq, hXrun']
      exact headmax_shift hres
    · push Not at hin
      by_cases hroot : v0 + d0 ≤ (((v0,w0) :: R).getD q (0,0)).1
      · -- H3: next-root closure; the trigger is the base itself
        have hrun := copyExp_runAt_root (G := G) (n := n) hk' hq hin hroot
        have hseq : stopAt (copyExp G ((v0,w0) :: R) d0 n)
            (G.length + (k' * ((v0,w0) :: R).length + q))
            = G.length + (k' + 1) * ((v0,w0) :: R).length := by
          unfold stopAt
          rw [hrun, List.length_map, List.length_drop, Nat.succ_mul]
          omega
        have hk1n : k' + 1 < n := by
          by_contra hcon
          push Not at hcon
          have : n * ((v0,w0) :: R).length
              ≤ (k' + 1) * ((v0,w0) :: R).length :=
            Nat.mul_le_mul_right _ hcon
          omega
        have hw0 : w0 ≤ (((v0,w0) :: R).getD q (0,0)).2 := by
          rw [hseq, show G.length + (k' + 1) * ((v0,w0) :: R).length
                = G.length + ((k' + 1) * ((v0,w0) :: R).length + 0) by omega,
              copyExp_getD_copy hk1n (by simp),
              copyExp_getD_copy hk' hq] at hclo
          simpa using hclo
        have hhmR := htail ⟨q, hq, hroot, hw0⟩
        -- the interior offset
        have hr : p - G.length - k' * ((v0,w0) :: R).length
            < ((v0,w0) :: R).length := by
          rw [hseq, Nat.succ_mul] at hple
          omega
        have hpeq : p = G.length
            + (k' * ((v0,w0) :: R).length
              + (p - G.length - k' * ((v0,w0) :: R).length)) := by omega
        have hrq : q ≤ p - G.length - k' * ((v0,w0) :: R).length := by omega
        -- every interior block run is head-maximal
        have hhead := headmax_runAt_block hdom hhmR
          (p - G.length - k' * ((v0,w0) :: R).length) hr
        -- relate the X-run to the block run
        by_cases hin' : stopAt ((v0,w0) :: R)
            (p - G.length - k' * ((v0,w0) :: R).length) < ((v0,w0) :: R).length
        · have hXrun' := copyExp_runAt_within (G := G) (d0 := d0) (n := n)
            hk' hr hin'
          rw [hpeq, hXrun']
          exact headmax_shift hhead
        · push Not at hin'
          have hroot' : v0 + d0
              ≤ (((v0,w0) :: R).getD
                  (p - G.length - k' * ((v0,w0) :: R).length) (0,0)).1 := by
            rcases Nat.eq_or_lt_of_le hrq with heq | hlt
            · rw [← heq]
              exact hroot
            · have := run_region_gt (M := (v0,w0) :: R) (a := q)
                (p := p - G.length - k' * ((v0,w0) :: R).length) hlt (by omega)
              omega
          have hXrun' := copyExp_runAt_root (G := G) (n := n) hk' hr hin' hroot'
          have hself : runAt ((v0,w0) :: R)
              (p - G.length - k' * ((v0,w0) :: R).length)
              = ((v0,w0) :: R).drop
                  ((p - G.length - k' * ((v0,w0) :: R).length) + 1) := by
            have hle := (List.takeWhile_sublist
              (l := ((v0,w0) :: R).drop
                ((p - G.length - k' * ((v0,w0) :: R).length) + 1))
              (fun r => decide ((((v0,w0) :: R).getD
                (p - G.length - k' * ((v0,w0) :: R).length) (0,0)).1 < r.1))).length_le
            have hlen : (runAt ((v0,w0) :: R)
                (p - G.length - k' * ((v0,w0) :: R).length)).length
                = (((v0,w0) :: R).drop
                    ((p - G.length - k' * ((v0,w0) :: R).length) + 1)).length := by
              unfold stopAt at hin'
              rw [List.length_drop] at *
              have hb : (runAt ((v0,w0) :: R)
                  (p - G.length - k' * ((v0,w0) :: R).length)).length
                  ≤ ((v0,w0) :: R).length
                    - ((p - G.length - k' * ((v0,w0) :: R).length) + 1) := hle
              omega
            exact (List.takeWhile_prefix _).eq_of_length hlen
          rw [hpeq, hXrun', ← hself]
          exact headmax_shift hhead
      · -- excluded: the run never stops
        exfalso
        push Not at hroot
        have := copyExp_stop_open (G := G) (n := n) hk' hq hdom hin hroot
        rw [copyExp_length] at this
        omega

end YAPSS
