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

end YAPSS
