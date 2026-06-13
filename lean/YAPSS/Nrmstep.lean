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
    obtain ⟨G, v0, w0, R, d0, lp, hM, hX, hdom, _hlpgt, hd0, -⟩ :=
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
    rcases hd0 with ⟨hd00, -⟩ | ⟨hd0p, hwlt, hlpe, hnl1⟩
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

/-- **HM⁺ is preserved by the expansion step**, given the all-column block
discipline of the host. -/
theorem hmok_oper {M : PairSeq} {n : ℕ} (hn : 1 ≤ n) (hM : hmok M)
    (htl : tailok M) : hmok (M⟦n⟧) := by
  by_cases hL0 : M.length - 1 = 0
  · rw [oper_eq_self_of_short n hL0]
    exact hM
  by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0
  · rw [oper_eq_pred_of_zero n hL0 hz]
    exact hmok_Pred hM
  by_cases hp : hasParent M (idx1 M (M.length - 1)) (M.length - 1)
  case neg =>
    rw [oper_eq_pred_of_noParent n hL0 hz hp]
    exact hmok_Pred hM
  case pos =>
    obtain ⟨G, v0, w0, R, d0, lp, hMeq, hX, hdom, _hlpgt, hd0, hnxt⟩ :=
      oper_bad_blocks (by omega) hz hp hn
    rw [hX]
    show hmok (copyExp G ((v0,w0) :: R) d0 n)
    have hMlen : M.length = G.length + ((v0,w0) :: R).length + 1 := by
      rw [hMeq]
      exact hostM_length ..
    have hj1 : M.length - 1 = G.length + ((v0,w0) :: R).length := by omega
    refine hmok_copyExp hn hdom (hMeq ▸ hM) ?_
    rintro ⟨q, hq, hroot, hw0⟩
    have happ := htl G.length (by omega) hnxt ?_
    · have htake : M.take (M.length - 1) = G ++ ((v0,w0) :: R) := by
        rw [hj1, hMeq,
            show G.length + ((v0,w0) :: R).length
              = (G ++ ((v0,w0) :: R)).length by simp,
            List.take_left]
      rw [htake] at happ
      have hdrop : (G ++ ((v0,w0) :: R)).drop (G.length + 1) = R := by
        rw [List.drop_append, List.drop_eq_nil_of_le (by omega),
            List.nil_append, show G.length + 1 - G.length = 1 by omega,
            List.drop_succ_cons, List.drop_zero]
      rwa [hdrop] at happ
    · intro hi1
      rcases hd0 with ⟨-, hi0⟩ | ⟨hd0p, -, hlpe, -⟩
      · rw [hi1] at hi0
        exact absurd hi0 one_ne_zero
      · have hq1 : 1 ≤ q := by
          by_contra hq0
          push Not at hq0
          have : q = 0 := by omega
          subst this
          rw [List.getD_cons_zero] at hroot
          simp at hroot
          omega
        refine ⟨G.length + q, by omega, by omega, ?_, ?_⟩
        · have h1 : M.getD (M.length - 1) (0,0) = lp := by
            rw [hj1, hMeq]
            exact hostM_getD_lp
          have h2 : M.getD (G.length + q) (0,0) = ((v0,w0) :: R).getD q (0,0) := by
            rw [hMeq]
            exact hostM_getD_blk hq
          rw [h1, h2, hlpe]
          exact hroot
        · have h3 : M.getD G.length (0,0) = (v0, w0) := by
            have h := hostM_getD_blk (G := G) (lp := lp)
              (show 0 < ((v0,w0) :: R).length by simp)
            rw [Nat.add_zero] at h
            rw [hMeq, h, List.getD_cons_zero]
          have h2 : M.getD (G.length + q) (0,0) = ((v0,w0) :: R).getD q (0,0) := by
            rw [hMeq]
            exact hostM_getD_blk hq
          rw [h3, h2]
          exact hw0


/-! ## Wholesale instance transfer below a shared truncation -/

theorem nextR_eq_of_take_eq {X Y : PairSeq} {m i j0 j : ℕ}
    (hXY : X.take m = Y.take m) (hj : j < m) (hjX : j < X.length)
    (hjY : j < Y.length) : nextR X i j0 j ↔ nextR Y i j0 j := by
  rw [← nextR_take_iff (M := X) hj hjX, hXY, nextR_take_iff (M := Y) hj hjY]

theorem idx1_eq_of_take_eq {X Y : PairSeq} {m j : ℕ}
    (hXY : X.take m = Y.take m) (hj : j < m) : idx1 X j = idx1 Y j := by
  rw [← idx1_take (M := X) hj, hXY, idx1_take (M := Y) hj]

theorem getD_eq_of_take_eq {X Y : PairSeq} {m j : ℕ}
    (hXY : X.take m = Y.take m) (hj : j < m) :
    X.getD j (0,0) = Y.getD j (0,0) := by
  rw [← getD_take (M := X) hj, hXY, getD_take (M := Y) hj]

/-- `tailokA` instances below a shared truncation transfer wholesale. -/
theorem tailokA_of_take_eq {X Y : PairSeq} {m : ℕ}
    (hXY : X.take m = Y.take m) (htA : tailokA Y) :
    ∀ j j0, j < m → j < X.length → j < Y.length → j0 < j →
      nextR X (idx1 X j) j0 j →
      (idx1 X j = 1 → ∃ b, j0 < b ∧ b < j ∧
        (X.getD j (0,0)).1 ≤ (X.getD b (0,0)).1 ∧
        (X.getD j0 (0,0)).2 ≤ (X.getD b (0,0)).2) →
      hhm ((X.take j).drop (j0 + 1)) := by
  intro j j0 hjm hjX hjY hj0 hnx htrig
  rw [idx1_eq_of_take_eq hXY hjm] at hnx htrig
  rw [nextR_eq_of_take_eq hXY hjm hjX hjY] at hnx
  have htrig' : idx1 Y j = 1 → ∃ b, j0 < b ∧ b < j ∧
      (Y.getD j (0,0)).1 ≤ (Y.getD b (0,0)).1 ∧
      (Y.getD j0 (0,0)).2 ≤ (Y.getD b (0,0)).2 := by
    intro h1
    obtain ⟨b, hb1, hb2, hb3, hb4⟩ := htrig h1
    refine ⟨b, hb1, hb2, ?_, ?_⟩
    · rwa [getD_eq_of_take_eq (j := j) hXY hjm,
        getD_eq_of_take_eq (j := b) hXY (by omega)] at hb3
    · rwa [getD_eq_of_take_eq (j := j0) hXY (by omega),
        getD_eq_of_take_eq (j := b) hXY (by omega)] at hb4
  have happ := htA j j0 hjY hj0 hnx htrig'
  have htk : X.take j = Y.take j := by
    have h1 : X.take j = (X.take m).take j := by
      rw [List.take_take, min_eq_left (by omega)]
    have h2 : Y.take j = (Y.take m).take j := by
      rw [List.take_take, min_eq_left (by omega)]
    rw [h1, h2, hXY]
  rwa [htk]


/-! ## Within-copy parenthood transfer -/

/-- Entry values at copy positions. -/
theorem entry_copyExp {G B : PairSeq} {d0 n k q : ℕ}
    (hk : k < n) (hq : q < B.length) :
    entry (copyExp G B d0 n) 0 (G.length + (k * B.length + q))
      = (B.getD q (0,0)).1 + k * d0
    ∧ entry (copyExp G B d0 n) 1 (G.length + (k * B.length + q))
      = (B.getD q (0,0)).2 := by
  unfold entry
  rw [if_pos rfl, if_neg one_ne_zero, copyExp_getD_copy hk hq]
  exact ⟨rfl, rfl⟩

/-- Within-copy row-0 parenthood is the shifted host-block parenthood. -/
theorem nextrel0_copy_iff {G B : PairSeq} {lp : ℕ × ℕ} {d0 n k q0 q : ℕ}
    (hk : k < n) (hq : q < B.length) (hq0 : q0 < q) :
    nextrel0 (copyExp G B d0 n)
        (G.length + (k * B.length + q0)) (G.length + (k * B.length + q))
      ↔ nextrel0 (G ++ B ++ [lp]) (G.length + q0) (G.length + q) := by
  have hq0B : q0 < B.length := by omega
  have hXlen : (copyExp G B d0 n).length = G.length + n * B.length :=
    copyExp_length ..
  have hMlen : (G ++ B ++ [lp]).length = G.length + B.length + 1 :=
    hostM_length ..
  have hkL : k * B.length + B.length ≤ n * B.length := by
    have := Nat.mul_le_mul_right B.length (show k + 1 ≤ n by omega)
    rw [Nat.succ_mul] at this
    omega
  have he0 : ∀ {r}, r < B.length →
      entry (copyExp G B d0 n) 0 (G.length + (k * B.length + r))
        = (B.getD r (0,0)).1 + k * d0 := fun hr => (entry_copyExp hk hr).1
  have heM : ∀ {r}, r < B.length →
      entry (G ++ B ++ [lp]) 0 (G.length + r) = (B.getD r (0,0)).1 := by
    intro r hr
    unfold entry
    rw [if_pos rfl, hostM_getD_blk hr]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨by omega, by omega, by omega, ?_, ?_⟩
    · rw [heM hq0B, heM hq]
      rw [he0 hq0B, he0 hq] at h4
      omega
    · intro l hl
      have hloff : l - G.length < B.length := by omega
      have hleq : l = G.length + (l - G.length) := by omega
      have hX := h5 (G.length + (k * B.length + (l - G.length)))
        (by constructor <;> omega)
      rw [he0 hq, he0 hloff] at hX
      rw [hleq, heM hq, heM hloff]
      omega
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨by omega, by omega, by omega, ?_, ?_⟩
    · rw [he0 hq0B, he0 hq]
      rw [heM hq0B, heM hq] at h4
      omega
    · intro l hl
      have hloff : l - G.length - k * B.length < B.length := by omega
      have hleq : l = G.length + (k * B.length
          + (l - G.length - k * B.length)) := by omega
      have hM := h5 (G.length + (l - G.length - k * B.length))
        (by constructor <;> omega)
      rw [heM hq, heM hloff] at hM
      rw [hleq, he0 hq, he0 hloff]
      omega

/-- A row-0 parent of a non-root copy column lies at or after the copy
root: the root itself dips below the column's level. -/
theorem nextrel0_into_copy {G : PairSeq} {v0 w0 : ℕ} {R : PairSeq}
    {d0 n k q j0X : ℕ} (hk : k < n) (hq : q < ((v0,w0) :: R).length)
    (hq1 : 1 ≤ q) (hdom : ∀ x ∈ R, v0 < x.1)
    (h : nextrel0 (copyExp G ((v0,w0) :: R) d0 n) j0X
      (G.length + (k * ((v0,w0) :: R).length + q))) :
    G.length + k * ((v0,w0) :: R).length ≤ j0X := by
  by_contra hcon
  push Not at hcon
  obtain ⟨-, -, -, -, h5⟩ := h
  have hroot := h5 (G.length + (k * ((v0,w0) :: R).length + 0))
    (by constructor <;> omega)
  have he1 := (entry_copyExp (G := G) (B := (v0,w0) :: R) (d0 := d0)
    hk hq).1
  have he2 := (entry_copyExp (G := G) (B := (v0,w0) :: R) (d0 := d0)
    hk (show 0 < ((v0,w0) :: R).length by simp)).1
  rw [he1, he2] at hroot
  rw [List.getD_cons_zero] at hroot
  -- the column's level strictly exceeds the root's
  have hgt : v0 < (((v0,w0) :: R).getD q (0,0)).1 := by
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [List.getD_cons_succ]
    exact hdom _ (getD_mem (by simpa using hq))
  have hroot' : (((v0,w0) :: R).getD q (0,0)).1 + k * d0
      ≤ v0 + k * d0 := hroot
  omega


/-! ## Segment extraction at copy positions -/

theorem hhm_shift {S : PairSeq} {d : ℕ} (h : hhm S) :
    hhm (S.map fun p => (p.1 + d, p.2)) := by
  constructor
  · exact headmax_shift h.1
  · intro p hp
    rw [List.length_map] at hp
    have hr := runAt_shiftr0 d S hp
    rw [show (S.map fun p => (p.1 + d, p.2)) = shiftr0 d S from rfl, hr]
    exact headmax_shift (h.2 p hp)

theorem copyExp_split (G B : PairSeq) (d0 : ℕ) {k n : ℕ} (hk : k ≤ n) :
    copyExp G B d0 n = copyExp G B d0 k
      ++ ((List.range (n - k)).flatMap
          fun i => B.map fun p => (p.1 + (k + i) * d0, p.2)) := by
  unfold copyExp
  rw [show n = k + (n - k) by omega, List.range_add, List.flatMap_append,
      List.flatMap_map, ← List.append_assoc,
      show k + (n - k) - k = n - k by omega]

theorem copyExp_take_at {G B : PairSeq} {d0 n k q : ℕ}
    (hk : k < n) (hq : q ≤ B.length) :
    (copyExp G B d0 n).take (G.length + (k * B.length + q))
      = copyExp G B d0 k ++ (B.map fun p => (p.1 + k * d0, p.2)).take q := by
  rw [copyExp_split G B d0 (le_of_lt hk)]
  have hlen : (copyExp G B d0 k).length = G.length + k * B.length :=
    copyExp_length ..
  rw [List.take_append, List.take_of_length_le (by rw [hlen]; omega), hlen,
      show G.length + (k * B.length + q) - (G.length + k * B.length) = q
        by omega]
  obtain ⟨m, hm⟩ : ∃ m, n - k = m + 1 := ⟨n - k - 1, by omega⟩
  rw [hm, List.range_succ_eq_map, List.flatMap_cons,
      List.take_append_of_le_length (by rw [List.length_map]; omega),
      Nat.add_zero]


/-! ## Within-copy row-0 instances of `tailokA` -/

theorem hostM_take_at {G B : PairSeq} {lp : ℕ × ℕ} {q : ℕ}
    (hq : q ≤ B.length) :
    (G ++ B ++ [lp]).take (G.length + q) = G ++ B.take q := by
  rw [List.append_assoc, List.take_append,
      List.take_of_length_le (by omega),
      show G.length + q - G.length = q by omega,
      List.take_append_of_le_length hq]

theorem idx1_copy {G B : PairSeq} {lp : ℕ × ℕ} {d0 n k q : ℕ}
    (hk : k < n) (hq : q < B.length) :
    idx1 (copyExp G B d0 n) (G.length + (k * B.length + q))
      = idx1 (G ++ B ++ [lp]) (G.length + q) := by
  unfold idx1
  rw [(entry_copyExp hk hq).2]
  unfold entry
  rw [if_neg one_ne_zero, hostM_getD_blk hq]

/-- The within-copy row-0 instances of `tailokA` transfer from the host. -/
theorem tailokA_copyExp_row0 {G : PairSeq} {v0 w0 : ℕ} {R : PairSeq}
    {lp : ℕ × ℕ} {d0 n k q j0X : ℕ}
    (htA : tailokA (G ++ ((v0,w0) :: R) ++ [lp]))
    (hdom : ∀ x ∈ R, v0 < x.1)
    (hk : k < n) (hq : q < ((v0,w0) :: R).length) (hq1 : 1 ≤ q)
    (hi0 : idx1 (copyExp G ((v0,w0) :: R) d0 n)
      (G.length + (k * ((v0,w0) :: R).length + q)) = 0)
    (hnx : nextrel0 (copyExp G ((v0,w0) :: R) d0 n) j0X
      (G.length + (k * ((v0,w0) :: R).length + q))) :
    hhm (((copyExp G ((v0,w0) :: R) d0 n).take
        (G.length + (k * ((v0,w0) :: R).length + q))).drop (j0X + 1)) := by
  have hge := nextrel0_into_copy hk hq hq1 hdom hnx
  have hlt := nextrel0_lt hnx
  have hq0 : j0X - G.length - k * ((v0,w0) :: R).length < q := by omega
  have hjeq : j0X = G.length + (k * ((v0,w0) :: R).length
      + (j0X - G.length - k * ((v0,w0) :: R).length)) := by omega
  rw [hjeq] at hnx
  have hM0 : nextrel0 (G ++ ((v0,w0) :: R) ++ [lp])
      (G.length + (j0X - G.length - k * ((v0,w0) :: R).length))
      (G.length + q) := (nextrel0_copy_iff hk hq hq0).1 hnx
  have hiM : idx1 (G ++ ((v0,w0) :: R) ++ [lp]) (G.length + q) = 0 := by
    rw [← idx1_copy (d0 := d0) (n := n) hk hq]
    exact hi0
  have hMlen : (G ++ ((v0,w0) :: R) ++ [lp]).length
      = G.length + ((v0,w0) :: R).length + 1 := hostM_length ..
  have happ := htA (G.length + q)
    (G.length + (j0X - G.length - k * ((v0,w0) :: R).length))
    (by omega) (by omega)
    (by unfold nextR; rw [hiM, if_pos rfl]; exact hM0)
    (by
      intro h1
      rw [hiM] at h1
      exact absurd h1 (by omega))
  have hMtake : ((G ++ ((v0,w0) :: R) ++ [lp]).take (G.length + q)).drop
      (G.length + (j0X - G.length - k * ((v0,w0) :: R).length) + 1)
      = (((v0,w0) :: R).take q).drop
          ((j0X - G.length - k * ((v0,w0) :: R).length) + 1) := by
    rw [hostM_take_at (le_of_lt hq), List.drop_append,
        List.drop_eq_nil_of_le (by omega), List.nil_append,
        show G.length + (j0X - G.length - k * ((v0,w0) :: R).length) + 1
            - G.length
          = (j0X - G.length - k * ((v0,w0) :: R).length) + 1 by omega]
  have hXtake : ((copyExp G ((v0,w0) :: R) d0 n).take
        (G.length + (k * ((v0,w0) :: R).length + q))).drop (j0X + 1)
      = ((((v0,w0) :: R).take q).drop
          ((j0X - G.length - k * ((v0,w0) :: R).length) + 1)).map
            fun p => (p.1 + k * d0, p.2) := by
    rw [copyExp_take_at hk (le_of_lt hq), List.drop_append,
        List.drop_eq_nil_of_le (by rw [copyExp_length]; omega),
        List.nil_append, copyExp_length,
        show j0X + 1 - (G.length + k * ((v0,w0) :: R).length)
          = (j0X - G.length - k * ((v0,w0) :: R).length) + 1 by omega,
        ← List.map_take, ← List.map_drop]
  rw [hXtake]
  rw [hMtake] at happ
  exact hhm_shift happ


/-! ## Chain lifts between the host block and a copy -/

theorem rtg_nextrel0_le {W : PairSeq} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 W) a b) : a ≤ b := by
  induction h with
  | refl => exact le_rfl
  | tail _ hs ih => exact le_trans ih (le_of_lt (nextrel0_lt hs))

/-- Host-block chains lift to within-copy chains. -/
theorem rtg_copy_of_host {G : PairSeq} {v0 w0 : ℕ} {R : PairSeq}
    {lp : ℕ × ℕ} {d0 n k : ℕ} (hk : k < n) {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 (G ++ ((v0,w0) :: R) ++ [lp])) a b)
    (ha : G.length ≤ a) (hb : b < G.length + ((v0,w0) :: R).length) :
    Relation.ReflTransGen (nextrel0 (copyExp G ((v0,w0) :: R) d0 n))
      (a + k * ((v0,w0) :: R).length) (b + k * ((v0,w0) :: R).length) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c e hchain hstep ih =>
    have hac : a ≤ c := rtg_nextrel0_le hchain
    have hce : c < e := nextrel0_lt hstep
    have hstepX : nextrel0 (copyExp G ((v0,w0) :: R) d0 n)
        (c + k * ((v0,w0) :: R).length) (e + k * ((v0,w0) :: R).length) := by
      have h1 : c = G.length + (c - G.length) := by omega
      have h2 : e = G.length + (e - G.length) := by omega
      rw [h1, h2] at hstep
      have h3 := (nextrel0_copy_iff (d0 := d0) (n := n) hk
        (show e - G.length < ((v0,w0) :: R).length by omega)
        (show c - G.length < e - G.length by omega)).2 hstep
      rw [show G.length + (k * ((v0,w0) :: R).length + (c - G.length))
            = c + k * ((v0,w0) :: R).length by omega,
          show G.length + (k * ((v0,w0) :: R).length + (e - G.length))
            = e + k * ((v0,w0) :: R).length by omega] at h3
      exact h3
    exact (ih (by omega)).tail hstepX

/-- Within-copy chains project to host-block chains. -/
theorem rtg_host_of_copy {G : PairSeq} {v0 w0 : ℕ} {R : PairSeq}
    {lp : ℕ × ℕ} {d0 n k : ℕ} (hk : k < n) {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 (copyExp G ((v0,w0) :: R) d0 n)) a b)
    (ha : G.length + k * ((v0,w0) :: R).length ≤ a)
    (hb : b < G.length + k * ((v0,w0) :: R).length + ((v0,w0) :: R).length) :
    Relation.ReflTransGen (nextrel0 (G ++ ((v0,w0) :: R) ++ [lp]))
      (a - k * ((v0,w0) :: R).length) (b - k * ((v0,w0) :: R).length) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c e hchain hstep ih =>
    have hac : a ≤ c := rtg_nextrel0_le hchain
    have hce : c < e := nextrel0_lt hstep
    have hstepM : nextrel0 (G ++ ((v0,w0) :: R) ++ [lp])
        (c - k * ((v0,w0) :: R).length) (e - k * ((v0,w0) :: R).length) := by
      have h1 : c = G.length + (k * ((v0,w0) :: R).length
          + (c - G.length - k * ((v0,w0) :: R).length)) := by omega
      have h2 : e = G.length + (k * ((v0,w0) :: R).length
          + (e - G.length - k * ((v0,w0) :: R).length)) := by omega
      rw [h1, h2] at hstep
      have h3 := (nextrel0_copy_iff (lp := lp) hk
        (show e - G.length - k * ((v0,w0) :: R).length < ((v0,w0) :: R).length
          by omega)
        (show c - G.length - k * ((v0,w0) :: R).length
            < e - G.length - k * ((v0,w0) :: R).length by omega)).1 hstep
      rw [show G.length + (c - G.length - k * ((v0,w0) :: R).length)
            = c - k * ((v0,w0) :: R).length by omega,
          show G.length + (e - G.length - k * ((v0,w0) :: R).length)
            = e - k * ((v0,w0) :: R).length by omega] at h3
      exact h3
    exact (ih (by omega)).tail hstepM

/-- The within-copy row-1 instances of `tailokA` transfer from the host:
above the copy root, ancestry and maximality are in exact correspondence. -/
theorem tailokA_copyExp_row1 {G : PairSeq} {v0 w0 : ℕ} {R : PairSeq}
    {lp : ℕ × ℕ} {d0 n k q j0X : ℕ}
    (htA : tailokA (G ++ ((v0,w0) :: R) ++ [lp]))
    (hk : k < n) (hq : q < ((v0,w0) :: R).length)
    (hi1 : idx1 (copyExp G ((v0,w0) :: R) d0 n)
      (G.length + (k * ((v0,w0) :: R).length + q)) = 1)
    (hnx : nextrel1 (copyExp G ((v0,w0) :: R) d0 n) j0X
      (G.length + (k * ((v0,w0) :: R).length + q)))
    (hge : G.length + k * ((v0,w0) :: R).length ≤ j0X)
    (htrig : ∃ b, j0X < b ∧ b < G.length + (k * ((v0,w0) :: R).length + q) ∧
      ((copyExp G ((v0,w0) :: R) d0 n).getD
          (G.length + (k * ((v0,w0) :: R).length + q)) (0,0)).1
        ≤ ((copyExp G ((v0,w0) :: R) d0 n).getD b (0,0)).1 ∧
      ((copyExp G ((v0,w0) :: R) d0 n).getD j0X (0,0)).2
        ≤ ((copyExp G ((v0,w0) :: R) d0 n).getD b (0,0)).2) :
    hhm (((copyExp G ((v0,w0) :: R) d0 n).take
        (G.length + (k * ((v0,w0) :: R).length + q))).drop (j0X + 1)) := by
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ := hnx
  have hq0 : j0X - G.length - k * ((v0,w0) :: R).length < q := by omega
  have hq0B : j0X - G.length - k * ((v0,w0) :: R).length
      < ((v0,w0) :: R).length := by omega
  have hMlen : (G ++ ((v0,w0) :: R) ++ [lp]).length
      = G.length + ((v0,w0) :: R).length + 1 := hostM_length ..
  have hXlen : (copyExp G ((v0,w0) :: R) d0 n).length
      = G.length + n * ((v0,w0) :: R).length := copyExp_length ..
  have he1 : ∀ {r}, r < ((v0,w0) :: R).length →
      entry (copyExp G ((v0,w0) :: R) d0 n) 1
        (G.length + (k * ((v0,w0) :: R).length + r))
      = (((v0,w0) :: R).getD r (0,0)).2 :=
    fun hr => (entry_copyExp hk hr).2
  have heM1 : ∀ {r}, r < ((v0,w0) :: R).length →
      entry (G ++ ((v0,w0) :: R) ++ [lp]) 1 (G.length + r)
        = (((v0,w0) :: R).getD r (0,0)).2 := by
    intro r hr
    unfold entry
    rw [if_neg one_ne_zero, hostM_getD_blk hr]
  have hj0eq : j0X = G.length + (k * ((v0,w0) :: R).length
      + (j0X - G.length - k * ((v0,w0) :: R).length)) := by omega
  -- the host parenthood
  have hM1 : nextrel1 (G ++ ((v0,w0) :: R) ++ [lp])
      (G.length + (j0X - G.length - k * ((v0,w0) :: R).length))
      (G.length + q) := by
    refine ⟨by omega, by omega, by omega, ?_, ?_, ?_⟩
    · rw [heM1 hq0B, heM1 hq]
      rw [hj0eq] at hb4
      rw [he1 hq0B, he1 hq] at hb4
      exact hb4
    · obtain ⟨-, -, hchain⟩ := hb5
      refine ⟨by omega, by omega, ?_⟩
      have hlift := rtg_host_of_copy (lp := lp) hk hchain
        (by omega) (by omega)
      rw [show j0X - k * ((v0,w0) :: R).length
            = G.length + (j0X - G.length - k * ((v0,w0) :: R).length)
            by omega,
          show G.length + (k * ((v0,w0) :: R).length + q)
              - k * ((v0,w0) :: R).length = G.length + q by omega] at hlift
      exact hlift
    · intro j' hj'
      obtain ⟨hj'gt, hj'le0⟩ := hj'
      have hj'le : j' ≤ G.length + q := le0_le hj'le0
      obtain ⟨-, -, hchain⟩ := hj'le0
      have hlift := rtg_copy_of_host (d0 := d0) (n := n) hk hchain
        (by omega) (by omega)
      rw [show G.length + q + k * ((v0,w0) :: R).length
            = G.length + (k * ((v0,w0) :: R).length + q) by omega] at hlift
      have hX := hb6 (j' + k * ((v0,w0) :: R).length)
        ⟨by omega, by omega, by omega, hlift⟩
      rw [he1 hq] at hX
      rw [show j' + k * ((v0,w0) :: R).length
            = G.length + (k * ((v0,w0) :: R).length + (j' - G.length))
            by omega,
          he1 (show j' - G.length < ((v0,w0) :: R).length by omega)] at hX
      rw [heM1 hq, show j' = G.length + (j' - G.length) by omega,
          heM1 (show j' - G.length < ((v0,w0) :: R).length by omega)]
      exact hX
  have hiM : idx1 (G ++ ((v0,w0) :: R) ++ [lp]) (G.length + q) = 1 := by
    rw [← idx1_copy (d0 := d0) (n := n) hk hq]
    exact hi1
  -- the host trigger
  have htrigM : idx1 (G ++ ((v0,w0) :: R) ++ [lp]) (G.length + q) = 1 →
      ∃ b, G.length + (j0X - G.length - k * ((v0,w0) :: R).length) < b
        ∧ b < G.length + q
        ∧ ((G ++ ((v0,w0) :: R) ++ [lp]).getD (G.length + q) (0,0)).1
            ≤ ((G ++ ((v0,w0) :: R) ++ [lp]).getD b (0,0)).1
        ∧ ((G ++ ((v0,w0) :: R) ++ [lp]).getD
              (G.length + (j0X - G.length - k * ((v0,w0) :: R).length)) (0,0)).2
            ≤ ((G ++ ((v0,w0) :: R) ++ [lp]).getD b (0,0)).2 := by
    intro _
    obtain ⟨b, hbb1, hbb2, hbb3, hbb4⟩ := htrig
    have hrb : b - G.length - k * ((v0,w0) :: R).length
        < ((v0,w0) :: R).length := by omega
    have hbeq : b = G.length + (k * ((v0,w0) :: R).length
        + (b - G.length - k * ((v0,w0) :: R).length)) := by omega
    refine ⟨G.length + (b - G.length - k * ((v0,w0) :: R).length),
      by omega, by omega, ?_, ?_⟩
    · rw [hostM_getD_blk hq, hostM_getD_blk hrb]
      rw [hbeq, copyExp_getD_copy hk hq, copyExp_getD_copy hk hrb] at hbb3
      have hbb3' : (((v0,w0) :: R).getD q (0,0)).1 + k * d0
          ≤ (((v0,w0) :: R).getD
              (b - G.length - k * ((v0,w0) :: R).length) (0,0)).1 + k * d0 :=
        hbb3
      omega
    · rw [hostM_getD_blk hq0B, hostM_getD_blk hrb]
      rw [hbeq, hj0eq, copyExp_getD_copy hk hq0B,
          copyExp_getD_copy hk hrb] at hbb4
      exact hbb4
  have happ := htA (G.length + q)
    (G.length + (j0X - G.length - k * ((v0,w0) :: R).length))
    (by omega) (by omega)
    (by unfold nextR; rw [hiM, if_neg one_ne_zero]; exact hM1) htrigM
  have hMtake : ((G ++ ((v0,w0) :: R) ++ [lp]).take (G.length + q)).drop
      (G.length + (j0X - G.length - k * ((v0,w0) :: R).length) + 1)
      = (((v0,w0) :: R).take q).drop
          ((j0X - G.length - k * ((v0,w0) :: R).length) + 1) := by
    rw [hostM_take_at (le_of_lt hq), List.drop_append,
        List.drop_eq_nil_of_le (by omega), List.nil_append,
        show G.length + (j0X - G.length - k * ((v0,w0) :: R).length) + 1
            - G.length
          = (j0X - G.length - k * ((v0,w0) :: R).length) + 1 by omega]
  have hXtake : ((copyExp G ((v0,w0) :: R) d0 n).take
        (G.length + (k * ((v0,w0) :: R).length + q))).drop (j0X + 1)
      = ((((v0,w0) :: R).take q).drop
          ((j0X - G.length - k * ((v0,w0) :: R).length) + 1)).map
            fun p => (p.1 + k * d0, p.2) := by
    rw [copyExp_take_at hk (le_of_lt hq), List.drop_append,
        List.drop_eq_nil_of_le (by rw [copyExp_length]; omega),
        List.nil_append, copyExp_length,
        show j0X + 1 - (G.length + k * ((v0,w0) :: R).length)
          = (j0X - G.length - k * ((v0,w0) :: R).length) + 1 by omega,
        ← List.map_take, ← List.map_drop]
  rw [hXtake]
  rw [hMtake] at happ
  exact hhm_shift happ


/-! ## Chains cover their interval without dips -/

theorem rtg_nextrel0_e0_le {W : PairSeq} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 W) a b) :
    a = b ∨ entry W 0 a < entry W 0 b := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail c e hchain hstep ih =>
    right
    rcases ih with rfl | hlt
    · exact hstep.2.2.2.1
    · exact lt_trans hlt hstep.2.2.2.1

/-- A `nextrel0` chain covers its interval without dips: every strictly
intermediate position sits strictly above the base level. -/
theorem rtg_no_dip {W : PairSeq} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 W) a b) :
    ∀ l, a < l → l < b → entry W 0 a < entry W 0 l := by
  induction h with
  | refl =>
    intro l h1 h2
    omega
  | @tail c e hchain hstep ih =>
    intro l h1 h2
    have hac : a ≤ c := rtg_nextrel0_le hchain
    by_cases hlc : l < c
    · exact ih l h1 hlc
    · rcases Nat.eq_or_lt_of_le (show c ≤ l by omega) with rfl | hlt
      · rcases rtg_nextrel0_e0_le hchain with rfl | hlt'
        · omega
        · exact hlt'
      · have h5 := hstep.2.2.2.2 l ⟨hlt, h2⟩
        have h4 := hstep.2.2.2.1
        have h6 : entry W 0 a ≤ entry W 0 c := by
          rcases rtg_nextrel0_e0_le hchain with rfl | h7
          · exact le_rfl
          · exact le_of_lt h7
        omega


/-! ## The Pred branch of the final-block discipline -/

theorem runAt_take {M : PairSeq} {p m : ℕ} (hp : p < m) :
    runAt (M.take m) p = (runAt M p).take (m - (p + 1)) := by
  unfold runAt
  rw [getD_take hp, List.drop_take, ← List.take_takeWhile]

theorem headmax_take {K : PairSeq} (h : headmax K) (t : ℕ) :
    headmax (K.take t) := by
  rcases h with rfl | h
  · exact Or.inl (by simp)
  · cases K with
    | nil => exact Or.inl (by simp)
    | cons k0 K' =>
      cases t with
      | zero => exact Or.inl rfl
      | succ t' =>
        rw [List.take_succ_cons]
        right
        rw [List.headI_cons] at h ⊢
        have hdec : k0 :: K' = k0 :: (K'.take t' ++ K'.drop t') := by
          rw [List.take_append_drop]
        rw [hdec] at h
        exact headmax_prefix h

theorem mem_iff_getD {L : List (ℕ × ℕ)} {x : ℕ × ℕ} (h : x ∈ L) :
    ∃ i, i < L.length ∧ L.getD i (0,0) = x := by
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem h
  exact ⟨i, hi, by rw [getD_eq_getElem' _ _ hi]; exact hget⟩

/-- **The Pred branch preserves the final-block discipline** when the host
ends in `(0,0)`: that column closes every run with row-1 value `0`, so the
new block and all its interior runs live inside `hmok` closures. -/
theorem tailok_Pred_zero {M : PairSeq} (hM : hmok M)
    (hlast : M.getD (M.length - 1) (0,0) = (0,0)) (hlen : 2 ≤ M.length) :
    tailok M.dropLast := by
  intro j0 hj0 hnx _htrig
  clear _htrig
  rw [List.dropLast_eq_take] at hj0 hnx ⊢
  have hXlen : (M.take (M.length - 1)).length = M.length - 1 := by
    rw [List.length_take]
    omega
  rw [hXlen] at hj0 hnx ⊢
  rw [show M.length - 1 - 1 = M.length - 2 by omega] at hnx ⊢
  rw [idx1_take (by omega), nextR_take_iff (by omega) (by omega)] at hnx
  have hdip : ∀ l, j0 < l → l < M.length - 2 →
      entry M 0 j0 < entry M 0 l := by
    intro l hl1 hl2
    unfold nextR at hnx
    by_cases hi : idx1 M (M.length - 2) = 0
    · rw [if_pos hi] at hnx
      have h5 := hnx.2.2.2.2 l ⟨hl1, hl2⟩
      have h4 := hnx.2.2.2.1
      omega
    · rw [if_neg hi] at hnx
      obtain ⟨-, -, hchain⟩ := hnx.2.2.2.2.1
      exact rtg_no_dip hchain l hl1 hl2
  have hj0lt : entry M 0 j0 < entry M 0 (M.length - 2) := by
    unfold nextR at hnx
    by_cases hi : idx1 M (M.length - 2) = 0
    · rw [if_pos hi] at hnx
      exact hnx.2.2.2.1
    · rw [if_neg hi] at hnx
      obtain ⟨-, -, hchain⟩ := hnx.2.2.2.2.1
      rcases rtg_nextrel0_e0_le hchain with heq | hlt
      · omega
      · exact hlt
  have hrun : runAt M j0
      = (M.drop (j0 + 1)).take (M.length - 1 - (j0 + 1)) := by
    unfold runAt
    have hdec : M.drop (j0 + 1)
        = (M.drop (j0 + 1)).take (M.length - 1 - (j0 + 1))
          ++ (M.drop (j0 + 1)).drop (M.length - 1 - (j0 + 1)) := by
      rw [List.take_append_drop]
    conv_lhs => rw [hdec]
    rw [takeWhile_append_head_stop (by
      intro a ha
      have h1 : ((M.drop (j0 + 1)).drop (M.length - 1 - (j0 + 1)))[0]?
          = some a := by
        rw [← List.head?_eq_getElem?]
        exact ha
      rw [List.getElem?_drop, List.getElem?_drop] at h1
      have h2 : M.getD (j0 + 1 + (M.length - 1 - (j0 + 1) + 0)) (0,0) = a := by
        rw [List.getD_eq_getElem?_getD, h1]
        rfl
      have hidx : j0 + 1 + (M.length - 1 - (j0 + 1) + 0) = M.length - 1 := by
        omega
      rw [hidx] at h2
      rw [hlast] at h2
      rw [← h2]
      simp)]
    apply List.takeWhile_eq_self_iff.2
    intro x hx
    obtain ⟨i, hi, hgd⟩ := mem_iff_getD hx
    rw [List.length_take, List.length_drop] at hi
    have hieq : x = M.getD (j0 + 1 + i) (0,0) := by
      rw [← hgd, getD_take (by omega), getD_drop]
    have he : ∀ l, entry M 0 l = (M.getD l (0,0)).1 := by
      intro l
      unfold entry
      rw [if_pos rfl]
    have hgoal : (M.getD j0 (0,0)).1 < (M.getD (j0 + 1 + i) (0,0)).1 := by
      rcases Nat.lt_or_ge (j0 + 1 + i) (M.length - 2) with hc | hc
      · have h7 := hdip (j0 + 1 + i) (by omega) hc
        rw [he, he] at h7
        exact h7
      · have hieq2 : j0 + 1 + i = M.length - 2 := by omega
        rw [hieq2]
        have h7 := hj0lt
        rw [he, he] at h7
        exact h7
    rw [hieq]
    simpa using hgoal
  have hstopeq : stopAt M j0 = M.length - 1 := by
    unfold stopAt
    rw [hrun, List.length_take, List.length_drop]
    omega
  have hcc := hM j0 (by omega) (by omega)
    (by
      rw [hstopeq, hlast]
      simp)
  rw [hstopeq] at hcc
  -- the new block in canonical form
  have hbeq : ((M.take (M.length - 1)).take (M.length - 2)).drop (j0 + 1)
      = (M.take (M.length - 2)).drop (j0 + 1) := by
    rw [List.take_take, min_eq_left (by omega)]
  rw [hbeq]
  constructor
  · -- the block is a truncation of the parent's run
    have hb2 : (M.take (M.length - 2)).drop (j0 + 1)
        = (runAt M j0).take (M.length - 2 - (j0 + 1)) := by
      rw [hrun, List.drop_take, List.take_take,
          min_eq_left (by omega)]
    rw [hb2]
    exact headmax_take (hcc j0 le_rfl (by omega)) _
  · intro p' hp'
    rw [List.length_drop, List.length_take] at hp'
    have hp'2 : p' < M.length - 2 - (j0 + 1) := by omega
    have hsplit : M.take (M.length - 2)
        = M.take (j0 + 1) ++ (M.take (M.length - 2)).drop (j0 + 1) := by
      conv_lhs => rw [← List.take_append_drop (j0 + 1) (M.take (M.length - 2))]
      rw [List.take_take, min_eq_left (by omega)]
    have h1 := runAt_append_left (G := M.take (j0 + 1))
      (M := (M.take (M.length - 2)).drop (j0 + 1)) (j := p')
    rw [← hsplit, List.length_take, min_eq_left (by omega)] at h1
    rw [← h1, runAt_take (by omega)]
    exact headmax_take (hcc (j0 + 1 + p') (by omega) (by omega)) _


/-! ## Level-0 columns are `(0,0)` -/

/-- Level-0 columns carry row-1 value `0`. -/
def z0ok (M : PairSeq) : Prop :=
  ∀ j, j < M.length → (M.getD j (0,0)).1 = 0 → (M.getD j (0,0)).2 = 0

theorem z0ok_diagSeq (v : ℕ) : z0ok (diagSeq 0 v) := by
  intro j hj h0
  rw [diagSeq0_length] at hj
  rw [diagSeq0_getD hj] at h0 ⊢
  simpa using h0

theorem z0ok_take {M : PairSeq} (h : z0ok M) (m : ℕ) : z0ok (M.take m) := by
  intro j hj h0
  rw [List.length_take] at hj
  rw [getD_take (by omega)] at h0 ⊢
  exact h j (by omega) h0

theorem z0ok_Pred {M : PairSeq} (h : z0ok M) : z0ok (Pred M) := by
  unfold Pred
  by_cases hl : M.length ≤ 1
  · rw [if_pos hl]
    exact h
  · rw [if_neg hl, List.dropLast_eq_take]
    exact z0ok_take h _

theorem z0ok_copyExp {G B : PairSeq} {lp : ℕ × ℕ} {d0 n : ℕ}
    (h : z0ok (G ++ B ++ [lp])) : z0ok (copyExp G B d0 n) := by
  intro j hj h0
  rw [copyExp_length] at hj
  by_cases hjg : j < G.length
  · rw [copyExp_getD_pre hjg] at h0 ⊢
    have hg := h j (by rw [hostM_length]; omega)
    rw [hostM_getD_pre hjg] at hg
    exact hg h0
  · push Not at hjg
    have hL : 0 < B.length := by
      by_contra hB0
      push Not at hB0
      have : B.length = 0 := by omega
      rw [this, Nat.mul_zero] at hj
      omega
    obtain ⟨k, q, hk, hq, hdec⟩ := index_decomp hL
      (show j - G.length < n * B.length by omega)
    have hjeq : j = G.length + (k * B.length + q) := by omega
    subst hjeq
    rw [copyExp_getD_copy hk hq] at h0 ⊢
    have h0' : (B.getD q (0,0)).1 + k * d0 = 0 := h0
    have hM := h (G.length + q) (by rw [hostM_length]; omega)
    rw [hostM_getD_blk hq] at hM
    show (B.getD q (0,0)).2 = 0
    exact hM (by omega)


/-! ## Parent uniqueness and row-0 existence -/

/-- Row-0 parents are unique: a later candidate dips the earlier's clause. -/
theorem nextrel0_unique {M : PairSeq} {k1 k2 j : ℕ}
    (h1 : nextrel0 M k1 j) (h2 : nextrel0 M k2 j) : k1 = k2 := by
  rcases Nat.lt_trichotomy k1 k2 with h | h | h
  · have := h1.2.2.2.2 k2 ⟨h, h2.2.2.1⟩
    have := h2.2.2.2.1
    omega
  · exact h
  · have := h2.2.2.2.2 k1 ⟨h, h1.2.2.1⟩
    have := h1.2.2.2.1
    omega

/-- Row-1 parents are unique: maximality excludes a later candidate. -/
theorem nextrel1_unique {M : PairSeq} {k1 k2 j : ℕ}
    (h1 : nextrel1 M k1 j) (h2 : nextrel1 M k2 j) : k1 = k2 := by
  rcases Nat.lt_trichotomy k1 k2 with h | h | h
  · have := h1.2.2.2.2.2 k2 ⟨h, h2.2.2.2.2.1⟩
    have := h2.2.2.2.1
    omega
  · exact h
  · have := h2.2.2.2.2.2 k1 ⟨h, h1.2.2.2.2.1⟩
    have := h1.2.2.2.1
    omega

/-- The head of a `blockok 0` host is a level-0 column. -/
theorem blockok_head_zero {M : PairSeq} (hb : blockok 0 M)
    (hne : 0 < M.length) : (M.getD 0 (0,0)).1 = 0 := by
  obtain ⟨m0, M', rfl⟩ : ∃ m0 M', M = m0 :: M' := by
    cases M with
    | nil => simp at hne
    | cons m0 M' => exact ⟨m0, M', rfl⟩
  rw [List.getD_cons_zero]
  have := hb.1 (by simp)
  rw [List.headI_cons] at this
  exact this

/-- Row-0 parent existence: the largest lower-level position qualifies. -/
theorem parent0_exists {M : PairSeq} (hb : blockok 0 M) {j : ℕ}
    (hj : j < M.length) (h0 : 0 < entry M 0 j) :
    ∃ k, nextrel0 M k j := by
  classical
  have hj0 : 0 < j := by
    by_contra hc
    push Not at hc
    have : j = 0 := by omega
    subst this
    have := blockok_head_zero hb (by omega)
    unfold entry at h0
    rw [if_pos rfl] at h0
    omega
  set P : ℕ → Prop := fun k => entry M 0 k < entry M 0 j with hP
  have hP0 : P 0 := by
    show entry M 0 0 < entry M 0 j
    unfold entry
    rw [if_pos rfl, blockok_head_zero hb (by omega)]
    unfold entry at h0
    rw [if_pos rfl] at h0
    exact h0
  refine ⟨Nat.findGreatest P (j - 1), ?_, hj, ?_, ?_, ?_⟩
  · have := Nat.findGreatest_le (P := P) (j - 1)
    omega
  · have := Nat.findGreatest_le (P := P) (j - 1)
    omega
  · exact Nat.findGreatest_spec (Nat.zero_le _) hP0
  · intro l hl
    have hnl := Nat.findGreatest_is_greatest (P := P) hl.1 (by omega)
    rw [hP] at hnl
    push Not at hnl
    exact hnl


/-! ## Parent existence: the no-parent branch is empty on the class -/

theorem chain_to_zero {M : PairSeq} (hb : blockok 0 M) :
    ∀ lev j, entry M 0 j = lev → j < M.length →
      ∃ r, r ≤ j ∧ entry M 0 r = 0
        ∧ Relation.ReflTransGen (nextrel0 M) r j := by
  intro lev
  induction lev using Nat.strong_induction_on with
  | _ lev IH =>
    intro j he hj
    by_cases h0 : entry M 0 j = 0
    · exact ⟨j, le_rfl, h0, Relation.ReflTransGen.refl⟩
    · obtain ⟨k, hk⟩ := parent0_exists hb hj (by omega)
      have hklt : entry M 0 k < entry M 0 j := hk.2.2.2.1
      have hkj : k < j := hk.2.2.1
      obtain ⟨r, hr1, hr2, hr3⟩ :=
        IH (entry M 0 k) (by omega) k rfl hk.1
      exact ⟨r, by omega, hr2, hr3.tail hk⟩

theorem parent1_exists {M : PairSeq} (hb : blockok 0 M) (hz : z0ok M)
    {j : ℕ} (hj : j < M.length) (h1 : 0 < entry M 1 j) :
    ∃ k, nextrel1 M k j := by
  classical
  obtain ⟨r, hrle, hr0, hchain⟩ := chain_to_zero hb (entry M 0 j) j rfl hj
  have hre1 : entry M 1 r = 0 := by
    have hz' := hz r (by omega)
    unfold entry at hr0 ⊢
    rw [if_pos rfl] at hr0
    rw [if_neg one_ne_zero]
    exact hz' hr0
  have hrj : r < j := by
    rcases Nat.eq_or_lt_of_le hrle with rfl | h
    · omega
    · exact h
  set P : ℕ → Prop := fun k => le0 M k j ∧ entry M 1 k < entry M 1 j with hP
  have hPr : P r := by
    refine ⟨⟨by omega, hj, hchain⟩, ?_⟩
    rw [hre1]
    exact h1
  have hspec := Nat.findGreatest_spec (P := P) (show r ≤ j - 1 by omega) hPr
  have hle := Nat.findGreatest_le (P := P) (j - 1)
  refine ⟨Nat.findGreatest P (j - 1), ?_, hj, by omega, hspec.2, hspec.1, ?_⟩
  · omega
  · intro j' hj'
    rcases Nat.eq_or_lt_of_le (le0_le hj'.2) with rfl | hlt
    · exact le_rfl
    · by_contra hcon
      push Not at hcon
      exact Nat.findGreatest_is_greatest (P := P) hj'.1 (by omega)
        ⟨hj'.2, hcon⟩

theorem nextR_one_iff {M : PairSeq} {k j : ℕ} :
    nextR M 1 k j ↔ nextrel1 M k j := by
  unfold nextR
  rw [if_neg one_ne_zero]

theorem nextR_zero_iff {M : PairSeq} {k j : ℕ} :
    nextR M 0 k j ↔ nextrel0 M k j := by
  unfold nextR
  rw [if_pos rfl]

/-- **Every nonzero final column of a standard-shaped host has a unique
parent** — the no-parent `Pred` branch is empty on the class. -/
theorem hp_last {M : PairSeq} (hb : blockok 0 M) (hz : z0ok M)
    (hlen : 0 < M.length)
    (hzz : ¬ M.getD (M.length - 1) (0,0) = (0,0)) :
    hasParent M (idx1 M (M.length - 1)) (M.length - 1) := by
  classical
  by_cases h1 : 0 < entry M 1 (M.length - 1)
  · have hi : idx1 M (M.length - 1) = 1 := by
      unfold idx1
      rw [if_pos h1]
    obtain ⟨k, hk⟩ := parent1_exists hb hz (by omega) h1
    refine ⟨k, ?_, ?_⟩
    · show nextR M (idx1 M (M.length - 1)) k (M.length - 1)
      rw [hi, nextR_one_iff]
      exact hk
    · intro y hy
      have hy' : nextR M (idx1 M (M.length - 1)) y (M.length - 1) := hy
      rw [hi, nextR_one_iff] at hy'
      exact nextrel1_unique hy' hk
  · have h1' : entry M 1 (M.length - 1) = 0 := by omega
    have h0 : 0 < entry M 0 (M.length - 1) := by
      by_contra hc
      push Not at hc
      apply hzz
      unfold entry at h1'
      rw [if_neg one_ne_zero] at h1'
      have h0' : (M.getD (M.length - 1) (0,0)).1 = 0 := by
        unfold entry at hc
        rw [if_pos rfl] at hc
        omega
      exact Prod.ext h0' h1'
    have hi : idx1 M (M.length - 1) = 0 := by
      unfold idx1
      rw [if_neg (by omega)]
    obtain ⟨k, hk⟩ := parent0_exists hb (by omega) h0
    refine ⟨k, ?_, ?_⟩
    · show nextR M (idx1 M (M.length - 1)) k (M.length - 1)
      rw [hi, nextR_zero_iff]
      exact hk
    · intro y hy
      have hy' : nextR M (idx1 M (M.length - 1)) y (M.length - 1) := hy
      rw [hi, nextR_zero_iff] at hy'
      exact nextrel0_unique hy' hk


/-! ## Block intervals above a base are hereditarily head-maximal -/

theorem interval_eq_run_take {B : PairSeq} {q0 t : ℕ}
    (hpass : ∀ i, i < t → i < (B.drop (q0 + 1)).length →
      (B.getD q0 (0,0)).1 < ((B.drop (q0 + 1)).getD i (0,0)).1) :
    (B.drop (q0 + 1)).take t = (runAt B q0).take t := by
  unfold runAt
  rw [List.take_takeWhile]
  rw [List.takeWhile_eq_self_iff.2 (by
    intro x hx
    obtain ⟨i, hi, hgd⟩ := mem_iff_getD hx
    rw [List.length_take] at hi
    have hieq : x = (B.drop (q0 + 1)).getD i (0,0) := by
      rw [← hgd, getD_take (by omega)]
    rw [hieq]
    simp only [decide_eq_true_eq]
    exact hpass i (by omega) (by omega))]

/-- `hhm` of every block interval above a base. -/
theorem hhm_block_interval {v0 w0 : ℕ} {R : PairSeq}
    (hdom : ∀ x ∈ R, v0 < x.1) (hR : hhm R) {q0 t : ℕ}
    (hq0 : q0 < ((v0,w0) :: R).length)
    (hpass : ∀ i, i < t → i < (((v0,w0) :: R).drop (q0 + 1)).length →
      (((v0,w0) :: R).getD q0 (0,0)).1
        < ((((v0,w0) :: R).drop (q0 + 1)).getD i (0,0)).1) :
    hhm ((((v0,w0) :: R).drop (q0 + 1)).take t) := by
  constructor
  · rw [interval_eq_run_take hpass]
    exact headmax_take (headmax_runAt_block hdom hR q0 hq0) t
  · intro p' hp'
    rw [List.length_take, List.length_drop] at hp'
    have hp'L : q0 + 1 + p' < ((v0,w0) :: R).length := by omega
    have hsplit : ((v0,w0) :: R).take (q0 + 1 + t)
        = ((v0,w0) :: R).take (q0 + 1)
          ++ (((v0,w0) :: R).drop (q0 + 1)).take t := by
      conv_lhs => rw [← List.take_append_drop (q0 + 1)
        (((v0,w0) :: R).take (q0 + 1 + t))]
      rw [List.take_take, min_eq_left (by omega), List.drop_take,
          Nat.add_sub_cancel_left]
    have h1 := runAt_append_left (G := ((v0,w0) :: R).take (q0 + 1))
      (M := (((v0,w0) :: R).drop (q0 + 1)).take t) (j := p')
    rw [← hsplit, List.length_take, min_eq_left (by omega)] at h1
    rw [← h1, runAt_take (by omega)]
    exact headmax_take (headmax_runAt_block hdom hR _ hp'L) _


/-! ## Final-column instances with a parent inside the last copy -/

/-- The final-column instances of `copyExp` with a parent inside the last
copy: the block is a shifted dominated interval of the host block. -/
theorem tlast_copyExp_within {G : PairSeq} {v0 w0 : ℕ} {R : PairSeq}
    {d0 n j0X : ℕ} (hdom : ∀ x ∈ R, v0 < x.1) (hn : 1 ≤ n) (hhmR : hhm R)
    (hge : G.length + (n - 1) * ((v0,w0) :: R).length ≤ j0X)
    (hnx : nextR (copyExp G ((v0,w0) :: R) d0 n)
      (idx1 (copyExp G ((v0,w0) :: R) d0 n)
        ((copyExp G ((v0,w0) :: R) d0 n).length - 1)) j0X
      ((copyExp G ((v0,w0) :: R) d0 n).length - 1)) :
    hhm (((copyExp G ((v0,w0) :: R) d0 n).take
        ((copyExp G ((v0,w0) :: R) d0 n).length - 1)).drop (j0X + 1)) := by
  have hL : 0 < ((v0,w0) :: R).length := by simp
  have hXlen : (copyExp G ((v0,w0) :: R) d0 n).length
      = G.length + n * ((v0,w0) :: R).length := copyExp_length ..
  have hnL : (n - 1) * ((v0,w0) :: R).length + ((v0,w0) :: R).length
      = n * ((v0,w0) :: R).length := by
    have h := Nat.succ_mul (n - 1) ((v0,w0) :: R).length
    rw [Nat.succ_eq_add_one, show n - 1 + 1 = n by omega] at h
    omega
  -- the dip-free property across the block, both rows
  have hj0lt : j0X < (copyExp G ((v0,w0) :: R) d0 n).length - 1 := by
    unfold nextR at hnx
    by_cases hi : idx1 (copyExp G ((v0,w0) :: R) d0 n)
        ((copyExp G ((v0,w0) :: R) d0 n).length - 1) = 0
    · rw [if_pos hi] at hnx
      exact hnx.2.2.1
    · rw [if_neg hi] at hnx
      exact hnx.2.2.1
  have hdip : ∀ l, j0X < l → l < (copyExp G ((v0,w0) :: R) d0 n).length - 1 →
      entry (copyExp G ((v0,w0) :: R) d0 n) 0 j0X
        < entry (copyExp G ((v0,w0) :: R) d0 n) 0 l := by
    intro l hl1 hl2
    unfold nextR at hnx
    by_cases hi : idx1 (copyExp G ((v0,w0) :: R) d0 n)
        ((copyExp G ((v0,w0) :: R) d0 n).length - 1) = 0
    · rw [if_pos hi] at hnx
      have h5 := hnx.2.2.2.2 l ⟨hl1, hl2⟩
      have h4 := hnx.2.2.2.1
      omega
    · rw [if_neg hi] at hnx
      obtain ⟨-, -, hchain⟩ := hnx.2.2.2.2.1
      exact rtg_no_dip hchain l hl1 hl2
  -- offsets within the last copy
  have hq0 : j0X - G.length - (n - 1) * ((v0,w0) :: R).length
      < ((v0,w0) :: R).length := by omega
  -- the block in canonical shifted-interval form
  have hblock : ((copyExp G ((v0,w0) :: R) d0 n).take
        ((copyExp G ((v0,w0) :: R) d0 n).length - 1)).drop (j0X + 1)
      = ((((v0,w0) :: R).drop
            ((j0X - G.length - (n - 1) * ((v0,w0) :: R).length) + 1)).take
          (((v0,w0) :: R).length - 1
            - ((j0X - G.length - (n - 1) * ((v0,w0) :: R).length) + 1))).map
        fun p => (p.1 + (n - 1) * d0, p.2) := by
    rw [hXlen,
        show G.length + n * ((v0,w0) :: R).length - 1
          = G.length + ((n - 1) * ((v0,w0) :: R).length
            + (((v0,w0) :: R).length - 1)) by omega,
        copyExp_take_at (by omega) (by omega),
        List.drop_append,
        List.drop_eq_nil_of_le (by rw [copyExp_length]; omega),
        List.nil_append, copyExp_length,
        show j0X + 1 - (G.length + (n - 1) * ((v0,w0) :: R).length)
          = (j0X - G.length - (n - 1) * ((v0,w0) :: R).length) + 1 by omega,
        ← List.map_take, ← List.map_drop, List.drop_take]
  rw [hblock]
  apply hhm_shift
  apply hhm_block_interval hdom hhmR hq0
  intro i hi hi2
  rw [List.length_drop] at hi2
  have hj0form : j0X = G.length + ((n - 1) * ((v0,w0) :: R).length
      + (j0X - G.length - (n - 1) * ((v0,w0) :: R).length)) := by omega
  have he1' : entry (copyExp G ((v0,w0) :: R) d0 n) 0 j0X
      = (((v0,w0) :: R).getD
          (j0X - G.length - (n - 1) * ((v0,w0) :: R).length) (0,0)).1
        + (n - 1) * d0 := by
    conv_lhs => rw [hj0form]
    exact (entry_copyExp (show n - 1 < n by omega) hq0).1
  have he2 := (entry_copyExp (G := G) (B := (v0,w0) :: R) (d0 := d0)
    (show n - 1 < n by omega)
    (show (j0X - G.length - (n - 1) * ((v0,w0) :: R).length) + 1 + i
        < ((v0,w0) :: R).length by omega)).1
  have hl := hdip (G.length + ((n - 1) * ((v0,w0) :: R).length
      + ((j0X - G.length - (n - 1) * ((v0,w0) :: R).length) + 1 + i)))
    (by omega) (by omega)
  rw [he1', he2] at hl
  rw [getD_drop]
  rw [show (j0X - G.length - (n - 1) * ((v0,w0) :: R).length) + 1 + i
        = (j0X - G.length - (n - 1) * ((v0,w0) :: R).length + 1) + i
      by omega] at hl
  omega

theorem z0ok_oper {M : PairSeq} {n : ℕ} (hn : 1 ≤ n) (h : z0ok M) :
    z0ok (M⟦n⟧) := by
  by_cases hL0 : M.length - 1 = 0
  · rw [oper_eq_self_of_short n hL0]
    exact h
  by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0
  · rw [oper_eq_pred_of_zero n hL0 hz]
    exact z0ok_Pred h
  by_cases hp : hasParent M (idx1 M (M.length - 1)) (M.length - 1)
  case neg =>
    rw [oper_eq_pred_of_noParent n hL0 hz hp]
    exact z0ok_Pred h
  case pos =>
    obtain ⟨G, v0, w0, R, d0, lp, hMeq, hX, -, -, -, -⟩ :=
      oper_bad_blocks (by omega) hz hp hn
    rw [hX]
    show z0ok (copyExp G ((v0,w0) :: R) d0 n)
    exact z0ok_copyExp (hMeq ▸ h)

/-- **Level-0 columns of standard hosts are `(0,0)`** — unconditional. -/
theorem z0ok_ST_PS {M : PairSeq} (hM : ST_PS M) : z0ok M := by
  induction hM with
  | diag v => exact z0ok_diagSeq v
  | oper hN hn ih => exact z0ok_oper hn ih


/-! ## The conditional generation closure of the invariant package -/

/-- The seam obligation: final-column instances of the expansion whose
parent lies before the last copy (mined exact on the class). -/
def seamOK (M : PairSeq) (n : ℕ) : Prop :=
  ∀ G v0 w0 (R : PairSeq) (lp : ℕ × ℕ) d0,
    M = G ++ ((v0,w0) :: R) ++ [lp] →
    M⟦n⟧ = copyExp G ((v0,w0) :: R) d0 n →
    (∀ p ∈ R, v0 < p.1) →
    nextR M (idx1 M (M.length - 1)) G.length (M.length - 1) →
    (d0 = 0 ∨ (0 < d0 ∧ w0 < lp.2 ∧ lp.1 = v0 + d0 ∧
      nextrel1 M G.length (M.length - 1))) →
    ∀ j0X, j0X < G.length + (n - 1) * ((v0,w0) :: R).length →
      j0X + 1 < (M⟦n⟧).length →
    nextR (M⟦n⟧) (idx1 (M⟦n⟧) ((M⟦n⟧).length - 1)) j0X ((M⟦n⟧).length - 1) →
    (idx1 (M⟦n⟧) ((M⟦n⟧).length - 1) = 1 →
      ∃ b, j0X < b ∧ b + 1 < (M⟦n⟧).length ∧
        ((M⟦n⟧).getD ((M⟦n⟧).length - 1) (0,0)).1
          ≤ ((M⟦n⟧).getD b (0,0)).1 ∧
        ((M⟦n⟧).getD j0X (0,0)).2 ≤ ((M⟦n⟧).getD b (0,0)).2) →
    hhm (((M⟦n⟧).take ((M⟦n⟧).length - 1)).drop (j0X + 1))

/-- The within-trigger obligation: a consumed final-column instance whose
parent lies in the last copy yields the host trigger when the host parent
row is 1 (mined exact: direct transfer in the 0-configs, vacuity in the
−1-configs via `interior_low`, and the iX = 0 coincidence). -/
def withinTrigOK (M : PairSeq) (n : ℕ) : Prop :=
  ∀ G v0 w0 (R : PairSeq) (lp : ℕ × ℕ) d0,
    M = G ++ ((v0,w0) :: R) ++ [lp] →
    M⟦n⟧ = copyExp G ((v0,w0) :: R) d0 n →
    0 < d0 → w0 < lp.2 → lp.1 = v0 + d0 →
    nextrel1 M G.length (M.length - 1) →
    nextR M (idx1 M (M.length - 1)) G.length (M.length - 1) →
    ∀ j0X, G.length + (n - 1) * ((v0,w0) :: R).length ≤ j0X →
      j0X + 1 < (M⟦n⟧).length →
      nextR (M⟦n⟧) (idx1 (M⟦n⟧) ((M⟦n⟧).length - 1)) j0X ((M⟦n⟧).length - 1) →
      (idx1 (M⟦n⟧) ((M⟦n⟧).length - 1) = 1 →
        ∃ b, j0X < b ∧ b + 1 < (M⟦n⟧).length ∧
          ((M⟦n⟧).getD ((M⟦n⟧).length - 1) (0,0)).1
            ≤ ((M⟦n⟧).getD b (0,0)).1 ∧
          ((M⟦n⟧).getD j0X (0,0)).2 ≤ ((M⟦n⟧).getD b (0,0)).2) →
      idx1 M (M.length - 1) = 1 →
      ∃ b, G.length < b ∧ b + 1 < M.length ∧
        (M.getD (M.length - 1) (0,0)).1 ≤ (M.getD b (0,0)).1 ∧
        (M.getD G.length (0,0)).2 ≤ (M.getD b (0,0)).2

/-- **The expansion step preserves the final-block discipline**, modulo the
seam and within-trigger obligations. -/
theorem tailok_oper {M : PairSeq} {n : ℕ} (hn : 1 ≤ n)
    (hMok : hmok M) (htl : tailok M) (hbk : blockok 0 M) (hz0 : z0ok M)
    (hseam : seamOK M n) (htr : withinTrigOK M n) : tailok (M⟦n⟧) := by
  by_cases hL0 : M.length - 1 = 0
  · rw [oper_eq_self_of_short n hL0] at *
    exact htl
  by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0
  · rw [oper_eq_pred_of_zero n hL0 hz] at *
    unfold Pred at *
    by_cases hl : M.length ≤ 1
    · rw [if_pos hl] at *
      exact htl
    · rw [if_neg hl] at *
      refine tailok_Pred_zero hMok ?_ (by omega)
      obtain ⟨h0, h1⟩ := hz
      unfold entry at h0 h1
      rw [if_pos rfl] at h0
      rw [if_neg one_ne_zero] at h1
      exact Prod.ext h0 h1
  by_cases hp : hasParent M (idx1 M (M.length - 1)) (M.length - 1)
  case neg =>
    exfalso
    exact hp (hp_last hbk hz0 (by omega) (by
      intro he
      apply hz
      constructor
      · unfold entry
        rw [if_pos rfl, he]
      · unfold entry
        rw [if_neg one_ne_zero, he]))
  case pos =>
    obtain ⟨G, v0, w0, R, d0, lp, hMeq, hX, hdom, -, hd0, hnxtM⟩ :=
      oper_bad_blocks (by omega) hz hp hn
    have hMlen : M.length = G.length + ((v0,w0) :: R).length + 1 := by
      rw [hMeq]
      exact hostM_length ..
    have hL : 0 < ((v0,w0) :: R).length := by simp
    have hXc : M⟦n⟧ = copyExp G ((v0,w0) :: R) d0 n := hX
    intro j0X hj0 hnx htrigX
    by_cases hge : G.length + (n - 1) * ((v0,w0) :: R).length ≤ j0X
    · -- within the last copy
      have hhmR : hhm R := by
        have htake : M.take (M.length - 1) = G ++ ((v0,w0) :: R) := by
          rw [show M.length - 1 = G.length + ((v0,w0) :: R).length by omega,
              hMeq,
              show G.length + ((v0,w0) :: R).length
                = (G ++ ((v0,w0) :: R)).length by simp,
              List.take_left]
        have hdrop : (G ++ ((v0,w0) :: R)).drop (G.length + 1) = R := by
          rw [List.drop_append, List.drop_eq_nil_of_le (by omega),
              List.nil_append, show G.length + 1 - G.length = 1 by omega,
              List.drop_succ_cons, List.drop_zero]
        rcases hd0 with ⟨-, hi0⟩ | ⟨hd0p, hwlt, hlpe, hnx1M⟩
        · have happ := htl G.length (by omega) hnxtM (by
            intro h1
            rw [hi0] at h1
            exact absurd h1 (by omega))
          rw [htake, hdrop] at happ
          exact happ
        · have hi1 : idx1 M (M.length - 1) = 1 := by
            unfold idx1
            rw [if_pos]
            unfold entry
            rw [if_neg one_ne_zero,
                show M.length - 1
                  = G.length + ((v0,w0) :: R).length by omega, hMeq,
                hostM_getD_lp]
            omega
          have hMtrig := htr G v0 w0 R lp d0 hMeq hXc hd0p hwlt hlpe
            hnx1M hnxtM j0X hge hj0 hnx htrigX hi1
          have happ := htl G.length (by omega) hnxtM (by
            intro _
            exact hMtrig)
          rw [htake, hdrop] at happ
          exact happ
      have hres := tlast_copyExp_within (d0 := d0) (n := n) hdom hn hhmR
        (by omega) (by rw [← hXc]; exact hnx)
      rw [← hXc] at hres
      exact hres
    · exact hseam G v0 w0 R lp d0 hMeq hXc hdom hnxtM (hd0.imp (·.1) id)
        j0X (by omega) hj0 hnx htrigX

/-- **The invariant package on standard hosts**, modulo the seam and
within-trigger obligations. -/
theorem hmok_tailok_ST_PS {M : PairSeq} (hM : ST_PS M)
    (hseam : ∀ N k, ST_PS N → 1 ≤ k → seamOK N k)
    (htr : ∀ N k, ST_PS N → 1 ≤ k → withinTrigOK N k) :
    hmok M ∧ tailok M := by
  induction hM with
  | diag v => exact ⟨hmok_diagSeq v, tailok_diagSeq v⟩
  | @oper N k hN hk ih =>
    obtain ⟨h1, h2⟩ := ih
    exact ⟨hmok_oper hk h1 h2,
      tailok_oper hk h1 h2 (blockok_ST_PS hN) (z0ok_ST_PS hN)
        (hseam N k hN hk) (htr N k hN hk)⟩


/-! ## The single-climb discipline -/

/-- **The single-climb discipline** (anchored form; mined exact over all
infixes of all hosts, 87,690/87,690): in a row-1 parented segment whose
parent edge is anchored at the segment head, no column strictly between the
head and the last column's row-0 parent reaches within one of the last
column's level. -/
def sclimb (M : PairSeq) : Prop :=
  ∀ r' r, 1 < M.length →
    nextR M (idx1 M (M.length - 1)) 0 (M.length - 1) →
    idx1 M (M.length - 1) = 1 →
    0 < r' → r' + 1 < M.length →
    (M.getD r' (0,0)).1 + 1 = (M.getD (M.length - 1) (0,0)).1 →
    (∀ l, r' < l → l + 1 < M.length →
      (M.getD (M.length - 1) (0,0)).1 ≤ (M.getD l (0,0)).1) →
    0 < r → r < r' →
    (M.getD r (0,0)).1 + 1 < (M.getD (M.length - 1) (0,0)).1

theorem sclimb_diagSeq (v : ℕ) : sclimb (diagSeq 0 v) := by
  intro r' r _hlen _hnx _hi1 _hr'1 hr'2 hlev _hafter hr1 hr2
  have hlen : (diagSeq 0 v).length = v + 1 := diagSeq0_length v
  rw [hlen] at hr'2 hlev ⊢
  rw [show v + 1 - 1 = v by omega] at hlev ⊢
  rw [diagSeq0_getD (by omega), diagSeq0_getD (by omega)] at hlev
  rw [diagSeq0_getD (by omega), diagSeq0_getD (by omega)]
  have h1 : r' + 1 = v := by simpa using hlev
  show r + 1 < v
  omega

/-- The `sclimb` witness data is exactly a `nextrel0` edge into the last
column. -/
theorem sclimb_rp_nextrel0 {M : PairSeq} {r' : ℕ}
    (hr'2 : r' + 1 < M.length)
    (hlev : (M.getD r' (0,0)).1 + 1 = (M.getD (M.length - 1) (0,0)).1)
    (hafter : ∀ l, r' < l → l + 1 < M.length →
      (M.getD (M.length - 1) (0,0)).1 ≤ (M.getD l (0,0)).1) :
    nextrel0 M r' (M.length - 1) := by
  refine ⟨by omega, by omega, by omega, ?_, ?_⟩
  · unfold entry
    rw [if_pos rfl, if_pos rfl]
    omega
  · intro l hl
    unfold entry
    rw [if_pos rfl, if_pos rfl]
    exact hafter l hl.1 (by omega)


/-! ## Drop transfer and chain-pivot machinery -/

theorem entry_drop {M : PairSeq} {k i j : ℕ} :
    entry (M.drop k) i j = entry M i (k + j) := by
  unfold entry
  rw [getD_drop]

theorem nextrel0_drop_iff {M : PairSeq} {k a b : ℕ} (hka : k ≤ a)
    (hkb : k ≤ b) :
    nextrel0 (M.drop k) (a - k) (b - k) ↔ nextrel0 M a b := by
  unfold nextrel0
  rw [List.length_drop]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨by omega, by omega, by omega, ?_, ?_⟩
    · rwa [entry_drop, entry_drop, Nat.add_sub_cancel' hka,
           Nat.add_sub_cancel' hkb] at h4
    · intro l hl
      have h6 := h5 (l - k) (by omega)
      rwa [entry_drop, entry_drop, Nat.add_sub_cancel' hkb,
           Nat.add_sub_cancel' (show k ≤ l by omega)] at h6
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨by omega, by omega, by omega, ?_, ?_⟩
    · rw [entry_drop, entry_drop, Nat.add_sub_cancel' hka,
          Nat.add_sub_cancel' hkb]
      exact h4
    · intro l hl
      rw [entry_drop, entry_drop, Nat.add_sub_cancel' hkb]
      exact h5 (k + l) (by omega)

theorem rtg_nextrel0_of_drop {M : PairSeq} {k a' b' : ℕ}
    (h : Relation.ReflTransGen (nextrel0 (M.drop k)) a' b') :
    Relation.ReflTransGen (nextrel0 M) (k + a') (k + b') := by
  induction h with
  | refl => exact .refl
  | @tail y z _ hs ih =>
    refine ih.tail ?_
    have h2 := (nextrel0_drop_iff (M := M) (k := k) (a := k + y) (b := k + z)
      (by omega) (by omega)).1
    rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left] at h2
    exact h2 hs

theorem rtg_nextrel0_to_drop {M : PairSeq} {k a b : ℕ} (hka : k ≤ a)
    (h : Relation.ReflTransGen (nextrel0 M) a b) :
    Relation.ReflTransGen (nextrel0 (M.drop k)) (a - k) (b - k) := by
  induction h with
  | refl => exact .refl
  | @tail y z hay hs ih =>
    have hky : k ≤ y := le_trans hka (nextrel0_rtrancl_index_le hay)
    have hz := nextrel0_lt hs
    exact ih.tail ((nextrel0_drop_iff hky (by omega)).2 hs)

theorem le0_drop_iff {M : PairSeq} {k a b : ℕ} (hka : k ≤ a) (hkb : k ≤ b)
    (hb : b < M.length) :
    le0 (M.drop k) (a - k) (b - k) ↔ le0 M a b := by
  unfold le0
  rw [List.length_drop]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have h4 := rtg_nextrel0_of_drop (M := M) h3
    rw [Nat.add_sub_cancel' hka, Nat.add_sub_cancel' hkb] at h4
    exact ⟨by omega, hb, h4⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, by omega, rtg_nextrel0_to_drop hka h3⟩

/-- A row-0 chain cannot jump a strict floor: if every column in `(ρ, b]`
sits strictly above `ρ`, any chain into `b` from before `ρ` passes
through `ρ`. -/
theorem rtg_through_pivot {M : PairSeq} {ρ : ℕ} :
    ∀ {a b}, Relation.ReflTransGen (nextrel0 M) a b → a < ρ → ρ ≤ b →
    (∀ y, ρ < y → y ≤ b → entry M 0 ρ < entry M 0 y) →
    Relation.ReflTransGen (nextrel0 M) ρ b := by
  intro a b h
  induction h with
  | refl =>
    intro h1 h2 _
    exact absurd (h1.trans_le h2) (lt_irrefl a)
  | @tail y z hay hyz ih =>
    intro h1 h2 hpiv
    by_cases hρy : ρ ≤ y
    · have ihy := ih h1 hρy
        (fun y' hy1 hy2 => hpiv y' hy1 (hy2.trans (nextrel0_lt hyz).le))
      exact ihy.tail hyz
    · push Not at hρy
      rcases eq_or_lt_of_le h2 with he | hlt
      · rw [he]
      · have hb5 := hyz.2.2.2.2 ρ ⟨hρy, hlt⟩
        exact absurd (hpiv z hlt le_rfl) (not_lt.mpr hb5)

theorem le0_through_pivot {M : PairSeq} {a ρ b : ℕ}
    (h : le0 M a b) (h1 : a < ρ) (h2 : ρ ≤ b)
    (hpiv : ∀ y, ρ < y → y ≤ b → entry M 0 ρ < entry M 0 y) :
    le0 M ρ b := by
  obtain ⟨_, hb, hch⟩ := h
  exact ⟨by omega, hb, rtg_through_pivot hch h1 h2 hpiv⟩


theorem entry_seg {X u S v : PairSeq} (heq : X = u ++ S ++ v) {i j : ℕ}
    (hj : j < S.length) :
    entry S i j = entry X i (u.length + j) := by
  unfold entry
  rw [heq, getD_middle hj]

/-- First half of the pivot split: the chain reaches the pivot. -/
theorem rtg_to_pivot {M : PairSeq} {ρ : ℕ} :
    ∀ {a b}, Relation.ReflTransGen (nextrel0 M) a b → a < ρ → ρ ≤ b →
    (∀ y, ρ < y → y ≤ b → entry M 0 ρ < entry M 0 y) →
    Relation.ReflTransGen (nextrel0 M) a ρ := by
  intro a b h
  induction h with
  | refl =>
    intro h1 h2 _
    exact absurd (h1.trans_le h2) (lt_irrefl a)
  | @tail y z hay hyz ih =>
    intro h1 h2 hpiv
    by_cases hρy : ρ ≤ y
    · exact ih h1 hρy
        (fun y' hy1 hy2 => hpiv y' hy1 (hy2.trans (nextrel0_lt hyz).le))
    · push Not at hρy
      rcases eq_or_lt_of_le h2 with he | hlt
      · rw [he]
        exact hay.tail hyz
      · have hb5 := hyz.2.2.2.2 ρ ⟨hρy, hlt⟩
        exact absurd (hpiv z hlt le_rfl) (not_lt.mpr hb5)

theorem le0_to_pivot {M : PairSeq} {a ρ b : ℕ}
    (h : le0 M a b) (h1 : a < ρ) (h2 : ρ ≤ b)
    (hpiv : ∀ y, ρ < y → y ≤ b → entry M 0 ρ < entry M 0 y) :
    le0 M a ρ := by
  obtain ⟨ha, hb, hch⟩ := h
  exact ⟨ha, by omega, rtg_to_pivot hch h1 h2 hpiv⟩

theorem nextrel1_drop_iff {M : PairSeq} {k a b : ℕ} (hka : k ≤ a)
    (hkb : k ≤ b) (hb : b < M.length) :
    nextrel1 (M.drop k) (a - k) (b - k) ↔ nextrel1 M a b := by
  unfold nextrel1
  rw [List.length_drop]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨by omega, hb, by omega, ?_, (le0_drop_iff hka hkb hb).1 h5, ?_⟩
    · rwa [entry_drop, entry_drop, Nat.add_sub_cancel' hka,
           Nat.add_sub_cancel' hkb] at h4
    · intro l hl
      have hkl : k ≤ l := by omega
      have h7 := h6 (l - k) ⟨by omega, (le0_drop_iff hkl hkb hb).2 hl.2⟩
      rwa [entry_drop, entry_drop, Nat.add_sub_cancel' hkb,
           Nat.add_sub_cancel' hkl] at h7
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨by omega, by omega, by omega, ?_,
      (le0_drop_iff hka hkb hb).2 h5, ?_⟩
    · rw [entry_drop, entry_drop, Nat.add_sub_cancel' hka,
          Nat.add_sub_cancel' hkb]
      exact h4
    · intro l hl
      have h8 : le0 M (k + l) b := by
        have h9 := (le0_drop_iff (M := M) (k := k) (a := k + l) (b := b)
          (by omega) hkb hb).1
        rw [Nat.add_sub_cancel_left] at h9
        exact h9 hl.2
      have h7 := h6 (k + l) ⟨by omega, h8⟩
      rw [entry_drop, entry_drop, Nat.add_sub_cancel' hkb]
      exact h7


/-! ## The master segment discipline -/

/-- **The master segment discipline**: every contiguous segment of the host
satisfies the anchored single-climb fact (mined exact, 87,690/87,690). -/
def classOK (H : PairSeq) : Prop :=
  ∀ u S v, H = u ++ S ++ v → sclimb S

/-- Truncation closure: segments of a truncation are host segments with
extended right context. -/
theorem classOK_take {H : PairSeq} (h : classOK H) (m : ℕ) :
    classOK (H.take m) := by
  intro u S v heq
  refine h u S (v ++ H.drop m) ?_
  conv_lhs => rw [← List.take_append_drop m H]
  rw [heq]
  simp [List.append_assoc]

/-! ## Shift invariance of the parent relations -/

theorem entry_shift {S : PairSeq} {d j : ℕ} (hj : j < S.length) :
    entry (S.map fun p => (p.1 + d, p.2)) 0 j = entry S 0 j + d
    ∧ entry (S.map fun p => (p.1 + d, p.2)) 1 j = entry S 1 j := by
  unfold entry
  rw [if_pos rfl, if_neg one_ne_zero,
      getD_eq_getElem' _ _ (by rw [List.length_map]; omega),
      List.getElem_map, ← getD_eq_getElem' _ (0,0) hj]
  exact ⟨rfl, rfl⟩

theorem nextrel0_shift_iff {S : PairSeq} {d a b : ℕ} (hb : b < S.length) :
    nextrel0 (S.map fun p => (p.1 + d, p.2)) a b ↔ nextrel0 S a b := by
  unfold nextrel0
  rw [List.length_map]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, h2, h3, ?_, ?_⟩
    · rw [(entry_shift (by omega)).1, (entry_shift hb).1] at h4
      omega
    · intro l hl
      have h6 := h5 l hl
      rw [(entry_shift hb).1, (entry_shift (by omega)).1] at h6
      omega
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, h2, h3, ?_, ?_⟩
    · rw [(entry_shift (by omega)).1, (entry_shift hb).1]
      omega
    · intro l hl
      have h6 := h5 l hl
      rw [(entry_shift hb).1, (entry_shift (by omega)).1]
      omega

theorem rtg_shift_of {S : PairSeq} {d : ℕ} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 (S.map fun p => (p.1 + d, p.2))) a b) :
    Relation.ReflTransGen (nextrel0 S) a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c e hchain hstep ih =>
    have hb := nextrel0_bound hstep
    rw [List.length_map] at hb
    exact ih.tail ((nextrel0_shift_iff hb).1 hstep)

theorem rtg_shift_to {S : PairSeq} {d : ℕ} {a b : ℕ}
    (h : Relation.ReflTransGen (nextrel0 S) a b) :
    Relation.ReflTransGen (nextrel0 (S.map fun p => (p.1 + d, p.2))) a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c e hchain hstep ih =>
    have hb := nextrel0_bound hstep
    exact ih.tail ((nextrel0_shift_iff hb).2 hstep)

theorem le0_shift_iff {S : PairSeq} {d a b : ℕ} :
    le0 (S.map fun p => (p.1 + d, p.2)) a b ↔ le0 S a b := by
  unfold le0
  rw [List.length_map]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, rtg_shift_of h3⟩,
    fun ⟨h1, h2, h3⟩ => ⟨h1, h2, rtg_shift_to h3⟩⟩

theorem idx1_shift {S : PairSeq} {d j : ℕ} :
    idx1 (S.map fun p => (p.1 + d, p.2)) j = idx1 S j := by
  unfold idx1
  by_cases hj : j < S.length
  · rw [(entry_shift hj).2]
  · push Not at hj
    have h1 : (S.map fun p => (p.1 + d, p.2)).getD j (0,0) = (0,0) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none
        (by rw [List.length_map]; omega)]
      rfl
    have h2 : S.getD j (0,0) = (0,0) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
    unfold entry
    rw [if_neg one_ne_zero, if_neg one_ne_zero, h1, h2]

theorem nextrel1_shift_iff {S : PairSeq} {d a b : ℕ} (hb : b < S.length) :
    nextrel1 (S.map fun p => (p.1 + d, p.2)) a b ↔ nextrel1 S a b := by
  unfold nextrel1
  rw [List.length_map]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, h2, h3, ?_, (le0_shift_iff).1 h5, ?_⟩
    · rwa [(entry_shift (by omega)).2, (entry_shift hb).2] at h4
    · intro l hl
      have h7 := h6 l ⟨hl.1, (le0_shift_iff).2 hl.2⟩
      have hlb : l ≤ b := le0_le hl.2
      rwa [(entry_shift hb).2, (entry_shift (by omega)).2] at h7
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨h1, h2, h3, ?_, (le0_shift_iff).2 h5, ?_⟩
    · rwa [(entry_shift (by omega)).2, (entry_shift hb).2]
    · intro l hl
      have hl0 := (le0_shift_iff).1 hl.2
      have hlb : l ≤ b := le0_le hl0
      have h7 := h6 l ⟨hl.1, hl0⟩
      rwa [(entry_shift hb).2, (entry_shift (by omega)).2]

/-- The single-climb discipline is shift-invariant. -/
theorem sclimb_shift {S : PairSeq} {d : ℕ} (h : sclimb S) :
    sclimb (S.map fun p => (p.1 + d, p.2)) := by
  intro r' r hlen1 hnx hi1 hr'1 hr'2 hlev hafter hr1 hr2
  rw [List.length_map] at hlen1 hr'2
  have hlen : (S.map fun p => (p.1 + d, p.2)).length = S.length :=
    List.length_map ..
  rw [hlen, idx1_shift] at hnx hi1
  rw [hlen] at hlev hafter ⊢
  have hgd : ∀ {i}, i < S.length →
      ((S.map fun p => (p.1 + d, p.2)).getD i (0,0)).1
        = (S.getD i (0,0)).1 + d := by
    intro i hi
    rw [getD_eq_getElem' _ _ (by rw [List.length_map]; omega),
        List.getElem_map, ← getD_eq_getElem' _ (0,0) hi]
  have hnx' : nextR S (idx1 S (S.length - 1)) 0 (S.length - 1) := by
    unfold nextR at hnx ⊢
    by_cases hi : idx1 S (S.length - 1) = 0
    · rw [if_pos hi] at hnx ⊢
      exact (nextrel0_shift_iff (by omega)).1 hnx
    · rw [if_neg hi] at hnx ⊢
      exact (nextrel1_shift_iff (by omega)).1 hnx
  have hres := h r' r hlen1 hnx' hi1 hr'1 hr'2 (by
      rw [hgd (by omega), hgd (by omega)] at hlev
      omega)
    (by
      intro l hl1 hl2
      have h7 := hafter l hl1 hl2
      rw [hgd (by omega), hgd (by omega)] at h7
      omega) hr1 hr2
  rw [hgd (by omega), hgd (by omega)]
  omega

/-- Slices of the diagonal ascend, so the single-climb is immediate. -/
theorem classOK_diagSeq (v : ℕ) : classOK (diagSeq 0 v) := by
  intro u S w heq
  have hlen := congrArg List.length heq
  rw [diagSeq0_length] at hlen
  simp at hlen
  have hgd : ∀ i, i < S.length →
      S.getD i (0,0) = (u.length + i, u.length + i) := by
    intro i hi
    have h1 : S.getD i (0,0) = (diagSeq 0 v).getD (u.length + i) (0,0) := by
      rw [heq, getD_middle hi]
    rw [h1, diagSeq0_getD (by omega)]
  intro r' r _hlen1 _hnx _hi1 _hr'1 hr'2 hlev _hafter hr1 hr2
  rw [hgd r' (by omega), hgd (S.length - 1) (by omega)] at hlev
  rw [hgd r (by omega), hgd (S.length - 1) (by omega)]
  have h2 : u.length + r' + 1 = u.length + (S.length - 1) := hlev
  show u.length + r + 1 < u.length + (S.length - 1)
  omega

theorem classOK_Pred {H : PairSeq} (h : classOK H) : classOK (Pred H) := by
  unfold Pred
  by_cases hl : H.length ≤ 1
  · rw [if_pos hl]
    exact h
  · rw [if_neg hl, List.dropLast_eq_take]
    exact classOK_take h _

/-- **Shared-base segment transfer**: if `X` and `Y` agree on their first `m`
entries and the segment of `X` lies entirely within those `m` entries, then
`classOK Y` yields the single-climb conclusion for the segment of `X`. -/
theorem classOK_of_take_eq {X Y : PairSeq} {m : ℕ}
    (hXY : X.take m = Y.take m) (hY : classOK Y) :
    ∀ u S v, X = u ++ S ++ v → u.length + S.length ≤ m → sclimb S := by
  intro u S v heq hm
  have hctxlen : (u ++ S).length = u.length + S.length := by simp
  have hXctx : X.take (u.length + S.length) = u ++ S := by
    rw [heq, ← hctxlen, List.take_left]
  have hYctx : Y.take (u.length + S.length) = u ++ S := by
    have h1 : Y.take (u.length + S.length)
        = (Y.take m).take (u.length + S.length) := by
      rw [List.take_take, min_eq_left hm]
    rw [h1, ← hXY, List.take_take, min_eq_left hm]
    exact hXctx
  have hYeq : Y = u ++ S ++ Y.drop (u.length + S.length) := by
    conv_lhs => rw [← List.take_append_drop (u.length + S.length) Y]
    rw [hYctx]
  exact hY u S _ hYeq

theorem sclimb_nil : sclimb ([] : PairSeq) := by
  intro r' r h _ _ _ _ _ _ _ _
  simp at h

/-- `classOK` restricts to any infix. -/
theorem classOK_infix {H u H' v : PairSeq} (h : classOK H)
    (heq : H = u ++ H' ++ v) : classOK H' := by
  intro u' S v' heq'
  refine h (u ++ u') S (v' ++ v) ?_
  rw [heq, heq']
  simp [List.append_assoc]

/-- The master segment discipline is shift-invariant. -/
theorem classOK_shift {B : PairSeq} {d : ℕ} (h : classOK B) :
    classOK (B.map fun p => (p.1 + d, p.2)) := by
  intro u S v heq
  obtain ⟨l1, v0, hB, hl1, hv⟩ := List.map_eq_append_iff.mp heq
  obtain ⟨u0, S0, hl1e, hu, hS⟩ := List.map_eq_append_iff.mp hl1
  subst hl1e
  have h4 := sclimb_shift (d := d) (h u0 S0 v0 hB)
  rwa [hS] at h4

/-- A segment lying inside an infix window transfers to the infix. -/
theorem classOK_within_infix {X u C v : PairSeq}
    (hX : X = u ++ C ++ v) (hC : classOK C) :
    ∀ (pre S post : PairSeq),
      X = pre ++ S ++ post →
      u.length ≤ pre.length →
      pre.length + S.length ≤ u.length + C.length →
      sclimb S := by
  intro pre S post heq hlo hhi
  have h1 : X.take u.length = u := by
    rw [hX, List.take_append_of_le_length (by rw [List.length_append]; omega),
        List.take_append_of_le_length le_rfl, List.take_length]
  have h2 : X.take u.length = pre.take u.length := by
    rw [heq, List.take_append_of_le_length (by rw [List.length_append]; omega),
        List.take_append_of_le_length hlo]
  have hpu : pre.take u.length = u := h2.symm.trans h1
  have hpre : pre = u ++ pre.drop u.length := by
    conv_lhs => rw [← List.take_append_drop u.length pre]
    rw [hpu]
  have hcancel : C ++ v = pre.drop u.length ++ (S ++ post) := by
    have h3 := hX.symm.trans heq
    rw [hpre] at h3
    simp only [List.append_assoc] at h3
    exact List.append_cancel_left h3
  have hlen2 : (pre.drop u.length).length + S.length ≤ C.length := by
    rw [List.length_drop]
    omega
  have hkey : C.take ((pre.drop u.length).length + S.length)
      = pre.drop u.length ++ S := by
    have h4 : (C ++ v).take ((pre.drop u.length).length + S.length)
        = C.take ((pre.drop u.length).length + S.length) :=
      List.take_append_of_le_length hlen2
    rw [hcancel] at h4
    rw [← h4, List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
        Nat.add_sub_cancel_left, List.take_append_of_le_length le_rfl,
        List.take_length]
  refine hC (pre.drop u.length) S
    (C.drop ((pre.drop u.length).length + S.length)) ?_
  conv_lhs => rw [← List.take_append_drop
    ((pre.drop u.length).length + S.length) C]
  rw [hkey]

/-- `classOK` for the copy expansion: segments within the shared base or a
single copy transfer unconditionally; copy-spanning segments are the
explicit hypothesis `hspan` (mined shapes: head in the prefix, last column
at a copy root). -/
theorem classOK_copyExp {G B : PairSeq} {lp : ℕ × ℕ} {d0 n : ℕ} (hn : 1 ≤ n)
    (hM : classOK (G ++ B ++ [lp]))
    (hspan : ∀ (u S v : PairSeq),
      copyExp G B d0 n = u ++ S ++ v →
      G.length + B.length < u.length + S.length →
      (¬ ∃ k, k < n ∧ G.length + k * B.length ≤ u.length ∧
        u.length + S.length ≤ G.length + (k + 1) * B.length) →
      sclimb S) :
    classOK (copyExp G B d0 n) := by
  have htkX : (copyExp G B d0 n).take (G.length + B.length) = G ++ B := by
    have h := copyExp_take_at (G := G) (B := B) (d0 := d0) (n := n)
      (k := 0) (q := B.length) (by omega) le_rfl
    simpa [copyExp] using h
  have htkM : (G ++ B ++ [lp]).take (G.length + B.length) = G ++ B := by
    have h := hostM_take_at (G := G) (B := B) (lp := lp) (q := B.length) le_rfl
    rwa [List.take_length] at h
  have htk : (copyExp G B d0 n).take (G.length + B.length)
      = (G ++ B ++ [lp]).take (G.length + B.length) := by rw [htkX, htkM]
  intro u S v heq
  by_cases hc1 : u.length + S.length ≤ G.length + B.length
  · exact classOK_of_take_eq htk hM u S v heq hc1
  by_cases hc2 : ∃ k, k < n ∧ G.length + k * B.length ≤ u.length ∧
      u.length + S.length ≤ G.length + (k + 1) * B.length
  · obtain ⟨k, hk, hlo, hhi⟩ := hc2
    have hwin := copyExp_split G B d0 (le_of_lt hk)
    obtain ⟨m, hm⟩ : ∃ m, n - k = m + 1 := ⟨n - k - 1, by omega⟩
    rw [hm, List.range_succ_eq_map, List.flatMap_cons] at hwin
    simp only [Nat.add_zero] at hwin
    rw [← List.append_assoc] at hwin
    have hCk : classOK (B.map fun p => (p.1 + k * d0, p.2)) :=
      classOK_shift (classOK_infix (u := G) (H' := B) (v := [lp]) hM rfl)
    refine classOK_within_infix hwin hCk u S v heq ?_ ?_
    · rw [copyExp_length]
      exact hlo
    · rw [copyExp_length, List.length_map]
      have hsm : (k + 1) * B.length = k * B.length + B.length :=
        Nat.succ_mul k B.length
      omega
  · exact hspan u S v heq (by omega) hc2

/-- Windows of lists agreeing on a prefix agree. -/
theorem take_eq_window {α : Type*} {X Y : List α} {m s w : ℕ}
    (hXY : X.take m = Y.take m) (hw : s + w ≤ m) :
    (X.drop s).take w = (Y.drop s).take w := by
  rw [List.take_drop, List.take_drop]
  have h2 : X.take (s + w) = Y.take (s + w) := by
    have h3 := congrArg (List.take (s + w)) hXY
    rwa [List.take_take, List.take_take, min_eq_left hw] at h3
  rw [h2]

/-- **Spanning discharge**: a copy-crossing segment of the copy expansion
satisfies the anchored single-climb, given the mined block facts. -/
theorem hspan_discharge {G R : PairSeq} {v0 w0 : ℕ} {lp : ℕ × ℕ} {d0 n : ℕ}
    (hn : 1 ≤ n)
    (hdom : ∀ p ∈ R, v0 < p.1)
    (hM : classOK (G ++ ((v0,w0) :: R) ++ [lp]))
    (hd0 : d0 = 0 ∨ (0 < d0 ∧ w0 < lp.2 ∧ lp.1 = v0 + d0 ∧
      nextrel1 (G ++ ((v0,w0) :: R) ++ [lp]) G.length
        ((G ++ ((v0,w0) :: R) ++ [lp]).length - 1)))
    (hBF1 : ∀ q, 0 < q → q < ((v0,w0) :: R).length →
      le0 ((v0,w0) :: R) 0 q → 0 < (((v0,w0) :: R).getD q (0,0)).2 →
      w0 < (((v0,w0) :: R).getD q (0,0)).2)
    (hBF2 : 0 < d0 → ∀ q, q < ((v0,w0) :: R).length →
      w0 ≤ (((v0,w0) :: R).getD q (0,0)).2)
    (hMF3 : 0 < d0 → ∀ a, a < G.length →
      le0 (G ++ ((v0,w0) :: R) ++ [lp]) a G.length →
      (G.getD a (0,0)).2 < w0 →
      ∀ h, a < h → h < G.length → (G.getD h (0,0)).1 + 1 < lp.1)
    (hBF45 : 0 < w0 → 0 < d0 → ∀ q, 0 < q → q < ((v0,w0) :: R).length →
      (((v0,w0) :: R).getD q (0,0)).1 + 1 < v0 + 2 * d0) :
    ∀ u S v, copyExp G ((v0,w0) :: R) d0 n = u ++ S ++ v →
      G.length + ((v0,w0) :: R).length < u.length + S.length →
      (¬ ∃ k, k < n ∧ G.length + k * ((v0,w0) :: R).length ≤ u.length ∧
        u.length + S.length ≤ G.length + (k + 1) * ((v0,w0) :: R).length) →
      sclimb S := by
  intro u S v heq hsp hnc r' r hS1 hnx hi1 hr'pos hr'lt hlev hafter hrpos hrlt
  set B : PairSeq := (v0,w0) :: R with hBdef
  have hL1 : 1 ≤ B.length := by simp [hBdef]
  -- length bookkeeping
  have hXlen : (copyExp G B d0 n).length = G.length + n * B.length :=
    copyExp_length ..
  have hlen : u.length + S.length + v.length = G.length + n * B.length := by
    have h := congrArg List.length heq
    rw [hXlen] at h
    simp at h
    clear hnc
    omega
  have hht : u.length + (S.length - 1) < G.length + n * B.length := by
    clear hnc
    omega
  have htc : G.length + B.length ≤ u.length + (S.length - 1) := by
    clear hnc
    omega
  -- copy coordinates of t
  obtain ⟨kt, qt, hqtL, hdm⟩ : ∃ kt qt, qt < B.length ∧
      u.length + (S.length - 1) - G.length = B.length * kt + qt :=
    ⟨_, _, Nat.mod_lt _ (by omega),
      (Nat.div_add_mod (u.length + (S.length - 1) - G.length) B.length).symm⟩
  have hdecomp : u.length + (S.length - 1)
      = G.length + (B.length * kt + qt) := by
    clear hnc
    omega
  have hktn : kt < n := by
    have h1 : B.length * kt < B.length * n := by
      have hcomm : n * B.length = B.length * n := Nat.mul_comm n B.length
      clear hnc
      omega
    exact Nat.lt_of_mul_lt_mul_left h1
  have hkt1 : 1 ≤ kt := by
    rcases Nat.eq_zero_or_pos kt with h0 | h1
    · rw [h0, Nat.mul_zero] at hdm
      clear hnc
      omega
    · exact h1
  -- the instance's parent edge
  have hnx1 : nextrel1 S 0 (S.length - 1) := by
    unfold nextR at hnx
    rw [if_neg (by rw [hi1]; exact one_ne_zero)] at hnx
    exact hnx
  have he1pos : 0 < entry S 1 (S.length - 1) := by
    by_contra h0
    unfold idx1 at hi1
    rw [if_neg h0] at hi1
    exact absurd hi1 zero_ne_one
  -- entries of S are X-entries
  have hentS : ∀ i j, j < S.length →
      entry S i j = entry (copyExp G B d0 n) i (u.length + j) :=
    fun i j hj => entry_seg heq hj
  have hBR : B.length = R.length + 1 := by
    rw [hBdef]
    rfl
  have hcm : B.length * kt = kt * B.length := Nat.mul_comm ..
  -- Step A2: t sits at a copy root
  have hqt0 : qt = 0 := by
    by_contra hqt
    have hqtpos : 0 < qt := Nat.pos_of_ne_zero hqt
    -- the segment head lies before the copy-kt root
    have hsρ : u.length < G.length + kt * B.length := by
      by_contra hge
      push Not at hge
      refine hnc ⟨kt, hktn, hge, ?_⟩
      have hsucc : (kt + 1) * B.length = kt * B.length + B.length := by
        rw [Nat.add_mul, Nat.one_mul]
      clear hnc
      omega
    obtain ⟨ρ, hρ⟩ : ∃ ρ, u.length + ρ = G.length + kt * B.length :=
      ⟨G.length + kt * B.length - u.length, by clear hnc; omega⟩
    have hρpos : 0 < ρ := by clear hnc; omega
    have hρt : ρ + qt = S.length - 1 := by clear hnc; omega
    -- the root and window entries
    have hce0 := entry_copyExp (G := G) (B := B) (d0 := d0) (n := n)
      (k := kt) (q := 0) hktn (by clear hnc; omega)
    have hroot0 : entry S 0 ρ = v0 + kt * d0 := by
      rw [hentS 0 ρ (by clear hnc; omega),
          show u.length + ρ = G.length + (kt * B.length + 0) by clear hnc; omega,
          hce0.1, hBdef, List.getD_cons_zero]
    have hroot1 : entry S 1 ρ = w0 := by
      rw [hentS 1 ρ (by clear hnc; omega),
          show u.length + ρ = G.length + (kt * B.length + 0) by clear hnc; omega,
          hce0.2, hBdef, List.getD_cons_zero]
    -- pivot condition: the copy-kt interior sits strictly above the root
    have hpiv : ∀ y, ρ < y → y ≤ S.length - 1 →
        entry S 0 ρ < entry S 0 y := by
      intro y hy1 hy2
      obtain ⟨qy, hqy⟩ : ∃ qy, y = ρ + qy := ⟨y - ρ, by clear hnc; omega⟩
      have hey : entry S 0 y = (B.getD qy (0,0)).1 + kt * d0 := by
        rw [hentS 0 y (by clear hnc; omega),
            show u.length + y = G.length + (kt * B.length + qy) by
              clear hnc; omega]
        exact (entry_copyExp hktn (by clear hnc; omega)).1
      rw [hroot0, hey]
      rcases qy with _ | qy'
      · omega
      · rw [hBdef, List.getD_cons_succ]
        have hmem : R.getD qy' (0,0) ∈ R := by
          rw [getD_eq_getElem' _ _ (by clear hnc; omega)]
          exact List.getElem_mem ..
        have hv := hdom _ hmem
        clear hnc
        omega
    -- the chain into t passes through the root
    have hle0S : le0 S 0 (S.length - 1) := hnx1.2.2.2.2.1
    have hle0ρ := le0_through_pivot hle0S hρpos (by clear hnc; omega) hpiv
    have hmax := hnx1.2.2.2.2.2 ρ ⟨hρpos, hle0ρ⟩
    rw [hroot1] at hmax
    -- the suffix from the root is the truncated shifted block
    have hwin : S.drop ρ
        = (B.map fun p => (p.1 + kt * d0, p.2)).take (qt + 1) := by
      have h1 : (copyExp G B d0 n).drop u.length = S ++ v := by
        rw [heq, List.append_assoc, List.drop_left]
      have h2 : (copyExp G B d0 n).drop (u.length + ρ) = S.drop ρ ++ v := by
        rw [← List.drop_drop, h1, List.drop_append,
            show ρ - S.length = 0 by clear hnc; omega, List.drop_zero]
      rw [hρ] at h2
      have hsplit := copyExp_split G B d0 (le_of_lt hktn)
      obtain ⟨m, hm⟩ : ∃ m, n - kt = m + 1 := ⟨n - kt - 1, by clear hnc; omega⟩
      rw [hm, List.range_succ_eq_map, List.flatMap_cons] at hsplit
      simp only [Nat.add_zero] at hsplit
      have h3 : (copyExp G B d0 n).drop (G.length + kt * B.length)
          = (B.map fun p => (p.1 + kt * d0, p.2))
            ++ ((List.map Nat.succ (List.range m)).flatMap
                fun i => B.map fun p => (p.1 + (kt + i) * d0, p.2)) := by
        conv_lhs => rw [hsplit]
        rw [show G.length + kt * B.length = (copyExp G B d0 kt).length from
              (copyExp_length ..).symm,
            List.drop_left]
      have h4 := h2.symm.trans h3
      have h5 := congrArg (List.take (qt + 1)) h4
      rw [List.take_append_of_le_length (by
            rw [List.length_drop]
            clear hnc
            omega),
          List.take_append_of_le_length (by
            rw [List.length_map]
            clear hnc
            omega),
          List.take_of_length_le (by
            rw [List.length_drop]
            clear hnc
            omega)] at h5
      exact h5
    -- transfer the chain to the unshifted block
    have hd1 : le0 (S.drop ρ) (ρ - ρ) ((S.length - 1) - ρ) :=
      (le0_drop_iff le_rfl (by clear hnc; omega) (by clear hnc; omega)).2 hle0ρ
    rw [Nat.sub_self, show S.length - 1 - ρ = qt by clear hnc; omega,
        hwin] at hd1
    have hd2 : le0 (B.map fun p => (p.1 + kt * d0, p.2)) 0 qt :=
      (le0_take_iff (by omega)
        (by rw [List.length_map]; clear hnc; omega)).1 hd1
    have hd3 : le0 B 0 qt := (le0_shift_iff).1 hd2
    -- BF1 against the parent-edge maximality
    have he1t : entry S 1 (S.length - 1) = (B.getD qt (0,0)).2 := by
      rw [hentS 1 _ (by clear hnc; omega),
          show u.length + (S.length - 1) = G.length + (kt * B.length + qt) by
            clear hnc; omega]
      exact (entry_copyExp hktn hqtL).2
    have hbf := hBF1 qt hqtpos hqtL hd3 (by rw [← he1t]; exact he1pos)
    rw [← he1t] at hbf
    clear hnc
    omega
  -- Step A3: the segment head lies in the prefix
  have hslt : u.length < G.length := by
    by_contra hge
    push Not at hge
    obtain ⟨ks, qs, hqsL, hdms⟩ : ∃ ks qs, qs < B.length ∧
        u.length - G.length = B.length * ks + qs :=
      ⟨_, _, Nat.mod_lt _ (by clear hnc; omega),
        (Nat.div_add_mod (u.length - G.length) B.length).symm⟩
    have hcms : B.length * ks = ks * B.length := Nat.mul_comm ..
    have hksn : ks < n := by
      have h1 : B.length * ks < B.length * n := by
        have hcomm : n * B.length = B.length * n := Nat.mul_comm ..
        clear hnc
        omega
      exact Nat.lt_of_mul_lt_mul_left h1
    have hhead : entry S 1 0 = (B.getD qs (0,0)).2 := by
      rw [hentS 1 0 (by clear hnc; omega),
          show u.length + 0 = G.length + (ks * B.length + qs) by
            clear hnc; omega]
      exact (entry_copyExp hksn hqsL).2
    have he1t : entry S 1 (S.length - 1) = w0 := by
      rw [hentS 1 _ (by clear hnc; omega),
          show u.length + (S.length - 1) = G.length + (kt * B.length + 0) by
            clear hnc; omega,
          (entry_copyExp hktn (by clear hnc; omega)).2, hBdef,
          List.getD_cons_zero]
    have hC1 := hnx1.2.2.2.1
    rw [he1t, hhead] at hC1
    rcases Nat.eq_zero_or_pos qs with hqs0 | hqspos
    · rw [hqs0, hBdef, List.getD_cons_zero] at hC1
      exact absurd hC1 (lt_irrefl w0)
    · rcases hd0 with hd0z | ⟨hd0p, -, -, -⟩
      · have hle0S : le0 S 0 (S.length - 1) := hnx1.2.2.2.2.1
        obtain ⟨-, -, hch⟩ := hle0S
        rcases Relation.ReflTransGen.cases_tail hch with he | ⟨y, hy, hyz⟩
        · clear hnc
          omega
        · have hylt : y < S.length - 1 := nextrel0_lt hyz
          have hinc := nextrel0_entry0_less hyz
          have he0t : entry S 0 (S.length - 1) = v0 := by
            rw [hentS 0 _ (by clear hnc; omega),
                show u.length + (S.length - 1)
                  = G.length + (kt * B.length + 0) by clear hnc; omega,
                (entry_copyExp hktn (by clear hnc; omega)).1, hBdef,
                List.getD_cons_zero, hd0z, Nat.mul_zero, Nat.add_zero]
          obtain ⟨ky, qy, hqyL, hdmy⟩ : ∃ ky qy, qy < B.length ∧
              u.length + y - G.length = B.length * ky + qy :=
            ⟨_, _, Nat.mod_lt _ (by clear hnc; omega),
              (Nat.div_add_mod (u.length + y - G.length) B.length).symm⟩
          have hcmy : B.length * ky = ky * B.length := Nat.mul_comm ..
          have hkyn : ky < n := by
            have h1 : B.length * ky < B.length * n := by
              have hcomm : n * B.length = B.length * n := Nat.mul_comm ..
              clear hnc
              omega
            exact Nat.lt_of_mul_lt_mul_left h1
          have hey : entry S 0 y = (B.getD qy (0,0)).1 := by
            rw [hentS 0 y (by clear hnc; omega),
                show u.length + y = G.length + (ky * B.length + qy) by
                  clear hnc; omega,
                (entry_copyExp hkyn hqyL).1, hd0z, Nat.mul_zero,
                Nat.add_zero]
          rw [hey, he0t] at hinc
          rcases Nat.eq_zero_or_pos qy with hqy0 | hqypos
          · rw [hqy0, hBdef, List.getD_cons_zero] at hinc
            exact absurd hinc (lt_irrefl v0)
          · obtain ⟨qy', rfl⟩ : ∃ qy', qy = qy' + 1 :=
              ⟨qy - 1, by clear hnc; omega⟩
            rw [hBdef, List.getD_cons_succ] at hinc
            have hmem : R.getD qy' (0,0) ∈ R := by
              rw [getD_eq_getElem' _ _ (by clear hnc; omega)]
              exact List.getElem_mem ..
            have hv := hdom _ hmem
            clear hnc
            omega
      · have hbf2 := hBF2 hd0p qs hqsL
        clear hnc
        omega
  subst hqt0
  -- shared bookkeeping for the possible shapes
  have hgdS : ∀ j, j < S.length →
      S.getD j (0,0) = (copyExp G B d0 n).getD (u.length + j) (0,0) := by
    intro j hj
    rw [heq, getD_middle hj]
  have hgt : S.getD (S.length - 1) (0,0) = (v0 + kt * d0, w0) := by
    rw [hgdS _ (by clear hnc; omega),
        show u.length + (S.length - 1) = G.length + (kt * B.length + 0) by
          clear hnc; omega,
        copyExp_getD_copy hktn (by clear hnc; omega), hBdef,
        List.getD_cons_zero]
  have hewt : entry S 1 (S.length - 1) = w0 := by
    unfold entry
    rw [if_neg one_ne_zero, hgt]
  have hw0pos : 0 < w0 := hewt ▸ he1pos
  have htkXM : (copyExp G B d0 n).take (G.length + B.length)
      = (G ++ B ++ [lp]).take (G.length + B.length) := by
    have htkX : (copyExp G B d0 n).take (G.length + B.length) = G ++ B := by
      have h := copyExp_take_at (G := G) (B := B) (d0 := d0) (n := n)
        (k := 0) (q := B.length) (by omega) le_rfl
      simpa [copyExp] using h
    have htkM : (G ++ B ++ [lp]).take (G.length + B.length) = G ++ B := by
      have h := hostM_take_at (G := G) (B := B) (lp := lp)
        (q := B.length) le_rfl
      rwa [List.take_length] at h
    rw [htkX, htkM]
  have hcopy_ge : ∀ j, j < S.length → G.length ≤ u.length + j →
      v0 ≤ entry S 0 j := by
    intro j hj hjg
    obtain ⟨kj, qj, hqjL, hdmj⟩ : ∃ kj qj, qj < B.length ∧
        u.length + j - G.length = B.length * kj + qj :=
      ⟨_, _, Nat.mod_lt _ (by clear hnc; omega),
        (Nat.div_add_mod (u.length + j - G.length) B.length).symm⟩
    have hcmj : B.length * kj = kj * B.length := Nat.mul_comm ..
    have hkjn : kj < n := by
      have h1 : B.length * kj < B.length * n := by
        have hcomm : n * B.length = B.length * n := Nat.mul_comm ..
        clear hnc
        omega
      exact Nat.lt_of_mul_lt_mul_left h1
    have hej : entry S 0 j = (B.getD qj (0,0)).1 + kj * d0 := by
      rw [hentS 0 j hj,
          show u.length + j = G.length + (kj * B.length + qj) by
            clear hnc; omega]
      exact (entry_copyExp hkjn hqjL).1
    rw [hej]
    rcases Nat.eq_zero_or_pos qj with hqj0 | hqjpos
    · rw [hqj0, hBdef, List.getD_cons_zero]
      show v0 ≤ v0 + kj * d0
      clear hnc
      omega
    · obtain ⟨qj', rfl⟩ : ∃ qj', qj = qj' + 1 :=
        ⟨qj - 1, by clear hnc; omega⟩
      rw [hBdef, List.getD_cons_succ]
      have hmem : R.getD qj' (0,0) ∈ R := by
        rw [getD_eq_getElem' _ _ (by clear hnc; omega)]
        exact List.getElem_mem ..
      have hv := hdom _ hmem
      clear hnc
      omega
  -- conclusion
  show (S.getD r (0,0)).1 + 1 < (S.getD (S.length - 1) (0,0)).1
  rcases hd0 with hd0z | ⟨hd0p, hwlp, hlp1, hnxM⟩
  · -- F3: d0 = 0
    have hg2 : (S.getD (S.length - 1) (0,0)).1 = v0 := by
      rw [hgt, hd0z]
      simp
    have het0 : entry S 0 (S.length - 1) = v0 := by
      unfold entry
      rw [if_pos rfl]
      exact hg2
    -- the climb column lies in the prefix
    have hr'g : u.length + r' < G.length := by
      by_contra hge'
      push Not at hge'
      have h6 := hcopy_ge r' (by clear hnc; omega) hge'
      unfold entry at h6
      rw [if_pos rfl] at h6
      clear hnc
      omega
    -- the copy-0 root inside S
    obtain ⟨gs, hgs⟩ : ∃ gs, u.length + gs = G.length :=
      ⟨G.length - u.length, by clear hnc; omega⟩
    have hgs1 : 1 ≤ gs := by clear hnc; omega
    have hgsS : gs + 1 ≤ S.length := by clear hnc; omega
    have hgsroot : S.getD gs (0,0) = (v0 + 0 * d0, w0) := by
      rw [hgdS _ (by clear hnc; omega),
          show u.length + gs = G.length + (0 * B.length + 0) by
            clear hnc; omega,
          copyExp_getD_copy (show 0 < n by omega) (by clear hnc; omega),
          hBdef, List.getD_cons_zero]
    have hgsv : (S.getD gs (0,0)).1 = v0 := by
      rw [hgsroot]
      simp
    have hgsw : (S.getD gs (0,0)).2 = w0 := by
      rw [hgsroot]
    have hegs : entry S 0 gs = v0 := by
      unfold entry
      rw [if_pos rfl]
      exact hgsv
    have hewgs : entry S 1 gs = w0 := by
      unfold entry
      rw [if_neg one_ne_zero]
      exact hgsw
    -- sclimb of the prefix segment through classOK M
    have hdecT : copyExp G B d0 n
        = u ++ S.take (gs + 1) ++ (S.drop (gs + 1) ++ v) := by
      calc copyExp G B d0 n = u ++ S ++ v := heq
      _ = u ++ (S.take (gs + 1) ++ S.drop (gs + 1)) ++ v := by
          rw [List.take_append_drop]
      _ = u ++ S.take (gs + 1) ++ (S.drop (gs + 1) ++ v) := by
          simp only [List.append_assoc]
    have hsclT : sclimb (S.take (gs + 1)) :=
      classOK_of_take_eq htkXM hM u (S.take (gs + 1)) _ hdecT (by
        rw [List.length_take]
        clear hnc
        omega)
    have hTlen : (S.take (gs + 1)).length = gs + 1 := by
      rw [List.length_take]
      clear hnc
      omega
    -- the S-chain's last edge lands from the prefix
    have hle0S : le0 S 0 (S.length - 1) := hnx1.2.2.2.2.1
    obtain ⟨-, -, hch⟩ := hle0S
    rcases Relation.ReflTransGen.cases_tail hch with he | ⟨y, hy, hyz⟩
    · exfalso
      clear hnc
      omega
    · have hylt := nextrel0_lt hyz
      have hinc := nextrel0_entry0_less hyz
      have hyg : u.length + y < G.length := by
        by_contra hyge
        push Not at hyge
        have h6 := hcopy_ge y (by clear hnc; omega) hyge
        rw [het0] at hinc
        clear hnc
        omega
      have hygs : y < gs := by clear hnc; omega
      have hchT : Relation.ReflTransGen (nextrel0 (S.take (gs + 1))) 0 y :=
        rtg_nextrel0_to_take hy (by omega)
      have hedge : nextrel0 (S.take (gs + 1)) y gs := by
        refine ⟨by rw [hTlen]; omega, by rw [hTlen]; omega, hygs, ?_, ?_⟩
        · rw [entry_take (by omega), entry_take (by omega), hegs, ← het0]
          exact hinc
        · intro l hl
          rw [entry_take (by omega), entry_take (by omega), hegs]
          have h6 := hyz.2.2.2.2 l ⟨hl.1, by clear hnc; omega⟩
          rwa [het0] at h6
      have hle0T : le0 (S.take (gs + 1)) 0 gs :=
        ⟨by rw [hTlen]; omega, by rw [hTlen]; omega, hchT.tail hedge⟩
      have hmaxT : ∀ jj, 0 < jj ∧ le0 (S.take (gs + 1)) jj gs →
          entry (S.take (gs + 1)) 1 gs ≤ entry (S.take (gs + 1)) 1 jj := by
        intro jj hjj
        obtain ⟨hjj0, hjle⟩ := hjj
        have hjjgs : jj ≤ gs := le0_le hjle
        rw [entry_take (by omega), entry_take (by omega), hewgs]
        rcases eq_or_lt_of_le hjjgs with hje | hjlt
        · rw [hje, hewgs]
        · have hjS : le0 S jj gs :=
            (le0_take_iff (by omega) (by clear hnc; omega)).1 hjle
          obtain ⟨-, -, hchj⟩ := hjS
          rcases Relation.ReflTransGen.cases_tail hchj with he2 | ⟨x, hx, hxe⟩
          · exfalso
            omega
          · have hxlt := nextrel0_lt hxe
            have hxg : entry S 0 x < v0 := by
              have h6 := nextrel0_entry0_less hxe
              rwa [hegs] at h6
            have hedge2 : nextrel0 S x (S.length - 1) := by
              refine ⟨by clear hnc; omega, by clear hnc; omega,
                by clear hnc; omega, ?_, ?_⟩
              · rw [het0]
                exact hxg
              · intro l hl
                rw [het0]
                by_cases hlg : l < gs
                · have h6 := hxe.2.2.2.2 l ⟨hl.1, hlg⟩
                  rwa [hegs] at h6
                · push Not at hlg
                  exact hcopy_ge l (by clear hnc; omega) (by clear hnc; omega)
            have hjt : le0 S jj (S.length - 1) :=
              ⟨by clear hnc; omega, by clear hnc; omega, hx.tail hedge2⟩
            have h7 := hnx1.2.2.2.2.2 jj ⟨hjj0, hjt⟩
            rwa [hewt] at h7
      have hnxT : nextrel1 (S.take (gs + 1)) 0 gs := by
        refine ⟨by rw [hTlen]; omega, by rw [hTlen]; omega, by omega, ?_,
          hle0T, hmaxT⟩
        rw [entry_take (by omega), entry_take (by omega), hewgs]
        have hC1 := hnx1.2.2.2.1
        rwa [hewt] at hC1
      have hi1T : idx1 (S.take (gs + 1)) ((S.take (gs + 1)).length - 1)
          = 1 := by
        rw [hTlen, Nat.add_sub_cancel]
        unfold idx1
        rw [if_pos (by rw [entry_take (by omega), hewgs]; exact hw0pos)]
      have hnxRT : nextR (S.take (gs + 1))
          (idx1 (S.take (gs + 1)) ((S.take (gs + 1)).length - 1)) 0
          ((S.take (gs + 1)).length - 1) := by
        rw [hi1T]
        unfold nextR
        rw [if_neg one_ne_zero, hTlen, Nat.add_sub_cancel]
        exact hnxT
      have hconc := hsclT r' r (by rw [hTlen]; omega) hnxRT hi1T hr'pos
        (by rw [hTlen]; clear hnc; omega)
        (by
          rw [hTlen, Nat.add_sub_cancel, getD_take (by clear hnc; omega),
              getD_take (by omega), hgsv, ← hg2]
          exact hlev)
        (by
          intro l hl1 hl2
          rw [hTlen] at hl2
          rw [hTlen, Nat.add_sub_cancel, getD_take (by omega),
              getD_take (by clear hnc; omega), hgsv]
          have h6 := hafter l hl1 (by clear hnc; omega)
          rwa [hg2] at h6)
        hrpos hrlt
      rw [hTlen, Nat.add_sub_cancel, getD_take (by clear hnc; omega),
          getD_take (by omega), hgsv] at hconc
      rw [hg2]
      exact hconc
  · -- F2: d0 > 0
    have hMlen : (G ++ B ++ [lp]).length = G.length + B.length + 1 :=
      hostM_length ..
    -- strict copy-region lower bound
    have hcopy_gt : ∀ j, j < S.length → G.length < u.length + j →
        v0 < entry S 0 j := by
      intro j hj hjg
      obtain ⟨kj, qj, hqjL, hdmj⟩ : ∃ kj qj, qj < B.length ∧
          u.length + j - G.length = B.length * kj + qj :=
        ⟨_, _, Nat.mod_lt _ (by clear hnc; omega),
          (Nat.div_add_mod (u.length + j - G.length) B.length).symm⟩
      have hcmj : B.length * kj = kj * B.length := Nat.mul_comm ..
      have hkjn : kj < n := by
        have h1 : B.length * kj < B.length * n := by
          have hcomm : n * B.length = B.length * n := Nat.mul_comm ..
          clear hnc
          omega
        exact Nat.lt_of_mul_lt_mul_left h1
      have hej : entry S 0 j = (B.getD qj (0,0)).1 + kj * d0 := by
        rw [hentS 0 j hj,
            show u.length + j = G.length + (kj * B.length + qj) by
              clear hnc; omega]
        exact (entry_copyExp hkjn hqjL).1
      rw [hej]
      rcases Nat.eq_zero_or_pos qj with hqj0 | hqjpos
      · have hkj1 : 1 ≤ kj := by
          rcases Nat.eq_zero_or_pos kj with h0 | h1
          · rw [h0, Nat.mul_zero] at hdmj
            exfalso
            clear hnc
            omega
          · exact h1
        have hposj : 0 < kj * d0 := Nat.mul_pos hkj1 hd0p
        rw [hqj0, hBdef, List.getD_cons_zero]
        show v0 < v0 + kj * d0
        clear hnc
        omega
      · obtain ⟨qj', rfl⟩ : ∃ qj', qj = qj' + 1 :=
          ⟨qj - 1, by clear hnc; omega⟩
        rw [hBdef, List.getD_cons_succ]
        have hmem : R.getD qj' (0,0) ∈ R := by
          rw [getD_eq_getElem' _ _ (by clear hnc; omega)]
          exact List.getElem_mem ..
        have hv := hdom _ hmem
        clear hnc
        omega
    -- the copy-0 root inside S
    obtain ⟨gs, hgs⟩ : ∃ gs, u.length + gs = G.length :=
      ⟨G.length - u.length, by clear hnc; omega⟩
    have hgs1 : 1 ≤ gs := by clear hnc; omega
    have hgsS : gs + 1 ≤ S.length := by clear hnc; omega
    have hgsroot : S.getD gs (0,0) = (v0 + 0 * d0, w0) := by
      rw [hgdS _ (by clear hnc; omega),
          show u.length + gs = G.length + (0 * B.length + 0) by
            clear hnc; omega,
          copyExp_getD_copy (show 0 < n by omega) (by clear hnc; omega),
          hBdef, List.getD_cons_zero]
    have hgsv : (S.getD gs (0,0)).1 = v0 := by
      rw [hgsroot]
      simp
    have hegs : entry S 0 gs = v0 := by
      unfold entry
      rw [if_pos rfl]
      exact hgsv
    -- the chain reaches the copy-0 root
    have hpiv : ∀ y, gs < y → y ≤ S.length - 1 →
        entry S 0 gs < entry S 0 y := by
      intro y hy1 hy2
      rw [hegs]
      exact hcopy_gt y (by clear hnc; omega) (by clear hnc; omega)
    have hle0S : le0 S 0 (S.length - 1) := hnx1.2.2.2.2.1
    have hle0gs : le0 S 0 gs :=
      le0_to_pivot hle0S (by omega) (by clear hnc; omega) hpiv
    -- transfer to the host M
    have hSwin : S.take (gs + 1)
        = ((copyExp G B d0 n).drop u.length).take (gs + 1) := by
      have h1 : (copyExp G B d0 n).drop u.length = S ++ v := by
        rw [heq, List.append_assoc, List.drop_left]
      rw [h1, List.take_append_of_le_length (by clear hnc; omega)]
    have hMwin : S.take (gs + 1)
        = ((G ++ B ++ [lp]).drop u.length).take (gs + 1) := by
      rw [hSwin]
      exact take_eq_window htkXM (by clear hnc; omega)
    have hle0M : le0 (G ++ B ++ [lp]) u.length G.length := by
      have h8 : le0 ((G ++ B ++ [lp]).drop u.length) 0 gs := by
        have h9 := (le0_take_iff (m := gs + 1) (by omega)
          (by clear hnc; omega)).2 hle0gs
        rw [hMwin] at h9
        exact (le0_take_iff (m := gs + 1) (by omega)
          (by rw [List.length_drop, hMlen]; clear hnc; omega)).1 h9
      have h10 := (le0_drop_iff (M := G ++ B ++ [lp]) (k := u.length)
        (a := u.length) (b := G.length) le_rfl (le_of_lt hslt)
        (by rw [hMlen]; omega)).1
      refine h10 ?_
      rw [Nat.sub_self, show G.length - u.length = gs by clear hnc; omega]
      exact h8
    -- the prefix bound from MF3
    have hC1 := hnx1.2.2.2.1
    rw [hewt] at hC1
    have hpre1 : entry S 1 0 = (G.getD u.length (0,0)).2 := by
      rw [hentS 1 0 (by clear hnc; omega), Nat.add_zero]
      unfold entry
      rw [if_neg one_ne_zero, copyExp_getD_pre hslt]
    have hpre := hMF3 hd0p u.length hslt hle0M (by rw [← hpre1]; exact hC1)
    have hpre0 : ∀ j, j < S.length → u.length + j < G.length →
        (S.getD j (0,0)).1 = (G.getD (u.length + j) (0,0)).1 := by
      intro j hj hjg
      rw [hgdS j hj, copyExp_getD_pre hjg]
    -- the climb column lies in copy kt-1
    have hr'lev : (S.getD r' (0,0)).1 + 1 = v0 + kt * d0 := by
      have h9 := hlev
      rw [hgt] at h9
      exact h9
    have hktd0 : d0 ≤ kt * d0 := by
      have h9 := Nat.mul_le_mul_right d0 hkt1
      rwa [Nat.one_mul] at h9
    have hr'ge : G.length ≤ u.length + r' := by
      by_contra hpre'
      push Not at hpre'
      have h8 := hpre (u.length + r') (by omega) hpre'
      rw [← hpre0 r' (by clear hnc; omega) hpre', hlp1] at h8
      clear hnc
      omega
    obtain ⟨kr, qr, hqrL, hdmr⟩ : ∃ kr qr, qr < B.length ∧
        u.length + r' - G.length = B.length * kr + qr :=
      ⟨_, _, Nat.mod_lt _ (by clear hnc; omega),
        (Nat.div_add_mod (u.length + r' - G.length) B.length).symm⟩
    have hcmr : B.length * kr = kr * B.length := Nat.mul_comm ..
    have hkrn : kr < n := by
      have h1 : B.length * kr < B.length * n := by
        have hcomm : n * B.length = B.length * n := Nat.mul_comm ..
        clear hnc
        omega
      exact Nat.lt_of_mul_lt_mul_left h1
    have hgr' : S.getD r' (0,0)
        = ((B.getD qr (0,0)).1 + kr * d0, (B.getD qr (0,0)).2) := by
      rw [hgdS _ (by clear hnc; omega),
          show u.length + r' = G.length + (kr * B.length + qr) by
            clear hnc; omega,
          copyExp_getD_copy hkrn hqrL]
    have hr'val : (B.getD qr (0,0)).1 + kr * d0 + 1 = v0 + kt * d0 := by
      have h9 := hr'lev
      rw [hgr'] at h9
      exact h9
    have hkrkt : kr + 1 = kt := by
      have hkrlt : kr < kt := by
        have h9 : B.length * kr < B.length * kt := by clear hnc; omega
        exact Nat.lt_of_mul_lt_mul_left h9
      by_contra hne
      obtain ⟨ir, hir⟩ : ∃ ir, u.length + ir
          = G.length + (kr + 1) * B.length :=
        ⟨G.length + (kr + 1) * B.length - u.length, by
          have hsucc : (kr + 1) * B.length = kr * B.length + B.length := by
            rw [Nat.add_mul, Nat.one_mul]
          clear hnc
          omega⟩
      have hsucc : (kr + 1) * B.length = kr * B.length + B.length := by
        rw [Nat.add_mul, Nat.one_mul]
      have hirgt : r' < ir := by clear hnc; omega
      have hirlt : ir < S.length - 1 := by
        have h9 : kr + 2 ≤ kt := by omega
        have h11 := Nat.mul_le_mul_right B.length h9
        rw [Nat.add_mul] at h11
        clear hnc
        omega
      have hroot' : (S.getD ir (0,0)).1 = v0 + (kr + 1) * d0 := by
        rw [hgdS _ (by clear hnc; omega),
            show u.length + ir = G.length + ((kr + 1) * B.length + 0) by
              clear hnc; omega,
            copyExp_getD_copy (by clear hnc; omega) (by clear hnc; omega),
            hBdef, List.getD_cons_zero]
      have h12 := hafter ir hirgt (by clear hnc; omega)
      rw [hgt, hroot'] at h12
      have h12' : v0 + kt * d0 ≤ v0 + (kr + 1) * d0 := h12
      have h13 : kr + 2 ≤ kt := by omega
      have h14 := Nat.mul_le_mul_right d0 h13
      rw [Nat.add_mul] at h14
      have h15 : (kr + 1) * d0 = kr * d0 + d0 := by
        rw [Nat.add_mul, Nat.one_mul]
      clear hnc
      omega
    have hktkr2 : kt * d0 = kr * d0 + d0 := by
      rw [← hkrkt, Nat.add_mul, Nat.one_mul]
    have hktB : kt * B.length = kr * B.length + B.length := by
      rw [← hkrkt, Nat.add_mul, Nat.one_mul]
    have hqrval : (B.getD qr (0,0)).1 + 1 = lp.1 := by
      rw [hlp1]
      clear hnc
      omega
    -- the within-block conclusion via the host parent edge
    have hT2conc : ∀ rr, 0 < rr → rr < qr →
        (B.getD rr (0,0)).1 + 1 < lp.1 := by
      rcases Nat.eq_zero_or_pos qr with hqr0 | hqrpos
      · intro rr h1 h2
        exfalso
        omega
      · have hdecT2 : G ++ B ++ [lp] = G ++ (B ++ [lp]) ++ ([] : PairSeq) := by
          simp [List.append_assoc]
        have hsclT2 : sclimb (B ++ [lp]) := hM G (B ++ [lp]) [] hdecT2
        have hT2len : (B ++ [lp]).length = B.length + 1 := by simp
        have hgB : ∀ j, j < B.length →
            (B ++ [lp]).getD j (0,0) = B.getD j (0,0) :=
          fun j hj => getD_append_left hj
        have hgLp : (B ++ [lp]).getD B.length (0,0) = lp := by
          rw [getD_append_right le_rfl, Nat.sub_self]
          rfl
        have heB1 : entry (B ++ [lp]) 1 B.length = lp.2 := by
          unfold entry
          rw [if_neg one_ne_zero, hgLp]
        have hdropM : (G ++ B ++ [lp]).drop G.length = B ++ [lp] := by
          rw [List.append_assoc, List.drop_left]
        have hnxT2 : nextrel1 (B ++ [lp]) 0 B.length := by
          have h10 : (G ++ B ++ [lp]).length - 1 = G.length + B.length := by
            rw [hMlen, Nat.add_sub_cancel]
          have h11 := hnxM
          rw [h10] at h11
          have h9 := (nextrel1_drop_iff (M := G ++ B ++ [lp])
            (k := G.length) (a := G.length) (b := G.length + B.length)
            le_rfl (by omega) (by rw [hMlen]; omega)).2 h11
          rw [hdropM, Nat.sub_self, Nat.add_sub_cancel_left] at h9
          exact h9
        have hi1T2 : idx1 (B ++ [lp]) ((B ++ [lp]).length - 1) = 1 := by
          rw [hT2len, Nat.add_sub_cancel]
          unfold idx1
          rw [if_pos (by rw [heB1]; omega)]
        have hnxRT2 : nextR (B ++ [lp])
            (idx1 (B ++ [lp]) ((B ++ [lp]).length - 1)) 0
            ((B ++ [lp]).length - 1) := by
          rw [hi1T2]
          unfold nextR
          rw [if_neg one_ne_zero, hT2len, Nat.add_sub_cancel]
          exact hnxT2
        have hT2after : ∀ l, qr < l → l + 1 < (B ++ [lp]).length →
            ((B ++ [lp]).getD ((B ++ [lp]).length - 1) (0,0)).1
              ≤ ((B ++ [lp]).getD l (0,0)).1 := by
          intro l hl1 hl2
          rw [hT2len] at hl2
          rw [hT2len, Nat.add_sub_cancel, hgLp, hgB l (by omega)]
          obtain ⟨il, hil⟩ : ∃ il, u.length + il
              = G.length + (kr * B.length + l) :=
            ⟨G.length + (kr * B.length + l) - u.length, by
              clear hnc; omega⟩
          have hil1 : r' < il := by clear hnc; omega
          have hil2 : il < S.length - 1 := by clear hnc; omega
          have h12 := hafter il hil1 (by clear hnc; omega)
          have hgil : S.getD il (0,0)
              = ((B.getD l (0,0)).1 + kr * d0, (B.getD l (0,0)).2) := by
            rw [hgdS _ (by clear hnc; omega),
                show u.length + il = G.length + (kr * B.length + l) from hil,
                copyExp_getD_copy (by clear hnc; omega) (by omega)]
          rw [hgt, hgil] at h12
          have h13 : v0 + kt * d0 ≤ (B.getD l (0,0)).1 + kr * d0 := h12
          rw [hlp1]
          clear hnc
          omega
        intro rr h1 h2
        have hconc2 := hsclT2 qr rr (by rw [hT2len]; omega) hnxRT2 hi1T2
          hqrpos (by rw [hT2len]; omega)
          (by
            rw [hT2len, Nat.add_sub_cancel, hgLp, hgB qr (by omega)]
            exact hqrval)
          hT2after h1 h2
        rw [hT2len, Nat.add_sub_cancel, hgLp, hgB rr (by omega)] at hconc2
        exact hconc2
    -- assemble the conclusion
    rw [hgt]
    show (S.getD r (0,0)).1 + 1 < v0 + kt * d0
    by_cases hrg : u.length + r < G.length
    · have h8 := hpre (u.length + r) (by omega) hrg
      rw [← hpre0 r (by clear hnc; omega) hrg, hlp1] at h8
      clear hnc
      omega
    · push Not at hrg
      obtain ⟨k2, q2, hq2L, hdm2⟩ : ∃ k2 q2, q2 < B.length ∧
          u.length + r - G.length = B.length * k2 + q2 :=
        ⟨_, _, Nat.mod_lt _ (by clear hnc; omega),
          (Nat.div_add_mod (u.length + r - G.length) B.length).symm⟩
      have hcm2 : B.length * k2 = k2 * B.length := Nat.mul_comm ..
      have hk2n : k2 < n := by
        have h1 : B.length * k2 < B.length * n := by
          have hcomm : n * B.length = B.length * n := Nat.mul_comm ..
          clear hnc
          omega
        exact Nat.lt_of_mul_lt_mul_left h1
      have hgr2 : S.getD r (0,0)
          = ((B.getD q2 (0,0)).1 + k2 * d0, (B.getD q2 (0,0)).2) := by
        rw [hgdS _ (by clear hnc; omega),
            show u.length + r = G.length + (k2 * B.length + q2) by
              clear hnc; omega,
            copyExp_getD_copy hk2n hq2L]
      have hval : (S.getD r (0,0)).1 = (B.getD q2 (0,0)).1 + k2 * d0 := by
        rw [hgr2]
      have hk2kr : k2 < kr ∨ (k2 = kr ∧ q2 < qr) := by
        by_cases h9 : k2 < kr
        · exact Or.inl h9
        · push Not at h9
          have hk2eq : k2 = kr := by
            by_contra h10
            have h11 : kr + 1 ≤ k2 := by omega
            have h12 := Nat.mul_le_mul_left B.length h11
            have h13 : B.length * (kr + 1) = B.length * kr + B.length := by
              rw [Nat.mul_add, Nat.mul_one]
            clear hnc
            omega
          refine Or.inr ⟨hk2eq, ?_⟩
          rw [hk2eq] at hdm2
          clear hnc
          omega
      rw [hval]
      rcases Nat.eq_zero_or_pos q2 with hq20 | hq2pos
      · have hval0 : (B.getD q2 (0,0)).1 = v0 := by
          rw [hq20, hBdef, List.getD_cons_zero]
        rw [hval0]
        rcases hk2kr with h9 | ⟨h9, h10⟩
        · have h11 : k2 + 2 ≤ kt := by omega
          have h12 := Nat.mul_le_mul_right d0 h11
          rw [Nat.add_mul] at h12
          clear hnc
          omega
        · have hd02 : 2 ≤ d0 := by
            have hqrpos : 0 < qr := by omega
            obtain ⟨qr', hqr'⟩ : ∃ qr', qr = qr' + 1 :=
              ⟨qr - 1, by omega⟩
            have hmem : R.getD qr' (0,0) ∈ R := by
              rw [getD_eq_getElem' _ _ (by clear hnc; omega)]
              exact List.getElem_mem ..
            have hv := hdom _ hmem
            have h13 : (B.getD qr (0,0)).1 = (R.getD qr' (0,0)).1 := by
              rw [hqr', hBdef, List.getD_cons_succ]
            have h14 := hqrval
            rw [hlp1, h13] at h14
            clear hnc
            omega
          rw [h9]
          clear hnc
          omega
      · rcases hk2kr with h9 | ⟨h9, h10⟩
        · have h11 := hBF45 hw0pos hd0p q2 hq2pos hq2L
          have h12 : k2 + 2 ≤ kt := by omega
          have h13 := Nat.mul_le_mul_right d0 h12
          rw [Nat.add_mul] at h13
          clear hnc
          omega
        · have h11 := hT2conc q2 hq2pos h10
          rw [hlp1] at h11
          rw [h9]
          clear hnc
          omega

/-- **The spanning block facts** (all mined exact): for the parent
decomposition of the host, (1) row-0 descendants of the block root with
positive row 1 sit strictly above the root's row 1; (2) in the triggered
branch the root's row 1 is minimal in its block; (3) prefix row-0 ancestors
of the parent with row 1 below the root see everything after them below
`lp.1 - 1`; (4) block interiors stay below `v0 + 2*d0`. -/
def spanOK (M : PairSeq) : Prop :=
  ∀ G v0 w0 R (lp : ℕ × ℕ) d0,
    M = G ++ ((v0, w0) :: R) ++ [lp] →
    nextR M (idx1 M (M.length - 1)) G.length (M.length - 1) →
    (d0 = 0 ∨ (0 < d0 ∧ w0 < lp.2 ∧ lp.1 = v0 + d0 ∧
      nextrel1 M G.length (M.length - 1))) →
    (∀ q, 0 < q → q < ((v0,w0) :: R).length →
      le0 ((v0,w0) :: R) 0 q → 0 < (((v0,w0) :: R).getD q (0,0)).2 →
      w0 < (((v0,w0) :: R).getD q (0,0)).2)
    ∧ (0 < d0 → ∀ q, q < ((v0,w0) :: R).length →
      w0 ≤ (((v0,w0) :: R).getD q (0,0)).2)
    ∧ (0 < d0 → ∀ a, a < G.length → le0 M a G.length →
      (G.getD a (0,0)).2 < w0 →
      ∀ h, a < h → h < G.length → (G.getD h (0,0)).1 + 1 < lp.1)
    ∧ (0 < w0 → 0 < d0 → ∀ q, 0 < q → q < ((v0,w0) :: R).length →
      (((v0,w0) :: R).getD q (0,0)).1 + 1 < v0 + 2 * d0)
    ∧ (0 < w0 → 0 < d0 → ∀ a q q', a < q → q < q' →
      q' < ((v0,w0) :: R).length →
      (((v0,w0) :: R).getD q (0,0)).1 + 1 + (((v0,w0) :: R).getD a (0,0)).1
        < 2 * (((v0,w0) :: R).getD q' (0,0)).1)
    ∧ (0 < d0 → lp.2 = w0 + 1)
    ∧ (0 < d0 → ∀ q, 0 < q → q < ((v0,w0) :: R).length →
      le0 ((v0,w0) :: R) 0 q → 0 < (((v0,w0) :: R).getD q (0,0)).2 →
      le0 (G ++ ((v0,w0) :: R) ++ [lp]) (G.length + q)
        ((G ++ ((v0,w0) :: R) ++ [lp]).length - 1)
      ∨ ((v0,w0) :: R).getD q (0,0) = lp)
    ∧ (0 < d0 → ∀ j, j < G.length → G.getD j (0,0) ≠ (v0, w0))
    ∧ (lp.2 = 0 → 0 < w0 → ∀ i, 0 < i → i < ((v0,w0) :: R).length →
      le0 ((v0,w0) :: R) 0 i → (((v0,w0) :: R).getD i (0,0)).2 = 0)
    ∧ (0 < d0 → ∀ i, le0 ((v0,w0) :: R) 0 i → i < ((v0,w0) :: R).length →
      ((v0,w0) :: R).getD i (0,0) = lp →
      ∀ m, i ≤ m → m < ((v0,w0) :: R).length →
        lp.1 ≤ (((v0,w0) :: R).getD m (0,0)).1)

/-- **`classOK` is preserved by the expansion step**, given the spanning
block facts of the host. -/
theorem classOK_oper {M : PairSeq} {n : ℕ} (hn : 1 ≤ n) (hM : classOK M)
    (hsp : spanOK M) : classOK (M⟦n⟧) := by
  by_cases hL0 : M.length - 1 = 0
  · rw [oper_eq_self_of_short n hL0]
    exact hM
  by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0
  · rw [oper_eq_pred_of_zero n hL0 hz]
    exact classOK_Pred hM
  by_cases hp : hasParent M (idx1 M (M.length - 1)) (M.length - 1)
  case neg =>
    rw [oper_eq_pred_of_noParent n hL0 hz hp]
    exact classOK_Pred hM
  case pos =>
    obtain ⟨G, v0, w0, R, d0, lp, hMeq, hX, hdom, _hlpgt, hd0, hnxt⟩ :=
      oper_bad_blocks (by omega) hz hp hn
    rw [hX]
    show classOK (copyExp G ((v0,w0) :: R) d0 n)
    have hd0' : d0 = 0 ∨ (0 < d0 ∧ w0 < lp.2 ∧ lp.1 = v0 + d0 ∧
        nextrel1 M G.length (M.length - 1)) := hd0.imp (·.1) id
    obtain ⟨hBF1, hBF2, hMF3, hBF45, -, -, -, -, -, -⟩ :=
      hsp G v0 w0 R lp d0 hMeq hnxt hd0'
    have hMc : classOK (G ++ ((v0,w0) :: R) ++ [lp]) := hMeq ▸ hM
    have hd0M : d0 = 0 ∨ (0 < d0 ∧ w0 < lp.2 ∧ lp.1 = v0 + d0 ∧
        nextrel1 (G ++ ((v0,w0) :: R) ++ [lp]) G.length
          ((G ++ ((v0,w0) :: R) ++ [lp]).length - 1)) := by
      rw [← hMeq]
      exact hd0'
    have hMF3' : 0 < d0 → ∀ a, a < G.length →
        le0 (G ++ ((v0,w0) :: R) ++ [lp]) a G.length →
        (G.getD a (0,0)).2 < w0 →
        ∀ h, a < h → h < G.length → (G.getD h (0,0)).1 + 1 < lp.1 := by
      rw [← hMeq]
      exact hMF3
    exact classOK_copyExp hn hMc
      (hspan_discharge hn hdom hMc hd0M hBF1 hBF2 hMF3' hBF45)

/-- **The master segment discipline along the standard closure**, modulo the
spanning block facts. -/
theorem classOK_ST_PS {M : PairSeq} (hM : ST_PS M)
    (hsp : ∀ N k, ST_PS N → 1 ≤ k → spanOK N) : classOK M := by
  induction hM with
  | diag v => exact classOK_diagSeq v
  | @oper N k hN hk ih => exact classOK_oper hk ih (hsp N k hN hk)

/-- **Block interiors below the row-0 parent of the last column stay below
its level** — the anchored single-climb instance of the host segment
`B ++ [lp]` rooted at the row-1 parent. -/
theorem block_interior_low {G R : PairSeq} {v0 w0 : ℕ} {lp : ℕ × ℕ}
    (hM : classOK (G ++ ((v0,w0) :: R) ++ [lp]))
    (hwlp : w0 < lp.2)
    (hnxM : nextrel1 (G ++ ((v0,w0) :: R) ++ [lp]) G.length
      ((G ++ ((v0,w0) :: R) ++ [lp]).length - 1))
    {qr : ℕ} (hqr0 : 0 < qr) (hqrL : qr < ((v0,w0) :: R).length)
    (hlev : (((v0,w0) :: R).getD qr (0,0)).1 + 1 = lp.1)
    (hafter : ∀ l, qr < l → l < ((v0,w0) :: R).length →
      lp.1 ≤ (((v0,w0) :: R).getD l (0,0)).1) :
    ∀ rr, 0 < rr → rr < qr →
      (((v0,w0) :: R).getD rr (0,0)).1 + 1 < lp.1 := by
  set B : PairSeq := (v0,w0) :: R with hBdef
  have hMlen : (G ++ B ++ [lp]).length = G.length + B.length + 1 :=
    hostM_length ..
  have hdecT2 : G ++ B ++ [lp] = G ++ (B ++ [lp]) ++ ([] : PairSeq) := by
    simp [List.append_assoc]
  have hsclT2 : sclimb (B ++ [lp]) := hM G (B ++ [lp]) [] hdecT2
  have hT2len : (B ++ [lp]).length = B.length + 1 := by simp
  have hgB : ∀ j, j < B.length →
      (B ++ [lp]).getD j (0,0) = B.getD j (0,0) :=
    fun j hj => getD_append_left hj
  have hgLp : (B ++ [lp]).getD B.length (0,0) = lp := by
    rw [getD_append_right le_rfl, Nat.sub_self]
    rfl
  have heB1 : entry (B ++ [lp]) 1 B.length = lp.2 := by
    unfold entry
    rw [if_neg one_ne_zero, hgLp]
  have hdropM : (G ++ B ++ [lp]).drop G.length = B ++ [lp] := by
    rw [List.append_assoc, List.drop_left]
  have hnxT2 : nextrel1 (B ++ [lp]) 0 B.length := by
    have h10 : (G ++ B ++ [lp]).length - 1 = G.length + B.length := by
      rw [hMlen, Nat.add_sub_cancel]
    have h11 := hnxM
    rw [h10] at h11
    have h9 := (nextrel1_drop_iff (M := G ++ B ++ [lp])
      (k := G.length) (a := G.length) (b := G.length + B.length)
      le_rfl (by omega) (by rw [hMlen]; omega)).2 h11
    rw [hdropM, Nat.sub_self, Nat.add_sub_cancel_left] at h9
    exact h9
  have hi1T2 : idx1 (B ++ [lp]) ((B ++ [lp]).length - 1) = 1 := by
    rw [hT2len, Nat.add_sub_cancel]
    unfold idx1
    rw [if_pos (by rw [heB1]; omega)]
  have hnxRT2 : nextR (B ++ [lp])
      (idx1 (B ++ [lp]) ((B ++ [lp]).length - 1)) 0
      ((B ++ [lp]).length - 1) := by
    rw [hi1T2]
    unfold nextR
    rw [if_neg one_ne_zero, hT2len, Nat.add_sub_cancel]
    exact hnxT2
  intro rr h1 h2
  have hconc2 := hsclT2 qr rr (by rw [hT2len]; omega) hnxRT2 hi1T2 hqr0
    (by rw [hT2len]; omega)
    (by
      rw [hT2len, Nat.add_sub_cancel, hgLp, hgB qr (by omega)]
      exact hlev)
    (by
      intro l hl1 hl2
      rw [hT2len] at hl2
      rw [hT2len, Nat.add_sub_cancel, hgLp, hgB l (by omega)]
      exact hafter l hl1 (by omega))
    h1 h2
  rw [hT2len, Nat.add_sub_cancel, hgLp, hgB rr (by omega)] at hconc2
  exact hconc2

/-- **The within-trigger obligation discharges** from `r1ok`, `classOK` and
the spanning block facts: the row-0-parent dichotomy at the last column
either yields the host trigger directly at the last block column, or forces
the −1 configuration, where the parent-edge maximality makes the expansion
row-1-triggered and the block single-climb refutes its witness. -/
theorem withinTrigOK_of {M : PairSeq} {n : ℕ} (hn : 1 ≤ n)
    (hr1 : r1ok M) (hcl : classOK M) (hsp : spanOK M) :
    withinTrigOK M n := by
  intro G v0 w0 R lp d0 hMeq hX hd0p hwlp hlp1 hnx1M hnxtM j0X hge hj0 hnx
    htrigX hi1
  have hL1 : 1 ≤ ((v0,w0) :: R).length := by simp
  have hMlen : M.length = G.length + ((v0,w0) :: R).length + 1 := by
    rw [hMeq]
    exact hostM_length ..
  have hXlen : (M⟦n⟧).length = G.length + n * ((v0,w0) :: R).length := by
    rw [hX]
    exact copyExp_length ..
  have hnL : n * ((v0,w0) :: R).length
      = (n - 1) * ((v0,w0) :: R).length + ((v0,w0) :: R).length := by
    have h9 : n - 1 + 1 = n := by omega
    calc n * ((v0,w0) :: R).length
        = (n - 1 + 1) * ((v0,w0) :: R).length := by rw [h9]
    _ = (n - 1) * ((v0,w0) :: R).length + 1 * ((v0,w0) :: R).length := by
        rw [Nat.add_mul]
    _ = (n - 1) * ((v0,w0) :: R).length + ((v0,w0) :: R).length := by
        rw [Nat.one_mul]
  obtain ⟨-, hBF2, -, -, -, -, -, -, -, -⟩ := hsp G v0 w0 R lp d0 hMeq hnxtM
    (Or.inr ⟨hd0p, hwlp, hlp1, hnx1M⟩)
  have hBF2' := hBF2 hd0p
  have hgblk : ∀ q, q < ((v0,w0) :: R).length →
      M.getD (G.length + q) (0,0) = ((v0,w0) :: R).getD q (0,0) := by
    intro q hq
    rw [hMeq]
    exact hostM_getD_blk hq
  have hglp : M.getD (M.length - 1) (0,0) = lp := by
    rw [show M.length - 1 = G.length + ((v0,w0) :: R).length by omega, hMeq]
    exact hostM_getD_lp
  have hlp1pos : 0 < (M.getD (M.length - 1) (0,0)).1 := by
    rw [hglp]
    omega
  obtain ⟨k, hklt, hklev, hkval, hkr1⟩ := hr1 (M.length - 1) (by omega) hlp1pos
  by_cases hcase : lp.1
      ≤ (((v0,w0) :: R).getD (((v0,w0) :: R).length - 1) (0,0)).1
  · -- direct host trigger at the last block column
    have hL2 : 2 ≤ ((v0,w0) :: R).length := by
      by_contra hL1'
      push Not at hL1'
      have hLe : ((v0,w0) :: R).length = 1 := by omega
      rw [hLe, show (1:ℕ) - 1 = 0 from rfl, List.getD_cons_zero] at hcase
      have h9 : lp.1 ≤ v0 := hcase
      omega
    refine ⟨G.length + (((v0,w0) :: R).length - 1), by omega, by omega,
      ?_, ?_⟩
    · rw [hglp, hgblk _ (by omega)]
      exact hcase
    · have h9 := hBF2' (((v0,w0) :: R).length - 1) (by omega)
      have hgroot : M.getD G.length (0,0) = (v0, w0) := by
        have h10 := hgblk 0 (by omega)
        rw [Nat.add_zero] at h10
        rw [h10, List.getD_cons_zero]
      rw [hgroot, hgblk _ (by omega)]
      exact h9
  · -- the −1 configuration: refute the instance
    push Not at hcase
    have hkeq : k = G.length + (((v0,w0) :: R).length - 1) := by
      by_contra hne
      have h9 : k < G.length + (((v0,w0) :: R).length - 1) ∨
          G.length + (((v0,w0) :: R).length - 1) < k := by omega
      rcases h9 with h9 | h9
      · have h10 := hkval (G.length + (((v0,w0) :: R).length - 1)) h9
          (by omega)
        rw [hglp, hgblk _ (by omega)] at h10
        omega
      · omega
    have htail : (((v0,w0) :: R).getD (((v0,w0) :: R).length - 1) (0,0)).1
        + 1 = lp.1 := by
      have h9 := hklev
      rw [hkeq, hgblk _ (by omega), hglp] at h9
      exact h9
    have hadj : nextrel0 M (G.length + (((v0,w0) :: R).length - 1))
        (M.length - 1) := by
      refine ⟨by omega, by omega, by omega, ?_, ?_⟩
      · unfold entry
        rw [if_pos rfl, if_pos rfl, hgblk _ (by omega), hglp]
        omega
      · intro l hl
        exfalso
        omega
    have hle0adj : le0 M (G.length + (((v0,w0) :: R).length - 1))
        (M.length - 1) :=
      ⟨by omega, by omega, Relation.ReflTransGen.single hadj⟩
    have hmax := hnx1M.2.2.2.2.2 (G.length + (((v0,w0) :: R).length - 1))
      ⟨by omega, hle0adj⟩
    have htail2 : 0
        < (((v0,w0) :: R).getD (((v0,w0) :: R).length - 1) (0,0)).2 := by
      unfold entry at hmax
      rw [if_neg one_ne_zero, if_neg one_ne_zero, hgblk _ (by omega),
          hglp] at hmax
      omega
    have hXlast : (M⟦n⟧).getD ((M⟦n⟧).length - 1) (0,0)
        = ((((v0,w0) :: R).getD (((v0,w0) :: R).length - 1) (0,0)).1
            + (n - 1) * d0,
           (((v0,w0) :: R).getD (((v0,w0) :: R).length - 1) (0,0)).2) := by
      rw [hX]
      rw [show (copyExp G ((v0,w0) :: R) d0 n).length - 1
            = G.length + ((n - 1) * ((v0,w0) :: R).length
              + (((v0,w0) :: R).length - 1)) by
          rw [copyExp_length]
          omega]
      exact copyExp_getD_copy (by omega) (by omega)
    have hiX : idx1 (M⟦n⟧) ((M⟦n⟧).length - 1) = 1 := by
      unfold idx1
      rw [if_pos (by
        unfold entry
        rw [if_neg one_ne_zero, hXlast]
        exact htail2)]
    obtain ⟨bX, hbX1, hbX2, hbXe0, hbXe1⟩ := htrigX hiX
    obtain ⟨rb, hrb⟩ : ∃ rb,
        bX = G.length + ((n - 1) * ((v0,w0) :: R).length + rb) :=
      ⟨bX - (G.length + (n - 1) * ((v0,w0) :: R).length), by omega⟩
    have hrb1 : 0 < rb := by omega
    have hrbL : rb < ((v0,w0) :: R).length - 1 := by
      rw [hXlen] at hbX2
      omega
    have hbXval : (M⟦n⟧).getD bX (0,0)
        = ((((v0,w0) :: R).getD rb (0,0)).1 + (n - 1) * d0,
           (((v0,w0) :: R).getD rb (0,0)).2) := by
      rw [hX, hrb]
      exact copyExp_getD_copy (by omega) (by omega)
    have hge0 : (((v0,w0) :: R).getD (((v0,w0) :: R).length - 1) (0,0)).1
        ≤ (((v0,w0) :: R).getD rb (0,0)).1 := by
      rw [hXlast, hbXval] at hbXe0
      have h9 : (((v0,w0) :: R).getD (((v0,w0) :: R).length - 1) (0,0)).1
            + (n - 1) * d0
          ≤ (((v0,w0) :: R).getD rb (0,0)).1 + (n - 1) * d0 := hbXe0
      omega
    exfalso
    have hlow := block_interior_low (hMeq ▸ hcl) hwlp
      (by rw [← hMeq]; exact hnx1M)
      (show 0 < ((v0,w0) :: R).length - 1 by omega) (by omega) htail
      (by
        intro l hl1 hl2
        exfalso
        omega)
      rb hrb1 hrbL
    omega


/-- **No row-0 seam edge over a long block**: a `nextrel0` edge into the
expansion's last column from before the last copy forces the block to be a
single root — the between-condition at the last copy's root would put the
root at or above the block tail, contradicting its strict minimality. -/
theorem seam_edge0_short {G R : PairSeq} {v0 w0 d0 n j0X : ℕ}
    (hn : 1 ≤ n) (hdom : ∀ p ∈ R, v0 < p.1)
    (hj0 : j0X < G.length + (n - 1) * ((v0,w0) :: R).length)
    (hedge : nextrel0 (copyExp G ((v0,w0) :: R) d0 n) j0X
      ((copyExp G ((v0,w0) :: R) d0 n).length - 1)) :
    ((v0,w0) :: R).length = 1 := by
  by_contra hL
  have hL1 : 1 ≤ ((v0,w0) :: R).length := by simp
  have hL2 : 2 ≤ ((v0,w0) :: R).length := by omega
  have hXlen : (copyExp G ((v0,w0) :: R) d0 n).length
      = G.length + n * ((v0,w0) :: R).length := copyExp_length ..
  have hnL : n * ((v0,w0) :: R).length
      = (n - 1) * ((v0,w0) :: R).length + ((v0,w0) :: R).length := by
    have h9 : n - 1 + 1 = n := by omega
    calc n * ((v0,w0) :: R).length
        = (n - 1 + 1) * ((v0,w0) :: R).length := by rw [h9]
    _ = (n - 1) * ((v0,w0) :: R).length + 1 * ((v0,w0) :: R).length := by
        rw [Nat.add_mul]
    _ = (n - 1) * ((v0,w0) :: R).length + ((v0,w0) :: R).length := by
        rw [Nat.one_mul]
  -- the last copy's root lies strictly between
  have hroot : entry (copyExp G ((v0,w0) :: R) d0 n) 0
      (G.length + ((n - 1) * ((v0,w0) :: R).length + 0))
      = v0 + (n - 1) * d0 := by
    rw [(entry_copyExp (by omega) (by omega)).1, List.getD_cons_zero]
  have htail : entry (copyExp G ((v0,w0) :: R) d0 n) 0
      ((copyExp G ((v0,w0) :: R) d0 n).length - 1)
      = (((v0,w0) :: R).getD (((v0,w0) :: R).length - 1) (0,0)).1
        + (n - 1) * d0 := by
    rw [show (copyExp G ((v0,w0) :: R) d0 n).length - 1
          = G.length + ((n - 1) * ((v0,w0) :: R).length
            + (((v0,w0) :: R).length - 1)) by rw [hXlen]; omega]
    exact (entry_copyExp (by omega) (by omega)).1
  have hbet := hedge.2.2.2.2
    (G.length + ((n - 1) * ((v0,w0) :: R).length + 0))
    ⟨by omega, by rw [hXlen]; omega⟩
  rw [hroot, htail] at hbet
  -- v0 ≥ tail value, contradicting strict root minimality
  obtain ⟨q', hq'⟩ : ∃ q', ((v0,w0) :: R).length - 1 = q' + 1 :=
    ⟨((v0,w0) :: R).length - 2, by omega⟩
  rw [hq', List.getD_cons_succ] at hbet
  have hmem : R.getD q' (0,0) ∈ R := by
    rw [getD_eq_getElem' _ _ (by
      have h9 : ((v0,w0) :: R).length = R.length + 1 := by simp
      omega)]
    exact List.getElem_mem ..
  have hv := hdom _ hmem
  omega

/-- **No row-1 seam edge over a long block**: a `nextrel1` edge into the
expansion's last column from before the last copy forces the block to be a
single root — the chain passes through the last copy's root, whose
maximality clause contradicts the strict row-1 ascent of the block (BF1). -/
theorem seam_edge1_short {G R : PairSeq} {v0 w0 d0 n j0X : ℕ}
    (hn : 1 ≤ n) (hdom : ∀ p ∈ R, v0 < p.1)
    (hBF1 : ∀ q, 0 < q → q < ((v0,w0) :: R).length →
      le0 ((v0,w0) :: R) 0 q → 0 < (((v0,w0) :: R).getD q (0,0)).2 →
      w0 < (((v0,w0) :: R).getD q (0,0)).2)
    (hj0 : j0X < G.length + (n - 1) * ((v0,w0) :: R).length)
    (hedge : nextrel1 (copyExp G ((v0,w0) :: R) d0 n) j0X
      ((copyExp G ((v0,w0) :: R) d0 n).length - 1))
    (hpos : 0 < entry (copyExp G ((v0,w0) :: R) d0 n) 1
      ((copyExp G ((v0,w0) :: R) d0 n).length - 1)) :
    ((v0,w0) :: R).length = 1 := by
  by_contra hL
  have hL1 : 1 ≤ ((v0,w0) :: R).length := by simp
  have hL2 : 2 ≤ ((v0,w0) :: R).length := by omega
  have hXlen : (copyExp G ((v0,w0) :: R) d0 n).length
      = G.length + n * ((v0,w0) :: R).length := copyExp_length ..
  have hnL : n * ((v0,w0) :: R).length
      = (n - 1) * ((v0,w0) :: R).length + ((v0,w0) :: R).length := by
    have h9 : n - 1 + 1 = n := by omega
    calc n * ((v0,w0) :: R).length
        = (n - 1 + 1) * ((v0,w0) :: R).length := by rw [h9]
    _ = (n - 1) * ((v0,w0) :: R).length + 1 * ((v0,w0) :: R).length := by
        rw [Nat.add_mul]
    _ = (n - 1) * ((v0,w0) :: R).length + ((v0,w0) :: R).length := by
        rw [Nat.one_mul]
  -- the last copy's root and tail entries
  have hroot0 : entry (copyExp G ((v0,w0) :: R) d0 n) 0
      (G.length + ((n - 1) * ((v0,w0) :: R).length + 0))
      = v0 + (n - 1) * d0 := by
    rw [(entry_copyExp (by omega) (by omega)).1, List.getD_cons_zero]
  have hroot1 : entry (copyExp G ((v0,w0) :: R) d0 n) 1
      (G.length + ((n - 1) * ((v0,w0) :: R).length + 0)) = w0 := by
    rw [(entry_copyExp (by omega) (by omega)).2, List.getD_cons_zero]
  have hlastidx : (copyExp G ((v0,w0) :: R) d0 n).length - 1
      = G.length + ((n - 1) * ((v0,w0) :: R).length
        + (((v0,w0) :: R).length - 1)) := by
    rw [hXlen]
    omega
  have htail1 : entry (copyExp G ((v0,w0) :: R) d0 n) 1
      ((copyExp G ((v0,w0) :: R) d0 n).length - 1)
      = (((v0,w0) :: R).getD (((v0,w0) :: R).length - 1) (0,0)).2 := by
    rw [hlastidx]
    exact (entry_copyExp (by omega) (by omega)).2
  -- the chain into the last column passes through the last copy's root
  have hle0X : le0 (copyExp G ((v0,w0) :: R) d0 n) j0X
      ((copyExp G ((v0,w0) :: R) d0 n).length - 1) := hedge.2.2.2.2.1
  have hpiv : ∀ y, G.length + ((n - 1) * ((v0,w0) :: R).length + 0) < y →
      y ≤ (copyExp G ((v0,w0) :: R) d0 n).length - 1 →
      entry (copyExp G ((v0,w0) :: R) d0 n) 0
        (G.length + ((n - 1) * ((v0,w0) :: R).length + 0))
        < entry (copyExp G ((v0,w0) :: R) d0 n) 0 y := by
    intro y hy1 hy2
    obtain ⟨qy, hqy⟩ : ∃ qy,
        y = G.length + ((n - 1) * ((v0,w0) :: R).length + qy) :=
      ⟨y - (G.length + (n - 1) * ((v0,w0) :: R).length), by omega⟩
    have hqy1 : 1 ≤ qy := by omega
    have hqyL : qy < ((v0,w0) :: R).length := by
      rw [hXlen] at hy2
      omega
    have hey : entry (copyExp G ((v0,w0) :: R) d0 n) 0 y
        = (((v0,w0) :: R).getD qy (0,0)).1 + (n - 1) * d0 := by
      rw [hqy]
      exact (entry_copyExp (by omega) (by omega)).1
    rw [hroot0, hey]
    obtain ⟨qy', rfl⟩ : ∃ qy', qy = qy' + 1 := ⟨qy - 1, by omega⟩
    rw [List.getD_cons_succ]
    have hmem : R.getD qy' (0,0) ∈ R := by
      rw [getD_eq_getElem' _ _ (by
        have h9 : ((v0,w0) :: R).length = R.length + 1 := by simp
        omega)]
      exact List.getElem_mem ..
    have hv := hdom _ hmem
    omega
  have hle0ρ := le0_through_pivot hle0X (by omega)
    (by rw [hXlen]; omega) hpiv
  -- maximality at the root
  have hmax := hedge.2.2.2.2.2
    (G.length + ((n - 1) * ((v0,w0) :: R).length + 0))
    ⟨by omega, hle0ρ⟩
  rw [htail1] at hmax
  unfold entry at hmax
  rw [if_neg one_ne_zero] at hmax
  have hmax' : (((v0,w0) :: R).getD (((v0,w0) :: R).length - 1) (0,0)).2
      ≤ w0 := by
    have h9 := hroot1
    unfold entry at h9
    rw [if_neg one_ne_zero] at h9
    rw [h9] at hmax
    exact hmax
  -- the last copy is exactly the shifted block
  have hwin : (copyExp G ((v0,w0) :: R) d0 n).drop
      (G.length + (n - 1) * ((v0,w0) :: R).length)
      = ((v0,w0) :: R).map fun p => (p.1 + (n - 1) * d0, p.2) := by
    have hsplit := copyExp_split G ((v0,w0) :: R) d0
      (show n - 1 ≤ n by omega)
    rw [show n - (n - 1) = 1 by omega] at hsplit
    rw [show (1:ℕ) = 0 + 1 from rfl, List.range_succ_eq_map,
        List.range_zero, List.map_nil, List.flatMap_cons,
        List.flatMap_nil, List.append_nil] at hsplit
    simp only [Nat.add_zero] at hsplit
    rw [hsplit, show G.length + (n - 1) * ((v0,w0) :: R).length
          = (copyExp G ((v0,w0) :: R) d0 (n - 1)).length from
        (copyExp_length ..).symm,
      List.drop_left]
  -- transfer the chain to the unshifted block
  have hd1 : le0 ((copyExp G ((v0,w0) :: R) d0 n).drop
      (G.length + (n - 1) * ((v0,w0) :: R).length))
      ((G.length + ((n - 1) * ((v0,w0) :: R).length + 0))
        - (G.length + (n - 1) * ((v0,w0) :: R).length))
      (((copyExp G ((v0,w0) :: R) d0 n).length - 1)
        - (G.length + (n - 1) * ((v0,w0) :: R).length)) :=
    (le0_drop_iff (by omega) (by rw [hXlen]; omega)
      (by rw [hXlen]; omega)).2 hle0ρ
  rw [hwin, show (G.length + ((n - 1) * ((v0,w0) :: R).length + 0))
        - (G.length + (n - 1) * ((v0,w0) :: R).length) = 0 by omega,
      show ((copyExp G ((v0,w0) :: R) d0 n).length - 1)
        - (G.length + (n - 1) * ((v0,w0) :: R).length)
        = ((v0,w0) :: R).length - 1 by rw [hXlen]; omega] at hd1
  have hd2 : le0 ((v0,w0) :: R) 0 (((v0,w0) :: R).length - 1) :=
    (le0_shift_iff).1 hd1
  -- BF1 against the maximality
  have hbf := hBF1 (((v0,w0) :: R).length - 1) (by omega) (by omega) hd2
    (by rw [← htail1]; exact hpos)
  omega

theorem hhm_nil : hhm ([] : PairSeq) := by
  refine ⟨Or.inl rfl, ?_⟩
  intro p hp
  simp at hp

/-- The narrowed seam obligation: single-root blocks, prefix parents. -/
def seamOK1 (M : PairSeq) (n : ℕ) : Prop :=
  ∀ (G : PairSeq) (v0 w0 d0 : ℕ) (lp : ℕ × ℕ),
    M = G ++ [(v0,w0)] ++ [lp] →
    M⟦n⟧ = copyExp G [(v0,w0)] d0 n →
    nextR M (idx1 M (M.length - 1)) G.length (M.length - 1) →
    ∀ j0X, j0X < G.length →
      j0X + 1 < (M⟦n⟧).length →
      nextR (M⟦n⟧) (idx1 (M⟦n⟧) ((M⟦n⟧).length - 1)) j0X
        ((M⟦n⟧).length - 1) →
      (idx1 (M⟦n⟧) ((M⟦n⟧).length - 1) = 1 →
        ∃ b, j0X < b ∧ b + 1 < (M⟦n⟧).length ∧
          ((M⟦n⟧).getD ((M⟦n⟧).length - 1) (0,0)).1
            ≤ ((M⟦n⟧).getD b (0,0)).1 ∧
          ((M⟦n⟧).getD j0X (0,0)).2 ≤ ((M⟦n⟧).getD b (0,0)).2) →
      hhm (((M⟦n⟧).take ((M⟦n⟧).length - 1)).drop (j0X + 1))

/-- **The seam obligation reduces to single-root blocks with prefix
parents**: the edge-shortness lemmas force the block to one root; root
parents are refuted (row 1) or yield an empty region (row 0). -/
theorem seamOK_of {M : PairSeq} {n : ℕ} (hn : 1 ≤ n)
    (hBF1all : ∀ (G : PairSeq) (v0 w0 : ℕ) (R : PairSeq) (lp : ℕ × ℕ)
      (d0 : ℕ),
      M = G ++ ((v0,w0) :: R) ++ [lp] →
      nextR M (idx1 M (M.length - 1)) G.length (M.length - 1) →
      (d0 = 0 ∨ (0 < d0 ∧ w0 < lp.2 ∧ lp.1 = v0 + d0 ∧
        nextrel1 M G.length (M.length - 1))) →
      ∀ q, 0 < q → q < ((v0,w0) :: R).length →
        le0 ((v0,w0) :: R) 0 q → 0 < (((v0,w0) :: R).getD q (0,0)).2 →
        w0 < (((v0,w0) :: R).getD q (0,0)).2)
    (h1 : seamOK1 M n) : seamOK M n := by
  intro G v0 w0 R lp d0 hMeq hX hdom hnxtM hd0 j0X hj0lt hj0 hnx htrigX
  have hL : ((v0,w0) :: R).length = 1 := by
    unfold nextR at hnx
    by_cases hiX : idx1 (M⟦n⟧) ((M⟦n⟧).length - 1) = 0
    · rw [if_pos hiX] at hnx
      have hnx' := hnx
      rw [hX] at hnx'
      exact seam_edge0_short hn hdom hj0lt hnx'
    · rw [if_neg hiX] at hnx
      have hnx' := hnx
      rw [hX] at hnx'
      refine seam_edge1_short hn hdom
        (hBF1all G v0 w0 R lp d0 hMeq hnxtM hd0) hj0lt hnx' ?_
      rw [← hX]
      by_contra hpos0
      exact hiX (by unfold idx1; rw [if_neg hpos0])
  obtain rfl : R = [] := List.eq_nil_of_length_eq_zero (by simpa using hL)
  by_cases hg : j0X < G.length
  · exact h1 G v0 w0 d0 lp hMeq hX hnxtM j0X hg hj0 hnx htrigX
  · push Not at hg
    have hXlen : (M⟦n⟧).length = G.length + n * 1 := by
      rw [hX]
      exact copyExp_length ..
    have hent : ∀ k, k < n → (M⟦n⟧).getD (G.length + k) (0,0)
        = (v0 + k * d0, w0) := by
      intro k hk
      have hone : ([(v0,w0)] : PairSeq).length = 1 := rfl
      rw [hX, show G.length + k
            = G.length + (k * ([(v0,w0)] : PairSeq).length + 0) by
          rw [hone]; omega,
          copyExp_getD_copy hk (by rw [hone]; omega), List.getD_cons_zero]
    have hn2 : 2 ≤ n := by omega
    unfold nextR at hnx
    by_cases hiX : idx1 (M⟦n⟧) ((M⟦n⟧).length - 1) = 0
    · rw [if_pos hiX] at hnx
      have hj0eq : j0X = (M⟦n⟧).length - 2 := by
        by_contra hne
        have hlt : j0X < (M⟦n⟧).length - 2 := by omega
        have hbet := hnx.2.2.2.2 ((M⟦n⟧).length - 2) ⟨by omega, by omega⟩
        have h1e : entry (M⟦n⟧) 0 ((M⟦n⟧).length - 2)
            = v0 + (n - 2) * d0 := by
          unfold entry
          rw [if_pos rfl,
              show (M⟦n⟧).length - 2 = G.length + (n - 2) by omega,
              hent (n - 2) (by omega)]
        have h2e : entry (M⟦n⟧) 0 ((M⟦n⟧).length - 1)
            = v0 + (n - 1) * d0 := by
          unfold entry
          rw [if_pos rfl,
              show (M⟦n⟧).length - 1 = G.length + (n - 1) by omega,
              hent (n - 1) (by omega)]
        obtain ⟨k0, hk0⟩ : ∃ k0, j0X = G.length + k0 :=
          ⟨j0X - G.length, by omega⟩
        have h3e : entry (M⟦n⟧) 0 j0X = v0 + k0 * d0 := by
          unfold entry
          rw [if_pos rfl, hk0, hent k0 (by omega)]
        have hinc := hnx.2.2.2.1
        rw [h3e, h2e] at hinc
        rw [h1e, h2e] at hbet
        have hb1 : (n - 2) * d0 + d0 = (n - 1) * d0 := by
          have h9 : n - 2 + 1 = n - 1 := by omega
          calc (n - 2) * d0 + d0 = (n - 2 + 1) * d0 := by
                rw [Nat.add_mul, Nat.one_mul]
          _ = (n - 1) * d0 := by rw [h9]
        have hd00 : d0 = 0 := by omega
        rw [hd00, Nat.mul_zero, Nat.mul_zero] at hinc
        omega
      have hreg : (((M⟦n⟧).take ((M⟦n⟧).length - 1)).drop (j0X + 1))
          = [] := by
        apply List.drop_eq_nil_of_le
        rw [List.length_take]
        omega
      rw [hreg]
      exact hhm_nil
    · rw [if_neg hiX] at hnx
      exfalso
      have hinc := hnx.2.2.2.1
      obtain ⟨k0, hk0⟩ : ∃ k0, j0X = G.length + k0 :=
        ⟨j0X - G.length, by omega⟩
      have h1e : entry (M⟦n⟧) 1 j0X = w0 := by
        unfold entry
        rw [if_neg one_ne_zero, hk0, hent k0 (by omega)]
      have h2e : entry (M⟦n⟧) 1 ((M⟦n⟧).length - 1) = w0 := by
        unfold entry
        rw [if_neg one_ne_zero,
            show (M⟦n⟧).length - 1 = G.length + (n - 1) by omega,
            hent _ (by omega)]
      rw [h1e, h2e] at hinc
      omega

/-- **The invariant package on standard hosts**, now modulo only the seam
and spanning obligations: the within-trigger obligation is discharged. -/
theorem I_ST_PS {M : PairSeq} (hM : ST_PS M)
    (hseam1 : ∀ N k, ST_PS N → 1 ≤ k → seamOK1 N k)
    (hsp : ∀ N k, ST_PS N → 1 ≤ k → spanOK N) :
    hmok M ∧ tailok M ∧ classOK M := by
  have hcl : ∀ N, ST_PS N → classOK N := fun N hN => classOK_ST_PS hN hsp
  obtain ⟨h1, h2⟩ := hmok_tailok_ST_PS hM
    (fun N k hN hk => seamOK_of hk
      (fun G v0 w0 R lp d0 hMeq hnxtM hd0 =>
        (hsp N k hN hk G v0 w0 R lp d0 hMeq hnxtM hd0).1)
      (hseam1 N k hN hk))
    (fun N k hN hk => withinTrigOK_of hk (r1ok_ST_PS hN) (hcl N hN)
      (hsp N k hN hk))
  exact ⟨h1, h2, hcl M hM⟩

theorem rtg_diag_adj (v : ℕ) : ∀ b, b ≤ v → ∀ a, a ≤ b →
    Relation.ReflTransGen (nextrel0 (diagSeq 0 v)) a b := by
  intro b
  induction b with
  | zero =>
    intro _ a ha
    have : a = 0 := by omega
    rw [this]
  | succ b ih =>
    intro hbv a ha
    rcases Nat.eq_or_lt_of_le ha with he | hlt
    · rw [he]
    · refine (ih (by omega) a (by omega)).tail ?_
      refine ⟨by rw [diagSeq0_length]; omega, by rw [diagSeq0_length]; omega,
        by omega, ?_, ?_⟩
      · unfold entry
        rw [if_pos rfl, if_pos rfl, diagSeq0_getD (by omega),
            diagSeq0_getD (by omega)]
        omega
      · intro l hl
        exfalso
        omega

theorem le0_diagSeq {v a b : ℕ} (hab : a ≤ b) (hb : b ≤ v) :
    le0 (diagSeq 0 v) a b :=
  ⟨by rw [diagSeq0_length]; omega, by rw [diagSeq0_length]; omega,
    rtg_diag_adj v b hb a hab⟩

/-- On the diagonal the only parent edge into the last column is the
second-to-last column, where all spanning block facts trivialize. -/
theorem spanOK_diagSeq (v : ℕ) : spanOK (diagSeq 0 v) := by
  intro G v0 w0 R lp d0 hMeq hnxtM hd0
  have hlen := congrArg List.length hMeq
  rw [diagSeq0_length] at hlen
  simp at hlen
  have hG : G.length + (R.length + 1) = v := by omega
  have hgd : ∀ i, i < v + 1 → (diagSeq 0 v).getD i (0,0) = (i, i) :=
    fun i hi => diagSeq0_getD hi
  -- the maximality or between condition forces a one-root block
  have hR : R = [] := by
    by_contra hRne
    have hR1 : 1 ≤ R.length := by
      rcases R with _ | ⟨r, R'⟩
      · exact absurd rfl hRne
      · simp
    unfold nextR at hnxtM
    by_cases hi1 : idx1 (diagSeq 0 v) ((diagSeq 0 v).length - 1) = 0
    · rw [if_pos hi1] at hnxtM
      have hb := hnxtM.2.2.2.2 (G.length + 1)
        ⟨by omega, by rw [diagSeq0_length]; omega⟩
      unfold entry at hb
      rw [if_pos rfl, if_pos rfl, diagSeq0_length,
          show v + 1 - 1 = v by omega, hgd v (by omega),
          hgd (G.length + 1) (by omega)] at hb
      have hb' : v ≤ G.length + 1 := hb
      omega
    · rw [if_neg hi1] at hnxtM
      have hb := hnxtM.2.2.2.2.2 (G.length + 1) ⟨by omega, by
        rw [diagSeq0_length, show v + 1 - 1 = v by omega]
        exact le0_diagSeq (by omega) (by omega)⟩
      unfold entry at hb
      rw [if_neg one_ne_zero, if_neg one_ne_zero, diagSeq0_length,
          show v + 1 - 1 = v by omega, hgd v (by omega),
          hgd (G.length + 1) (by omega)] at hb
      have hb' : v ≤ G.length + 1 := hb
      omega
  subst hR
  have hG1 : G.length + 1 = v := by simpa using hG
  -- the prefix entries and the last pair
  have hGent : ∀ h, h < G.length → G.getD h (0,0) = (h, h) := by
    intro h hh
    have h1 : (diagSeq 0 v).getD h (0,0) = G.getD h (0,0) := by
      rw [hMeq, getD_append_left (by simp; omega), getD_append_left hh]
    rw [hgd h (by omega)] at h1
    exact h1.symm
  have hlp : lp = (v, v) := by
    have h1 : (diagSeq 0 v).getD v (0,0) = lp := by
      rw [hMeq, getD_append_right (by simp; omega)]
      have h2 : v - (G ++ [(v0,w0)]).length = 0 := by simp; omega
      rw [h2, List.getD_cons_zero]
    rw [hgd v (by omega)] at h1
    exact h1.symm
  have h9 : (diagSeq 0 v).getD G.length (0,0) = (v0, w0) := by
    rw [hMeq, getD_append_left (by simp),
        getD_append_right le_rfl, Nat.sub_self, List.getD_cons_zero]
  rw [hgd G.length (by omega)] at h9
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq1 hq2 _ _
    simp at hq2
    omega
  · intro _ q hq
    simp at hq
    rw [hq, List.getD_cons_zero]
  · intro _ a _ _ _ h ha hh
    rw [hGent h hh, hlp]
    show h + 1 < v
    omega
  · intro _ _ q hq1 hq2
    simp at hq2
    omega
  · intro _ _ a q q' ha hq hq'
    simp at hq'
    omega
  · intro _
    rw [hlp]
    have h10 := congrArg Prod.snd h9
    simp at h10
    show (v, v).2 = w0 + 1
    omega
  · intro _ q hq1 hq2 _ _
    simp at hq2
    omega
  · -- clause 8: no prefix column equals the block head
    intro _ j hj hcontra
    rw [hGent j hj] at hcontra
    have e1 := congrArg Prod.fst hcontra
    have e2 := congrArg Prod.fst h9
    simp at e1 e2
    omega
  · -- clause 9: vacuous, the block has a single column
    intro _ _ i hi0 hi _
    simp only [List.length_cons, List.length_nil] at hi
    omega
  · -- clause 10: i = m = 0 forced, conclusion reflexive via the tie premise
    intro _ i _ hi heq m hm1 hm2
    simp only [List.length_cons, List.length_nil] at hi hm2
    have hi0 : i = 0 := by omega
    have hm0 : m = 0 := by omega
    subst hi0
    subst hm0
    rw [heq]

/-- The guard under which `oper` truncates: zero last column or no unique
parent. -/
def predGuard (N : PairSeq) : Prop :=
  (entry N 0 (N.length - 1) = 0 ∧ entry N 1 (N.length - 1) = 0) ∨
  ¬ hasParent N (idx1 N (N.length - 1)) (N.length - 1)

/-- Guarded truncation images. -/
inductive predImages : PairSeq → PairSeq → Prop
  | refl (M : PairSeq) : predImages M M
  | step {M N : PairSeq} (h : predImages M N) (hg : predGuard N) :
      predImages M (Pred N)

/-- The spanning block facts along all guarded truncations. -/
def spanOKg (M : PairSeq) : Prop :=
  ∀ N, predImages M N → spanOK N

theorem spanOKg_spanOK {M : PairSeq} (h : spanOKg M) : spanOK M :=
  h M (predImages.refl M)

theorem predImages_trans {M N P : PairSeq} (h1 : predImages M N)
    (h2 : predImages N P) : predImages M P := by
  induction h2 with
  | refl => exact h1
  | step _ hg ih => exact ih.step hg

theorem spanOKg_pred {M : PairSeq} (h : spanOKg M) (hg : predGuard M) :
    spanOKg (Pred M) := by
  intro N hN
  exact h N (predImages_trans ((predImages.refl M).step hg) hN)

theorem spanOKg_self {M : PairSeq} (h : spanOK M)
    (hfix : ∀ N, predImages M N → N = M) : spanOKg M := by
  intro N hN
  rw [hfix N hN]
  exact h

/-- The diagonal's last column has the unique parent `v - 1`. -/
theorem diag_hasParent (v : ℕ) (hv : 1 ≤ v) :
    hasParent (diagSeq 0 v) (idx1 (diagSeq 0 v) ((diagSeq 0 v).length - 1))
      ((diagSeq 0 v).length - 1) := by
  have hlen : (diagSeq 0 v).length = v + 1 := diagSeq0_length v
  have h9 : (diagSeq 0 v).length - 1 = v := by rw [hlen]; omega
  rw [h9]
  have hi1 : idx1 (diagSeq 0 v) v = 1 := by
    unfold idx1
    rw [if_pos]
    unfold entry
    rw [if_neg one_ne_zero, diagSeq0_getD (by omega)]
    show 0 < (v, v).2
    omega
  rw [hi1]
  have hedge : nextrel1 (diagSeq 0 v) (v - 1) v := by
    refine ⟨by rw [hlen]; omega, by rw [hlen]; omega, by omega, ?_,
      le0_diagSeq (by omega) (by omega), ?_⟩
    · unfold entry
      rw [if_neg one_ne_zero, if_neg one_ne_zero, diagSeq0_getD (by omega),
          diagSeq0_getD (by omega)]
      show (v - 1, v - 1).2 < (v, v).2
      omega
    · intro j hj
      have hjv : j ≤ v := le0_le hj.2
      have hj1 : j = v := by omega
      rw [hj1]
  refine ⟨v - 1, ?_, ?_⟩
  · show nextrel1 (diagSeq 0 v) (v - 1) v
    exact hedge
  · intro y hy
    have hy' : nextrel1 (diagSeq 0 v) y v := hy
    exact nextrel1_unique hy' hedge

theorem predImages_diag {v : ℕ} (hv : 1 ≤ v) :
    ∀ N, predImages (diagSeq 0 v) N → N = diagSeq 0 v := by
  intro N h
  induction h with
  | refl => rfl
  | step h hg ih =>
    exfalso
    rw [ih] at hg
    rcases hg with ⟨-, h1⟩ | hp
    · unfold entry at h1
      rw [if_neg one_ne_zero, diagSeq0_length,
          show v + 1 - 1 = v by omega, diagSeq0_getD (by omega)] at h1
      omega
    · exact hp (diag_hasParent v hv)

theorem predImages_diag_zero :
    ∀ N, predImages (diagSeq 0 0) N → N = diagSeq 0 0 := by
  intro N h
  induction h with
  | refl => rfl
  | step h hg ih =>
    rw [ih]
    unfold Pred
    rw [if_pos (by rw [diagSeq0_length])]

theorem spanOKg_diagSeq (v : ℕ) : spanOKg (diagSeq 0 v) := by
  rcases Nat.eq_zero_or_pos v with h0 | hv
  · subst h0
    exact spanOKg_self (spanOK_diagSeq 0) predImages_diag_zero
  · exact spanOKg_self (spanOK_diagSeq v) (predImages_diag hv)

/-- The remaining spanning obligation: the copy expansion and its guarded
truncations satisfy the block facts. -/
def copySpanOK (M : PairSeq) (n : ℕ) : Prop :=
  ∀ G v0 w0 (R : PairSeq) (lp : ℕ × ℕ) d0,
    M = G ++ ((v0,w0) :: R) ++ [lp] →
    M⟦n⟧ = copyExp G ((v0,w0) :: R) d0 n →
    (∀ p ∈ R, v0 < p.1) →
    nextR M (idx1 M (M.length - 1)) G.length (M.length - 1) →
    ((d0 = 0 ∧ idx1 M (M.length - 1) = 0) ∨ (0 < d0 ∧ w0 < lp.2 ∧
      lp.1 = v0 + d0 ∧ nextrel1 M G.length (M.length - 1))) →
    spanOKg (M⟦n⟧)

/-- **The spanning facts along the standard closure**, modulo the copy
obligation. -/
theorem spanOKg_ST_PS {M : PairSeq} (hM : ST_PS M)
    (hbad : ∀ N k, ST_PS N → 1 ≤ k → copySpanOK N k) : spanOKg M := by
  induction hM with
  | diag v => exact spanOKg_diagSeq v
  | @oper N k hN hk ih =>
    by_cases hL0 : N.length - 1 = 0
    · rw [oper_eq_self_of_short k hL0]
      exact ih
    by_cases hz : entry N 0 (N.length - 1) = 0 ∧ entry N 1 (N.length - 1) = 0
    · rw [oper_eq_pred_of_zero k hL0 hz]
      exact spanOKg_pred ih (Or.inl hz)
    by_cases hp : hasParent N (idx1 N (N.length - 1)) (N.length - 1)
    case neg =>
      rw [oper_eq_pred_of_noParent k hL0 hz hp]
      exact spanOKg_pred ih (Or.inr hp)
    case pos =>
      obtain ⟨G, v0, w0, R, d0, lp, hMeq, hX, hdom, -, hd0, hnxt⟩ :=
        oper_bad_blocks (by omega) hz hp hk
      exact hbad N k hN hk G v0 w0 R lp d0 hMeq hX hdom hnxt hd0

/-- The invariant package with the spanning obligation reduced to the copy
case. -/
theorem I_ST_PS' {M : PairSeq} (hM : ST_PS M)
    (hseam1 : ∀ N k, ST_PS N → 1 ≤ k → seamOK1 N k)
    (hbad : ∀ N k, ST_PS N → 1 ≤ k → copySpanOK N k) :
    hmok M ∧ tailok M ∧ classOK M :=
  I_ST_PS hM hseam1
    (fun N k hN _ => spanOKg_spanOK (spanOKg_ST_PS hN hbad))

/-- In the one-root world, spanning-fact instances anchored at a copy root
are vacuous: the row-1 premises collapse since all roots share `w0`. -/
theorem spanOK_roots_rootsplit {G : PairSeq} {v0 w0 d0 n : ℕ}
    {GX : PairSeq} {vX wX : ℕ} {RX : PairSeq} {lpX : ℕ × ℕ} {dX : ℕ}
    (hX : copyExp G [(v0,w0)] d0 n = GX ++ ((vX,wX) :: RX) ++ [lpX])
    (hg : G.length ≤ GX.length)
    (hd0X : (dX = 0 ∧ idx1 (copyExp G [(v0,w0)] d0 n)
        ((copyExp G [(v0,w0)] d0 n).length - 1) = 0)
      ∨ (0 < dX ∧ wX < lpX.2 ∧ lpX.1 = vX + dX ∧
        nextrel1 (copyExp G [(v0,w0)] d0 n) GX.length
          ((copyExp G [(v0,w0)] d0 n).length - 1))) :
    (∀ q, 0 < q → q < ((vX,wX) :: RX).length →
      le0 ((vX,wX) :: RX) 0 q → 0 < (((vX,wX) :: RX).getD q (0,0)).2 →
      wX < (((vX,wX) :: RX).getD q (0,0)).2)
    ∧ (0 < dX → ∀ q, q < ((vX,wX) :: RX).length →
      wX ≤ (((vX,wX) :: RX).getD q (0,0)).2)
    ∧ (0 < dX → ∀ a, a < GX.length →
      le0 (copyExp G [(v0,w0)] d0 n) a GX.length →
      (GX.getD a (0,0)).2 < wX →
      ∀ h, a < h → h < GX.length → (GX.getD h (0,0)).1 + 1 < lpX.1)
    ∧ (0 < wX → 0 < dX → ∀ q, 0 < q → q < ((vX,wX) :: RX).length →
      (((vX,wX) :: RX).getD q (0,0)).1 + 1 < vX + 2 * dX)
    ∧ (0 < wX → 0 < dX → ∀ a q q', a < q → q < q' →
      q' < ((vX,wX) :: RX).length →
      (((vX,wX) :: RX).getD q (0,0)).1 + 1
          + (((vX,wX) :: RX).getD a (0,0)).1
        < 2 * (((vX,wX) :: RX).getD q' (0,0)).1)
    ∧ (0 < dX → lpX.2 = wX + 1)
    ∧ (0 < dX → ∀ q, 0 < q → q < ((vX,wX) :: RX).length →
      le0 ((vX,wX) :: RX) 0 q → 0 < (((vX,wX) :: RX).getD q (0,0)).2 →
      le0 (GX ++ ((vX,wX) :: RX) ++ [lpX]) (GX.length + q)
        ((GX ++ ((vX,wX) :: RX) ++ [lpX]).length - 1)
      ∨ ((vX,wX) :: RX).getD q (0,0) = lpX) := by
  -- lengths
  have hone : ([(v0,w0)] : PairSeq).length = 1 := rfl
  have hXlen : (copyExp G [(v0,w0)] d0 n).length = G.length + n * 1 := by
    rw [← hone]
    exact copyExp_length ..
  have hRXlen : ((vX,wX) :: RX).length = RX.length + 1 := rfl
  have hlenX : GX.length + (RX.length + 1) + 1 = G.length + n := by
    have h := congrArg List.length hX
    rw [hXlen] at h
    simp at h
    omega
  -- every position from G.length on is a root (v0 + k*d0, w0)
  have hent : ∀ k, k < n → (copyExp G [(v0,w0)] d0 n).getD (G.length + k) (0,0)
      = (v0 + k * d0, w0) := by
    intro k hk
    rw [show G.length + k = G.length + (k * ([(v0,w0)] : PairSeq).length + 0) by
        rw [hone]; omega,
        copyExp_getD_copy hk (by rw [hone]; omega), List.getD_cons_zero]
  -- the split head and the last column are roots
  have hroot : (vX, wX) = (v0 + (GX.length - G.length) * d0, w0) := by
    have h1 : (copyExp G [(v0,w0)] d0 n).getD GX.length (0,0) = (vX, wX) := by
      rw [hX, getD_append_left (by simp),
          getD_append_right le_rfl, Nat.sub_self, List.getD_cons_zero]
    rw [show GX.length = G.length + (GX.length - G.length) by omega,
        hent _ (by omega)] at h1
    exact h1.symm
  have hwX : wX = w0 := by
    have := congrArg Prod.snd hroot
    simpa using this
  have hlast : (copyExp G [(v0,w0)] d0 n).getD
      ((copyExp G [(v0,w0)] d0 n).length - 1) (0,0)
      = (v0 + (n - 1) * d0, w0) := by
    rw [hXlen, show G.length + n * 1 - 1 = G.length + (n - 1) by omega,
        hent _ (by omega)]
  rcases hd0X with ⟨hdz, hi0⟩ | ⟨hdp, hwlt, hlp1, hnx⟩
  · -- untriggered: w0 = 0 kills the BF1 premise
    have hw0 : w0 = 0 := by
      unfold idx1 at hi0
      by_cases hpos : 0 < entry (copyExp G [(v0,w0)] d0 n) 1
          ((copyExp G [(v0,w0)] d0 n).length - 1)
      · rw [if_pos hpos] at hi0
        exact absurd hi0 one_ne_zero
      · push Not at hpos
        unfold entry at hpos
        rw [if_neg one_ne_zero, hlast] at hpos
        simpa using hpos
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro q hq1 hq2 hle hpos
      -- every block entry is a root with row-1 = w0 = 0
      have hq3 : GX.length + q < G.length + n := by omega
      have hqe : ((vX,wX) :: RX).getD q (0,0)
          = (copyExp G [(v0,w0)] d0 n).getD (GX.length + q) (0,0) := by
        rw [hX, getD_append_left (by simp; omega),
            getD_append_right (by omega)]
        congr 1
        omega
      rw [show GX.length + q = G.length + (GX.length - G.length + q) by omega,
          hent _ (by omega)] at hqe
      rw [hqe] at hpos
      simp at hpos
      omega
    · intro hdp
      exfalso
      omega
    · intro hdp
      exfalso
      omega
    · intro _ hdp
      exfalso
      omega
    · intro _ hdp
      exfalso
      omega
    · intro hdp
      exfalso
      omega
    · intro hdp
      exfalso
      omega
  · -- triggered: wX < lpX.2 = w0 = wX is absurd
    exfalso
    have hlpX : lpX = (v0 + (n - 1) * d0, w0) := by
      have h1 : (copyExp G [(v0,w0)] d0 n).getD
          ((copyExp G [(v0,w0)] d0 n).length - 1) (0,0) = lpX := by
        have hidx : (copyExp G [(v0,w0)] d0 n).length - 1
            = (GX ++ ((vX,wX) :: RX)).length + 0 := by
          rw [hXlen]
          simp only [List.length_append, List.length_cons, Nat.add_zero]
          omega
        rw [hidx, hX, getD_append_right (Nat.le_add_right _ _),
            Nat.add_sub_cancel_left, List.getD_cons_zero]
      rw [hlast] at h1
      exact h1.symm
    rw [hlpX] at hwlt
    simp at hwlt
    omega

/-- A multi-column block keeps the expansion guard off: the last column is
positive and, by standardness, uniquely parented. -/
theorem copyExp_noguard {N : PairSeq} {k : ℕ} {G R : PairSeq} {v0 w0 d0 : ℕ}
    (hN : ST_PS N) (hk : 1 ≤ k)
    (hX : N⟦k⟧ = copyExp G ((v0,w0) :: R) d0 k)
    (hdom : ∀ p ∈ R, v0 < p.1) (hR : R ≠ []) :
    ¬ predGuard (N⟦k⟧) := by
  have hL1 : 1 ≤ ((v0,w0) :: R).length := by simp
  have hR1 : 1 ≤ R.length := by
    rcases R with _ | ⟨r, R'⟩
    · exact absurd rfl hR
    · simp
  have hBR : ((v0,w0) :: R).length = R.length + 1 := rfl
  have hXlen : (N⟦k⟧).length = G.length + k * ((v0,w0) :: R).length := by
    rw [hX]
    exact copyExp_length ..
  have hnL : k * ((v0,w0) :: R).length
      = (k - 1) * ((v0,w0) :: R).length + ((v0,w0) :: R).length := by
    have h9 : k - 1 + 1 = k := by omega
    calc k * ((v0,w0) :: R).length
        = (k - 1 + 1) * ((v0,w0) :: R).length := by rw [h9]
    _ = (k - 1) * ((v0,w0) :: R).length + 1 * ((v0,w0) :: R).length := by
        rw [Nat.add_mul]
    _ = (k - 1) * ((v0,w0) :: R).length + ((v0,w0) :: R).length := by
        rw [Nat.one_mul]
  -- the last column's row 0 is positive
  have hlastpos : 0 < entry (N⟦k⟧) 0 ((N⟦k⟧).length - 1) := by
    have hidx : (N⟦k⟧).length - 1
        = G.length + ((k - 1) * ((v0,w0) :: R).length
          + (((v0,w0) :: R).length - 1)) := by
      rw [hXlen]
      omega
    unfold entry
    rw [if_pos rfl, hidx, hX, copyExp_getD_copy (by omega) (by omega)]
    obtain ⟨q', hq'⟩ : ∃ q', ((v0,w0) :: R).length - 1 = q' + 1 :=
      ⟨((v0,w0) :: R).length - 2, by omega⟩
    rw [hq', List.getD_cons_succ]
    have hmem : R.getD q' (0,0) ∈ R := by
      rw [getD_eq_getElem' _ _ (by omega)]
      exact List.getElem_mem ..
    have hv := hdom _ hmem
    show 0 < (R.getD q' (0,0)).1 + (k - 1) * d0
    omega
  intro hg
  rcases hg with ⟨h0, -⟩ | hp
  · rw [h0] at hlastpos
    exact absurd hlastpos (lt_irrefl 0)
  · apply hp
    have hSTX : ST_PS (N⟦k⟧) := ST_PS.oper hN hk
    have hb := blockok_ST_PS hSTX
    have hz := z0ok_ST_PS hSTX
    have hlt : (N⟦k⟧).length - 1 < (N⟦k⟧).length := by
      rw [hXlen]
      have h9 : 1 ≤ k * ((v0,w0) :: R).length := by
        calc 1 = 1 * 1 := rfl
        _ ≤ k * ((v0,w0) :: R).length :=
            Nat.mul_le_mul hk (by omega)
      omega
    by_cases hiX : idx1 (N⟦k⟧) ((N⟦k⟧).length - 1) = 0
    · obtain ⟨p, hedge⟩ := parent0_exists hb hlt hlastpos
      refine ⟨p, ?_, ?_⟩
      · rw [hiX]
        show nextrel0 (N⟦k⟧) p ((N⟦k⟧).length - 1)
        exact hedge
      · intro y hy
        rw [hiX] at hy
        have hy' : nextrel0 (N⟦k⟧) y ((N⟦k⟧).length - 1) := hy
        exact nextrel0_unique hy' hedge
    · have hpos1 : 0 < entry (N⟦k⟧) 1 ((N⟦k⟧).length - 1) := by
        by_contra hc
        exact hiX (by unfold idx1; rw [if_neg hc])
      obtain ⟨p, hedge⟩ := parent1_exists hb hz hlt hpos1
      have hi1 : idx1 (N⟦k⟧) ((N⟦k⟧).length - 1) = 1 := by
        unfold idx1
        rw [if_pos hpos1]
      refine ⟨p, ?_, ?_⟩
      · rw [hi1]
        show nextrel1 (N⟦k⟧) p ((N⟦k⟧).length - 1)
        exact hedge
      · intro y hy
        rw [hi1] at hy
        have hy' : nextrel1 (N⟦k⟧) y ((N⟦k⟧).length - 1) := hy
        exact nextrel1_unique hy' hedge

/-- With a multi-column block the guarded chain from the expansion is
trivial. -/
theorem predImages_copyExp_fix {N : PairSeq} {k : ℕ} {G R : PairSeq}
    {v0 w0 d0 : ℕ} (hN : ST_PS N) (hk : 1 ≤ k)
    (hX : N⟦k⟧ = copyExp G ((v0,w0) :: R) d0 k)
    (hdom : ∀ p ∈ R, v0 < p.1) (hR : R ≠ []) :
    ∀ Y, predImages (N⟦k⟧) Y → Y = N⟦k⟧ := by
  intro Y h
  induction h with
  | refl => rfl
  | step h hg ih =>
    exfalso
    rw [ih] at hg
    exact copyExp_noguard hN hk hX hdom hR hg

/-- **Every block column is a row-0 descendant of the root**: the `r1ok`
one-level descent stays inside the block (the valley condition at the root
excludes prefix parents), so iterating it builds the ascending chain. -/
theorem le0_block_root {M G R : PairSeq} {v0 w0 : ℕ} {lp : ℕ × ℕ}
    (hr1 : r1ok M) (hMeq : M = G ++ ((v0,w0) :: R) ++ [lp])
    (hdom : ∀ p ∈ R, v0 < p.1) :
    ∀ q, q < ((v0,w0) :: R).length → le0 ((v0,w0) :: R) 0 q := by
  have hBR : ((v0,w0) :: R).length = R.length + 1 := rfl
  have hMlen : M.length = G.length + ((v0,w0) :: R).length + 1 := by
    rw [hMeq]
    exact hostM_length ..
  have hgblk : ∀ q, q < ((v0,w0) :: R).length →
      M.getD (G.length + q) (0,0) = ((v0,w0) :: R).getD q (0,0) := by
    intro q hq
    rw [hMeq]
    exact hostM_getD_blk hq
  -- strong induction on the level above the root
  suffices h : ∀ d q, q < ((v0,w0) :: R).length →
      (((v0,w0) :: R).getD q (0,0)).1 = v0 + d →
      le0 ((v0,w0) :: R) 0 q by
    intro q hq
    rcases Nat.eq_zero_or_pos q with h0 | hqpos
    · rw [h0]
      exact ⟨by omega, by omega, .refl⟩
    · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      have hmem : R.getD q' (0,0) ∈ R := by
        rw [getD_eq_getElem' _ _ (by omega)]
        exact List.getElem_mem ..
      have hv := hdom _ hmem
      refine h ((R.getD q' (0,0)).1 - v0) (q' + 1) hq ?_
      rw [List.getD_cons_succ]
      omega
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro q hq hlev
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · -- level v0: only the root
      rcases Nat.eq_zero_or_pos q with h0 | hqpos
      · rw [h0]
        exact ⟨by omega, by omega, .refl⟩
      · exfalso
        obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
        have hmem : R.getD q' (0,0) ∈ R := by
          rw [getD_eq_getElem' _ _ (by omega)]
          exact List.getElem_mem ..
        have hv := hdom _ hmem
        rw [List.getD_cons_succ] at hlev
        omega
    · -- positive level: descend one step via r1ok
      have hqpos : 0 < q := by
        rcases Nat.eq_zero_or_pos q with h0 | hpos
        · exfalso
          rw [h0, List.getD_cons_zero] at hlev
          omega
        · exact hpos
      have hjM : G.length + q < M.length := by omega
      have hpos0 : 0 < (M.getD (G.length + q) (0,0)).1 := by
        rw [hgblk q hq, hlev]
        omega
      obtain ⟨k, hklt, hklev, hkval, -⟩ := hr1 (G.length + q) hjM hpos0
      rw [hgblk q hq, hlev] at hklev hkval
      -- the parent stays in the block
      have hkg : G.length ≤ k := by
        by_contra hkpre
        push Not at hkpre
        have h9 := hkval G.length (by omega) (by omega)
        have hroot : M.getD G.length (0,0) = (v0, w0) := by
          have h10 := hgblk 0 (by omega)
          rw [Nat.add_zero] at h10
          rw [h10, List.getD_cons_zero]
        rw [hroot] at h9
        have h9' : v0 + d ≤ v0 := h9
        omega
      obtain ⟨q', hq'⟩ : ∃ q', k = G.length + q' := ⟨k - G.length, by omega⟩
      have hq'lt : q' < ((v0,w0) :: R).length := by omega
      have hq'q : q' < q := by omega
      -- its level is one below
      have hlev' : (((v0,w0) :: R).getD q' (0,0)).1 = v0 + (d - 1) := by
        have h9 := hklev
        rw [hq', hgblk q' hq'lt] at h9
        omega
      -- the in-block edge
      have hedge : nextrel0 ((v0,w0) :: R) q' q := by
        refine ⟨by omega, by omega, hq'q, ?_, ?_⟩
        · unfold entry
          rw [if_pos rfl, if_pos rfl, hlev', hlev]
          omega
        · intro l hl
          have h9 := hkval (G.length + l) (by omega) (by omega)
          rw [hgblk l (by omega)] at h9
          unfold entry
          rw [if_pos rfl, if_pos rfl, hlev]
          exact h9
      have hch := ih (d - 1) (by omega) q' hq'lt hlev'
      exact ⟨by omega, by omega, hch.2.2.tail hedge⟩

/-- With a multi-column block, any parent edge into the expansion's last
column comes from the last copy. -/
theorem copyExp_parent_in_last {G R : PairSeq} {v0 w0 d0 n p : ℕ}
    (hn : 1 ≤ n) (hdom : ∀ x ∈ R, v0 < x.1) (hR : R ≠ [])
    (hBF1 : ∀ q, 0 < q → q < ((v0,w0) :: R).length →
      le0 ((v0,w0) :: R) 0 q → 0 < (((v0,w0) :: R).getD q (0,0)).2 →
      w0 < (((v0,w0) :: R).getD q (0,0)).2)
    (hnx : nextR (copyExp G ((v0,w0) :: R) d0 n)
      (idx1 (copyExp G ((v0,w0) :: R) d0 n)
        ((copyExp G ((v0,w0) :: R) d0 n).length - 1)) p
      ((copyExp G ((v0,w0) :: R) d0 n).length - 1)) :
    G.length + (n - 1) * ((v0,w0) :: R).length ≤ p := by
  by_contra hlt
  push Not at hlt
  have hL2 : 2 ≤ ((v0,w0) :: R).length := by
    rcases R with _ | ⟨r, R'⟩
    · exact absurd rfl hR
    · simp
  unfold nextR at hnx
  by_cases hiX : idx1 (copyExp G ((v0,w0) :: R) d0 n)
      ((copyExp G ((v0,w0) :: R) d0 n).length - 1) = 0
  · rw [if_pos hiX] at hnx
    have h9 := seam_edge0_short hn hdom hlt hnx
    omega
  · rw [if_neg hiX] at hnx
    have hpos : 0 < entry (copyExp G ((v0,w0) :: R) d0 n) 1
        ((copyExp G ((v0,w0) :: R) d0 n).length - 1) := by
      by_contra hc
      exact hiX (by unfold idx1; rw [if_neg hc])
    have h9 := seam_edge1_short hn hdom hBF1 hlt hnx hpos
    omega

/-- **Last-copy split correspondence**: a decomposition of the expansion
whose split lies in the last copy reads off as the shifted block suffix. -/
theorem copyExp_split_corr {G R : PairSeq} {v0 w0 d0 n : ℕ}
    {GX : PairSeq} {vX wX : ℕ} {RX : PairSeq} {lpX : ℕ × ℕ}
    (hn : 1 ≤ n)
    (hX : copyExp G ((v0,w0) :: R) d0 n = GX ++ ((vX,wX) :: RX) ++ [lpX])
    (hge : G.length + (n - 1) * ((v0,w0) :: R).length ≤ GX.length) :
    ∃ q0, GX.length = G.length + ((n - 1) * ((v0,w0) :: R).length + q0) ∧
      q0 + (RX.length + 1) + 1 = ((v0,w0) :: R).length ∧
      (∀ q, q < RX.length + 1 →
        ((vX,wX) :: RX).getD q (0,0)
          = ((((v0,w0) :: R).getD (q0 + q) (0,0)).1 + (n - 1) * d0,
             (((v0,w0) :: R).getD (q0 + q) (0,0)).2)) ∧
      lpX = ((((v0,w0) :: R).getD (((v0,w0) :: R).length - 1) (0,0)).1
              + (n - 1) * d0,
             (((v0,w0) :: R).getD (((v0,w0) :: R).length - 1) (0,0)).2) := by
  have hL1 : 1 ≤ ((v0,w0) :: R).length := by simp
  have hbr2 : n * ((v0,w0) :: R).length = n * (R.length + 1) := rfl
  have hbr3 : (n - 1) * ((v0,w0) :: R).length = (n - 1) * (R.length + 1) :=
    rfl
  have hXlen : (copyExp G ((v0,w0) :: R) d0 n).length
      = G.length + n * ((v0,w0) :: R).length := copyExp_length ..
  have hnL : n * ((v0,w0) :: R).length
      = (n - 1) * ((v0,w0) :: R).length + ((v0,w0) :: R).length := by
    have h9 : n - 1 + 1 = n := by omega
    calc n * ((v0,w0) :: R).length
        = (n - 1 + 1) * ((v0,w0) :: R).length := by rw [h9]
    _ = (n - 1) * ((v0,w0) :: R).length + 1 * ((v0,w0) :: R).length := by
        rw [Nat.add_mul]
    _ = (n - 1) * ((v0,w0) :: R).length + ((v0,w0) :: R).length := by
        rw [Nat.one_mul]
  have hlenX : GX.length + (RX.length + 1) + 1
      = G.length + n * ((v0,w0) :: R).length := by
    have h := congrArg List.length hX
    rw [hXlen] at h
    simp at h
    omega
  refine ⟨GX.length - (G.length + (n - 1) * ((v0,w0) :: R).length),
    by omega, by omega, ?_, ?_⟩
  · intro q hq
    have h1 : ((vX,wX) :: RX).getD q (0,0)
        = (copyExp G ((v0,w0) :: R) d0 n).getD (GX.length + q) (0,0) := by
      rw [hX, getD_append_left (by simp; omega),
          getD_append_right (by omega)]
      congr 1
      omega
    rw [h1, show GX.length + q = G.length
          + ((n - 1) * ((v0,w0) :: R).length
            + (GX.length - (G.length + (n - 1) * ((v0,w0) :: R).length)
              + q)) by omega,
        copyExp_getD_copy (by omega) (by omega)]
  · have h1 : (copyExp G ((v0,w0) :: R) d0 n).getD
        ((copyExp G ((v0,w0) :: R) d0 n).length - 1) (0,0) = lpX := by
      have hidx : (copyExp G ((v0,w0) :: R) d0 n).length - 1
          = (GX ++ ((vX,wX) :: RX)).length + 0 := by
        rw [hXlen]
        simp only [List.length_append, List.length_cons, Nat.add_zero]
        omega
      rw [hidx, hX, getD_append_right (Nat.le_add_right _ _),
          Nat.add_sub_cancel_left, List.getD_cons_zero]
    rw [show (copyExp G ((v0,w0) :: R) d0 n).length - 1
          = G.length + ((n - 1) * ((v0,w0) :: R).length
            + (((v0,w0) :: R).length - 1)) by rw [hXlen]; omega,
        copyExp_getD_copy (by omega) (by omega)] at h1
    exact h1.symm

/-- The triple profile transfers to any shifted suffix segment. -/
theorem profile_transfer {B BX : PairSeq} {s q0 : ℕ}
    (hcorr : ∀ q, q < BX.length →
      (BX.getD q (0,0)).1 = (B.getD (q0 + q) (0,0)).1 + s)
    (hlen : q0 + BX.length ≤ B.length)
    (hprof : ∀ a q q', a < q → q < q' → q' < B.length →
      (B.getD q (0,0)).1 + 1 + (B.getD a (0,0)).1
        < 2 * (B.getD q' (0,0)).1) :
    ∀ a q q', a < q → q < q' → q' < BX.length →
      (BX.getD q (0,0)).1 + 1 + (BX.getD a (0,0)).1
        < 2 * (BX.getD q' (0,0)).1 := by
  intro a q q' ha hq hq'
  rw [hcorr a (by omega), hcorr q (by omega), hcorr q' (by omega)]
  have h9 := hprof (q0 + a) (q0 + q) (q0 + q') (by omega) (by omega)
    (by omega)
  omega

/-- The fourth block fact at a last-copy split follows from the host's
triple profile anchored at the split offset. -/
theorem bf45_transfer {B BX : PairSeq} {s q0 vX dX : ℕ}
    (hcorr : ∀ q, q < BX.length →
      (BX.getD q (0,0)).1 = (B.getD (q0 + q) (0,0)).1 + s)
    (hlen : q0 + BX.length + 1 = B.length)
    (hvX : vX = (B.getD q0 (0,0)).1 + s)
    (hdX : (B.getD (B.length - 1) (0,0)).1 + s = vX + dX)
    (hprof : ∀ a q q', a < q → q < q' → q' < B.length →
      (B.getD q (0,0)).1 + 1 + (B.getD a (0,0)).1
        < 2 * (B.getD q' (0,0)).1) :
    ∀ q, 0 < q → q < BX.length →
      (BX.getD q (0,0)).1 + 1 < vX + 2 * dX := by
  intro q hq0 hq
  rw [hcorr q (by omega)]
  have h9 := hprof q0 (q0 + q) (B.length - 1) (by omega) (by omega)
    (by omega)
  omega

/-- At a last-copy split whose suffix consists of ancestors of the tail,
the parent-edge maximality pushes every later row-1 strictly above the
split head's. -/
theorem split_row1_strict {X : PairSeq} {gX last : ℕ}
    (hedge : nextrel1 X gX last)
    (hanc : ∀ j, gX < j → j < last → le0 X j last) :
    ∀ j, gX < j → j ≤ last →
      entry X 1 gX < entry X 1 j := by
  intro j hj1 hj2
  have hC1 := hedge.2.2.2.1
  rcases Nat.eq_or_lt_of_le hj2 with he | hlt
  · rw [he]
    exact hC1
  · have hmax := hedge.2.2.2.2.2 j ⟨hj1, hanc j hj1 hlt⟩
    omega

/-- BF1 restricts to truncated blocks. -/
theorem bf1_take {v0 w0 : ℕ} {R : PairSeq} {m : ℕ}
    (h : ∀ q, 0 < q → q < ((v0,w0) :: R).length →
      le0 ((v0,w0) :: R) 0 q → 0 < (((v0,w0) :: R).getD q (0,0)).2 →
      w0 < (((v0,w0) :: R).getD q (0,0)).2) :
    ∀ q, 0 < q → q < ((v0,w0) :: R.take m).length →
      le0 ((v0,w0) :: R.take m) 0 q →
      0 < (((v0,w0) :: R.take m).getD q (0,0)).2 →
      w0 < (((v0,w0) :: R.take m).getD q (0,0)).2 := by
  have hcons : (v0,w0) :: R.take m = ((v0,w0) :: R).take (m + 1) := by
    rw [List.take_succ_cons]
  intro q hq1 hq2 hle hpos
  rw [hcons] at hq2 hle hpos ⊢
  rw [List.length_take] at hq2
  have hqlt : q < ((v0,w0) :: R).length := by omega
  rw [getD_take (by omega)] at hpos ⊢
  exact h q hq1 hqlt
    ((le0_take_iff (m := m + 1) (by omega) hqlt).1 hle) hpos

/-- BF2 restricts to truncated blocks. -/
theorem bf2_take {v0 w0 : ℕ} {R : PairSeq} {m : ℕ}
    (h : ∀ q, q < ((v0,w0) :: R).length →
      w0 ≤ (((v0,w0) :: R).getD q (0,0)).2) :
    ∀ q, q < ((v0,w0) :: R.take m).length →
      w0 ≤ (((v0,w0) :: R.take m).getD q (0,0)).2 := by
  have hcons : (v0,w0) :: R.take m = ((v0,w0) :: R).take (m + 1) := by
    rw [List.take_succ_cons]
  intro q hq
  rw [hcons] at hq ⊢
  rw [List.length_take] at hq
  rw [getD_take (by omega)]
  exact h q (by omega)

/-- `nextrel0` only reads lengths and row-0 entries. -/
theorem nextrel0_congr {S T : PairSeq} (hlen : S.length = T.length)
    (hent : ∀ i, i < S.length → entry S 0 i = entry T 0 i) {a b : ℕ} :
    nextrel0 S a b ↔ nextrel0 T a b := by
  unfold nextrel0
  rw [hlen]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, h2, h3, ?_, ?_⟩
    · rwa [hent a (by omega), hent b (by omega)] at h4
    · intro j hj
      have h6 := h5 j hj
      rwa [hent b (by omega), hent j (by omega)] at h6
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, h2, h3, ?_, ?_⟩
    · rw [hent a (by omega), hent b (by omega)]
      exact h4
    · intro j hj
      rw [hent b (by omega), hent j (by omega)]
      exact h5 j hj

/-- `le0` only reads lengths and row-0 entries. -/
theorem le0_congr {S T : PairSeq} (hlen : S.length = T.length)
    (hent : ∀ i, i < S.length → entry S 0 i = entry T 0 i) {a b : ℕ} :
    le0 S a b ↔ le0 T a b := by
  unfold le0
  rw [hlen]
  have hrtg : ∀ a b, Relation.ReflTransGen (nextrel0 S) a b →
      Relation.ReflTransGen (nextrel0 T) a b := by
    intro a b h
    induction h with
    | refl => exact .refl
    | @tail y z _ hs ih =>
      refine ih.tail ?_
      exact (nextrel0_congr hlen hent).1 hs
  have hrtg' : ∀ a b, Relation.ReflTransGen (nextrel0 T) a b →
      Relation.ReflTransGen (nextrel0 S) a b := by
    intro a b h
    induction h with
    | refl => exact .refl
    | @tail y z _ hs ih =>
      refine ih.tail ?_
      exact (nextrel0_congr hlen hent).2 hs
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, hrtg a b h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, hrtg' a b h3⟩

/-- `nextrel0` is invariant under a uniform row-0 shift read entrywise. -/
theorem nextrel0_congr_shift {S T : PairSeq} {s : ℕ}
    (hlen : S.length = T.length)
    (hent : ∀ i, i < S.length → entry S 0 i = entry T 0 i + s) {a b : ℕ} :
    nextrel0 S a b ↔ nextrel0 T a b := by
  unfold nextrel0
  rw [hlen]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, h2, h3, ?_, ?_⟩
    · rw [hent a (by omega), hent b (by omega)] at h4
      omega
    · intro j hj
      have h6 := h5 j hj
      rw [hent b (by omega), hent j (by omega)] at h6
      omega
  · rintro ⟨h1, h2, h3, h4, h5⟩
    refine ⟨h1, h2, h3, ?_, ?_⟩
    · rw [hent a (by omega), hent b (by omega)]
      omega
    · intro j hj
      have h6 := h5 j hj
      rw [hent b (by omega), hent j (by omega)]
      omega

/-- `le0` is invariant under a uniform row-0 shift read entrywise. -/
theorem le0_congr_shift {S T : PairSeq} {s : ℕ}
    (hlen : S.length = T.length)
    (hent : ∀ i, i < S.length → entry S 0 i = entry T 0 i + s) {a b : ℕ} :
    le0 S a b ↔ le0 T a b := by
  unfold le0
  rw [hlen]
  have hrtg : ∀ a b, Relation.ReflTransGen (nextrel0 S) a b →
      Relation.ReflTransGen (nextrel0 T) a b := by
    intro a b h
    induction h with
    | refl => exact .refl
    | @tail y z _ hs ih => exact ih.tail ((nextrel0_congr_shift hlen hent).1 hs)
  have hrtg' : ∀ a b, Relation.ReflTransGen (nextrel0 T) a b →
      Relation.ReflTransGen (nextrel0 S) a b := by
    intro a b h
    induction h with
    | refl => exact .refl
    | @tail y z _ hs ih => exact ih.tail ((nextrel0_congr_shift hlen hent).2 hs)
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, hrtg a b h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, hrtg' a b h3⟩

/-- **BF1 at the root split**: the root-anchored row-1 ascent transfers to
the shifted truncated block through the entrywise correspondence. -/
theorem bf1_rootsplit {R RX : PairSeq} {v0 w0 vX wX s : ℕ}
    (hlen : (RX.length + 1) + 1 = ((v0,w0) :: R).length)
    (hcorr : ∀ q, q < RX.length + 1 →
      ((vX,wX) :: RX).getD q (0,0)
        = ((((v0,w0) :: R).getD q (0,0)).1 + s,
           (((v0,w0) :: R).getD q (0,0)).2))
    (hBF1 : ∀ q, 0 < q → q < ((v0,w0) :: R).length →
      le0 ((v0,w0) :: R) 0 q → 0 < (((v0,w0) :: R).getD q (0,0)).2 →
      w0 < (((v0,w0) :: R).getD q (0,0)).2) :
    ∀ q, 0 < q → q < ((vX,wX) :: RX).length →
      le0 ((vX,wX) :: RX) 0 q → 0 < (((vX,wX) :: RX).getD q (0,0)).2 →
      wX < (((vX,wX) :: RX).getD q (0,0)).2 := by
  have hBXlen : ((vX,wX) :: RX).length = RX.length + 1 := rfl
  have hBlen : ((v0,w0) :: R).length = R.length + 1 := rfl
  have hwX : wX = w0 := by
    have h9 := hcorr 0 (by omega)
    rw [List.getD_cons_zero, List.getD_cons_zero] at h9
    have h10 := congrArg Prod.snd h9
    simpa using h10
  intro q hq1 hq2 hle hpos
  rw [hBXlen] at hq2
  -- transfer the chain to the truncated host block
  have hT : le0 (((v0,w0) :: R).take (RX.length + 1)) 0 q := by
    refine (le0_congr_shift (s := s) ?_ ?_).1 hle
    · rw [hBXlen, List.length_take]
      omega
    · intro i hi
      rw [hBXlen] at hi
      unfold entry
      rw [if_pos rfl, if_pos rfl, hcorr i (by omega),
          getD_take (by omega)]
  have hle' : le0 ((v0,w0) :: R) 0 q :=
    (le0_take_iff (m := RX.length + 1) (by omega) (by omega)).1 hT
  -- the row-1 values match
  have hq2' : (((vX,wX) :: RX).getD q (0,0)).2
      = (((v0,w0) :: R).getD q (0,0)).2 := by
    rw [hcorr q (by omega)]
  rw [hq2'] at hpos ⊢
  rw [hwX]
  exact hBF1 q hq1 (by omega) hle' hpos

/-- **BF2 at the root split**: root row-1 minimality transfers through the
entrywise correspondence. -/
theorem bf2_rootsplit {R RX : PairSeq} {v0 w0 vX wX s : ℕ}
    (hlen : (RX.length + 1) + 1 = ((v0,w0) :: R).length)
    (hcorr : ∀ q, q < RX.length + 1 →
      ((vX,wX) :: RX).getD q (0,0)
        = ((((v0,w0) :: R).getD q (0,0)).1 + s,
           (((v0,w0) :: R).getD q (0,0)).2))
    (hBF2 : ∀ q, q < ((v0,w0) :: R).length →
      w0 ≤ (((v0,w0) :: R).getD q (0,0)).2) :
    ∀ q, q < ((vX,wX) :: RX).length →
      wX ≤ (((vX,wX) :: RX).getD q (0,0)).2 := by
  have hBXlen : ((vX,wX) :: RX).length = RX.length + 1 := rfl
  have hwX : wX = w0 := by
    have h9 := hcorr 0 (by omega)
    rw [List.getD_cons_zero, List.getD_cons_zero] at h9
    have h10 := congrArg Prod.snd h9
    simpa using h10
  intro q hq
  rw [hBXlen] at hq
  rw [hcorr q (by omega), hwX]
  show w0 ≤ (((v0,w0) :: R).getD q (0,0)).2
  exact hBF2 q (by omega)

/-- **Low ancestors of the last-copy root live in the prefix**: BF2
excludes copy positions, and the chain restricts to the host prefix
through the copy-0 root pivot. -/
theorem rootsplit_low_ancestor {G R : PairSeq} {v0 w0 d0 n : ℕ}
    {lp : ℕ × ℕ} {a : ℕ}
    (hn : 1 ≤ n) (hd0p : 0 < d0)
    (hdom : ∀ p ∈ R, v0 < p.1)
    (hBF2 : ∀ q, q < ((v0,w0) :: R).length →
      w0 ≤ (((v0,w0) :: R).getD q (0,0)).2)
    (ha : a < G.length + (n - 1) * ((v0,w0) :: R).length)
    (hle0 : le0 (copyExp G ((v0,w0) :: R) d0 n) a
      (G.length + (n - 1) * ((v0,w0) :: R).length))
    (ha2 : entry (copyExp G ((v0,w0) :: R) d0 n) 1 a < w0) :
    a < G.length ∧ le0 (G ++ ((v0,w0) :: R) ++ [lp]) a G.length ∧
      (G.getD a (0,0)).2 < w0 := by
  have hL1 : 1 ≤ ((v0,w0) :: R).length := by simp
  have hXlen : (copyExp G ((v0,w0) :: R) d0 n).length
      = G.length + n * ((v0,w0) :: R).length := copyExp_length ..
  have hnL : n * ((v0,w0) :: R).length
      = (n - 1) * ((v0,w0) :: R).length + ((v0,w0) :: R).length := by
    have h9 : n - 1 + 1 = n := by omega
    calc n * ((v0,w0) :: R).length
        = (n - 1 + 1) * ((v0,w0) :: R).length := by rw [h9]
    _ = (n - 1) * ((v0,w0) :: R).length + 1 * ((v0,w0) :: R).length := by
        rw [Nat.add_mul]
    _ = (n - 1) * ((v0,w0) :: R).length + ((v0,w0) :: R).length := by
        rw [Nat.one_mul]
  -- a lies in the prefix
  have hapre : a < G.length := by
    by_contra hge
    push Not at hge
    obtain ⟨ka, qa, hqaL, hdma⟩ : ∃ ka qa, qa < ((v0,w0) :: R).length ∧
        a - G.length = ((v0,w0) :: R).length * ka + qa :=
      ⟨_, _, Nat.mod_lt _ (by omega),
        (Nat.div_add_mod (a - G.length) ((v0,w0) :: R).length).symm⟩
    have hcma : ((v0,w0) :: R).length * ka = ka * ((v0,w0) :: R).length :=
      Nat.mul_comm ..
    have hkan : ka < n := by
      have h1 : ((v0,w0) :: R).length * ka
          < ((v0,w0) :: R).length * n := by
        have hcomm : n * ((v0,w0) :: R).length
            = ((v0,w0) :: R).length * n := Nat.mul_comm ..
        omega
      exact Nat.lt_of_mul_lt_mul_left h1
    have hav : entry (copyExp G ((v0,w0) :: R) d0 n) 1 a
        = (((v0,w0) :: R).getD qa (0,0)).2 := by
      rw [show a = G.length + (ka * ((v0,w0) :: R).length + qa) by omega]
      exact (entry_copyExp hkan hqaL).2
    rw [hav] at ha2
    have h9 := hBF2 qa hqaL
    omega
  refine ⟨hapre, ?_, ?_⟩
  · -- the chain restricts to the host
    have hroot0 : entry (copyExp G ((v0,w0) :: R) d0 n) 0 G.length
        = v0 := by
      have h9 := (entry_copyExp (G := G) (B := (v0,w0) :: R) (d0 := d0)
        (n := n) (k := 0) (q := 0) (by omega) (by omega)).1
      simp only [Nat.zero_mul, Nat.add_zero] at h9
      rw [h9, List.getD_cons_zero]
    have hpiv : ∀ y, G.length < y →
        y ≤ G.length + (n - 1) * ((v0,w0) :: R).length →
        entry (copyExp G ((v0,w0) :: R) d0 n) 0 G.length
          < entry (copyExp G ((v0,w0) :: R) d0 n) 0 y := by
      intro y hy1 hy2
      rw [hroot0]
      obtain ⟨ky, qy, hqyL, hdmy⟩ : ∃ ky qy, qy < ((v0,w0) :: R).length ∧
          y - G.length = ((v0,w0) :: R).length * ky + qy :=
        ⟨_, _, Nat.mod_lt _ (by omega),
          (Nat.div_add_mod (y - G.length) ((v0,w0) :: R).length).symm⟩
      have hcmy : ((v0,w0) :: R).length * ky
          = ky * ((v0,w0) :: R).length := Nat.mul_comm ..
      have hkyn : ky < n := by
        have h1 : ((v0,w0) :: R).length * ky
            < ((v0,w0) :: R).length * n := by
          have hcomm : n * ((v0,w0) :: R).length
              = ((v0,w0) :: R).length * n := Nat.mul_comm ..
          omega
        exact Nat.lt_of_mul_lt_mul_left h1
      have hey : entry (copyExp G ((v0,w0) :: R) d0 n) 0 y
          = (((v0,w0) :: R).getD qy (0,0)).1 + ky * d0 := by
        rw [show y = G.length + (ky * ((v0,w0) :: R).length + qy) by omega]
        exact (entry_copyExp hkyn hqyL).1
      rw [hey]
      rcases Nat.eq_zero_or_pos qy with hqy0 | hqypos
      · have hky1 : 1 ≤ ky := by
          rcases Nat.eq_zero_or_pos ky with h0 | h1
          · exfalso
            rw [h0, Nat.mul_zero] at hdmy
            omega
          · exact h1
        have hkd : 0 < ky * d0 := Nat.mul_pos hky1 hd0p
        rw [hqy0, List.getD_cons_zero]
        show v0 < (v0, w0).1 + ky * d0
        omega
      · obtain ⟨qy', rfl⟩ : ∃ qy', qy = qy' + 1 := ⟨qy - 1, by omega⟩
        rw [List.getD_cons_succ]
        have hmem : R.getD qy' (0,0) ∈ R := by
          rw [getD_eq_getElem' _ _ (by
            have h8 : ((v0,w0) :: R).length = R.length + 1 := rfl
            omega)]
          exact List.getElem_mem ..
        have hv := hdom _ hmem
        omega
    have hle0g : le0 (copyExp G ((v0,w0) :: R) d0 n) a G.length :=
      le0_to_pivot hle0 hapre (by omega) hpiv
    have htkXM : (copyExp G ((v0,w0) :: R) d0 n).take
        (G.length + ((v0,w0) :: R).length)
        = (G ++ ((v0,w0) :: R) ++ [lp]).take
          (G.length + ((v0,w0) :: R).length) := by
      have htkX : (copyExp G ((v0,w0) :: R) d0 n).take
          (G.length + ((v0,w0) :: R).length) = G ++ ((v0,w0) :: R) := by
        have h9 := copyExp_take_at (G := G) (B := (v0,w0) :: R) (d0 := d0)
          (n := n) (k := 0) (q := ((v0,w0) :: R).length) (by omega) le_rfl
        simpa [copyExp] using h9
      have htkM : (G ++ ((v0,w0) :: R) ++ [lp]).take
          (G.length + ((v0,w0) :: R).length) = G ++ ((v0,w0) :: R) := by
        have h9 := hostM_take_at (G := G) (B := (v0,w0) :: R) (lp := lp)
          (q := ((v0,w0) :: R).length) le_rfl
        rwa [List.take_length] at h9
      rw [htkX, htkM]
    have hMlen : (G ++ ((v0,w0) :: R) ++ [lp]).length
        = G.length + ((v0,w0) :: R).length + 1 := hostM_length ..
    have h9 := (le0_take_iff (m := G.length + ((v0,w0) :: R).length)
      (by omega) (by rw [hXlen]; omega)).2 hle0g
    rw [htkXM] at h9
    exact (le0_take_iff (m := G.length + ((v0,w0) :: R).length)
      (by omega) (by rw [hMlen]; omega)).1 h9
  · have h9 : entry (copyExp G ((v0,w0) :: R) d0 n) 1 a
        = (G.getD a (0,0)).2 := by
      unfold entry
      rw [if_neg one_ne_zero, copyExp_getD_pre hapre]
    omega

/-- **The prefix bound at the root split** (multi-copy, multi-column):
intermediate entries before the last-copy root stay below its level plus
the shift — prefix entries via the host bound, roots by arithmetic,
interiors via the fourth fact or the profile. -/
theorem rootsplit_hbound {G R : PairSeq} {v0 w0 d0 n : ℕ} {lp : ℕ × ℕ}
    (hn2 : 2 ≤ n) (hd0p : 0 < d0) (hlp1 : lp.1 = v0 + d0) (hR : R ≠ [])
    (hdom : ∀ p ∈ R, v0 < p.1)
    (hBF45 : ∀ q, 0 < q → q < ((v0,w0) :: R).length →
      (((v0,w0) :: R).getD q (0,0)).1 + 1 < v0 + 2 * d0)
    (hprof : ∀ a q q', a < q → q < q' → q' < ((v0,w0) :: R).length →
      (((v0,w0) :: R).getD q (0,0)).1 + 1 + (((v0,w0) :: R).getD a (0,0)).1
        < 2 * (((v0,w0) :: R).getD q' (0,0)).1)
    (hpre : ∀ h, h < G.length → (G.getD h (0,0)).1 + 1 < lp.1) :
    ∀ h, h < G.length + (n - 1) * ((v0,w0) :: R).length →
      entry (copyExp G ((v0,w0) :: R) d0 n) 0 h + 1
        < (((v0,w0) :: R).getD (((v0,w0) :: R).length - 1) (0,0)).1
          + (n - 1) * d0 := by
  intro h hh
  have hL2 : 2 ≤ ((v0,w0) :: R).length := by
    rcases R with _ | ⟨r, R'⟩
    · exact absurd rfl hR
    · simp
  have htail_gt : v0 < (((v0,w0) :: R).getD
      (((v0,w0) :: R).length - 1) (0,0)).1 := by
    obtain ⟨q', hq'⟩ : ∃ q', ((v0,w0) :: R).length - 1 = q' + 1 :=
      ⟨((v0,w0) :: R).length - 2, by omega⟩
    rw [hq', List.getD_cons_succ]
    have hmem : R.getD q' (0,0) ∈ R := by
      rw [getD_eq_getElem' _ _ (by
        have h8 : ((v0,w0) :: R).length = R.length + 1 := rfl
        omega)]
      exact List.getElem_mem ..
    exact hdom _ hmem
  by_cases hhg : h < G.length
  · -- prefix entries
    have h9 : entry (copyExp G ((v0,w0) :: R) d0 n) 0 h
        = (G.getD h (0,0)).1 := by
      unfold entry
      rw [if_pos rfl, copyExp_getD_pre hhg]
    have h10 := hpre h hhg
    rw [h9, hlp1] at *
    have h11 : 1 * d0 ≤ (n - 1) * d0 :=
      Nat.mul_le_mul_right d0 (by omega)
    rw [Nat.one_mul] at h11
    omega
  · push Not at hhg
    obtain ⟨kh, qh, hqhL, hdmh⟩ : ∃ kh qh, qh < ((v0,w0) :: R).length ∧
        h - G.length = ((v0,w0) :: R).length * kh + qh :=
      ⟨_, _, Nat.mod_lt _ (by omega),
        (Nat.div_add_mod (h - G.length) ((v0,w0) :: R).length).symm⟩
    have hcmh : ((v0,w0) :: R).length * kh = kh * ((v0,w0) :: R).length :=
      Nat.mul_comm ..
    have hkhn : kh < n - 1 := by
      have h1 : ((v0,w0) :: R).length * kh
          < ((v0,w0) :: R).length * (n - 1) := by
        have hcomm : (n - 1) * ((v0,w0) :: R).length
            = ((v0,w0) :: R).length * (n - 1) := Nat.mul_comm ..
        omega
      exact Nat.lt_of_mul_lt_mul_left h1
    have h9 : entry (copyExp G ((v0,w0) :: R) d0 n) 0 h
        = (((v0,w0) :: R).getD qh (0,0)).1 + kh * d0 := by
      rw [show h = G.length + (kh * ((v0,w0) :: R).length + qh) by omega]
      exact (entry_copyExp (by omega) hqhL).1
    rw [h9]
    -- kh * d0 + d0 ≤ (n-1) * d0
    have hkd : kh * d0 + d0 ≤ (n - 1) * d0 := by
      have h11 : (kh + 1) * d0 ≤ (n - 1) * d0 :=
        Nat.mul_le_mul_right d0 (by omega)
      rw [Nat.add_mul, Nat.one_mul] at h11
      exact h11
    rcases Nat.eq_zero_or_pos qh with hqh0 | hqhpos
    · -- root entries
      rw [hqh0, List.getD_cons_zero]
      show v0 + kh * d0 + 1
          < (((v0,w0) :: R).getD (((v0,w0) :: R).length - 1) (0,0)).1
            + (n - 1) * d0
      omega
    · -- interior entries
      by_cases hcfg : v0 + d0
          ≤ (((v0,w0) :: R).getD (((v0,w0) :: R).length - 1) (0,0)).1
      · have h10 := hBF45 qh hqhpos hqhL
        omega
      · push Not at hcfg
        rcases Nat.eq_or_lt_of_le (by omega : qh ≤ ((v0,w0) :: R).length - 1)
          with he | hlt
        · -- qh is the tail itself: forced d0 ≥ 2 contradiction route
          rw [he]
          have hd02 : 2 ≤ d0 := by omega
          omega
        · have h10 := hprof 0 qh (((v0,w0) :: R).length - 1) (by omega)
            (by omega) (by omega)
          rw [List.getD_cons_zero] at h10
          have h10' : (((v0,w0) :: R).getD qh (0,0)).1 + 1 + v0
              < 2 * (((v0,w0) :: R).getD
                (((v0,w0) :: R).length - 1) (0,0)).1 := h10
          omega

/-- **A one-root triggered block climbs by exactly one**: the last column's
row-0 parent must be the root (a prefix parent's valley would lift the
root to the last column's level), so the climb is `1`. -/
theorem oneroot_d1 {G : PairSeq} {v0 w0 d0 : ℕ} {lp : ℕ × ℕ}
    {M : PairSeq} (hr1 : r1ok M) (hMeq : M = G ++ [(v0,w0)] ++ [lp])
    (hd0p : 0 < d0) (hlp1 : lp.1 = v0 + d0) : d0 = 1 := by
  have hone : ([(v0,w0)] : PairSeq).length = 1 := rfl
  have hMlen : M.length = G.length + 1 + 1 := by
    rw [hMeq]
    have h9 := hostM_length G [(v0,w0)] lp
    rw [hone] at h9
    exact h9
  have hglp : M.getD (M.length - 1) (0,0) = lp := by
    rw [show M.length - 1 = G.length + ([(v0,w0)] : PairSeq).length by
        rw [hone]; omega, hMeq]
    exact hostM_getD_lp
  have hgroot : M.getD G.length (0,0) = (v0, w0) := by
    have h9 := hostM_getD_blk (G := G) (B := [(v0,w0)]) (lp := lp)
      (q := 0) (by rw [hone]; omega)
    rw [Nat.add_zero] at h9
    rw [hMeq, h9, List.getD_cons_zero]
  have hlp1pos : 0 < (M.getD (M.length - 1) (0,0)).1 := by
    rw [hglp]
    omega
  obtain ⟨k, hklt, hklev, hkval, -⟩ := hr1 (M.length - 1) (by omega) hlp1pos
  rw [hglp] at hklev hkval
  rcases Nat.lt_trichotomy k G.length with hk | hk | hk
  · -- prefix parent: the valley lifts the root
    exfalso
    have h9 := hkval G.length hk (by omega)
    rw [hgroot] at h9
    have h9' : lp.1 ≤ v0 := h9
    omega
  · -- the root: climb is one
    rw [hk, hgroot] at hklev
    have hklev' : v0 + 1 = lp.1 := hklev
    omega
  · -- no positions between the root and the last column
    exfalso
    omega

/-- **Row-1 intermediate value along the block descent**: any block column
whose row 1 exceeds the root's admits a root-descendant sitting at exactly
one above the root — the `r1ok` descent changes row 1 by at most one per
step. -/
theorem block_chain_ivp {M G R : PairSeq} {v0 w0 : ℕ} {lp : ℕ × ℕ}
    (hr1 : r1ok M) (hMeq : M = G ++ ((v0,w0) :: R) ++ [lp])
    (hdom : ∀ p ∈ R, v0 < p.1) :
    ∀ q, q < ((v0,w0) :: R).length →
      w0 + 1 ≤ (((v0,w0) :: R).getD q (0,0)).2 →
      ∃ q', q' < ((v0,w0) :: R).length ∧ le0 ((v0,w0) :: R) 0 q' ∧
        (((v0,w0) :: R).getD q' (0,0)).2 = w0 + 1 := by
  have hBR : ((v0,w0) :: R).length = R.length + 1 := rfl
  have hMlen : M.length = G.length + ((v0,w0) :: R).length + 1 := by
    rw [hMeq]
    exact hostM_length ..
  have hgblk : ∀ q, q < ((v0,w0) :: R).length →
      M.getD (G.length + q) (0,0) = ((v0,w0) :: R).getD q (0,0) := by
    intro q hq
    rw [hMeq]
    exact hostM_getD_blk hq
  suffices h : ∀ d q, q < ((v0,w0) :: R).length →
      (((v0,w0) :: R).getD q (0,0)).1 = v0 + d →
      w0 + 1 ≤ (((v0,w0) :: R).getD q (0,0)).2 →
      ∃ q', q' < ((v0,w0) :: R).length ∧ le0 ((v0,w0) :: R) 0 q' ∧
        (((v0,w0) :: R).getD q' (0,0)).2 = w0 + 1 by
    intro q hq ht
    rcases Nat.eq_zero_or_pos q with h0 | hqpos
    · exfalso
      rw [h0, List.getD_cons_zero] at ht
      have ht' : w0 + 1 ≤ w0 := ht
      omega
    · obtain ⟨q'', rfl⟩ : ∃ q'', q = q'' + 1 := ⟨q - 1, by omega⟩
      have hmem : R.getD q'' (0,0) ∈ R := by
        rw [getD_eq_getElem' _ _ (by omega)]
        exact List.getElem_mem ..
      have hv := hdom _ hmem
      refine h ((R.getD q'' (0,0)).1 - v0) (q'' + 1) hq ?_ ht
      rw [List.getD_cons_succ]
      omega
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro q hq hlev ht
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · -- level v0: only the root, whose row 1 is w0 < w0 + 1
      exfalso
      rcases Nat.eq_zero_or_pos q with h0 | hqpos
      · rw [h0, List.getD_cons_zero] at ht
        have ht' : w0 + 1 ≤ w0 := ht
        omega
      · obtain ⟨q'', rfl⟩ : ∃ q'', q = q'' + 1 := ⟨q - 1, by omega⟩
        have hmem : R.getD q'' (0,0) ∈ R := by
          rw [getD_eq_getElem' _ _ (by omega)]
          exact List.getElem_mem ..
        have hv := hdom _ hmem
        rw [List.getD_cons_succ] at hlev
        omega
    · -- positive level: descend one step
      have hqpos : 0 < q := by
        rcases Nat.eq_zero_or_pos q with h0 | hpos
        · exfalso
          rw [h0, List.getD_cons_zero] at hlev
          omega
        · exact hpos
      have hjM : G.length + q < M.length := by omega
      have hpos0 : 0 < (M.getD (G.length + q) (0,0)).1 := by
        rw [hgblk q hq, hlev]
        omega
      obtain ⟨k, hklt, hklev, hkval, hkr1⟩ :=
        hr1 (G.length + q) hjM hpos0
      rw [hgblk q hq, hlev] at hklev hkval
      rw [hgblk q hq] at hkr1
      have hkg : G.length ≤ k := by
        by_contra hkpre
        push Not at hkpre
        have h9 := hkval G.length (by omega) (by omega)
        have hroot : M.getD G.length (0,0) = (v0, w0) := by
          have h10 := hgblk 0 (by omega)
          rw [Nat.add_zero] at h10
          rw [h10, List.getD_cons_zero]
        rw [hroot] at h9
        have h9' : v0 + d ≤ v0 := h9
        omega
      obtain ⟨q', hq'⟩ : ∃ q', k = G.length + q' := ⟨k - G.length, by omega⟩
      have hq'lt : q' < ((v0,w0) :: R).length := by omega
      have hlev' : (((v0,w0) :: R).getD q' (0,0)).1 = v0 + (d - 1) := by
        have h9 := hklev
        rw [hq', hgblk q' hq'lt] at h9
        omega
      have hkr1' : (((v0,w0) :: R).getD q (0,0)).2
          ≤ (((v0,w0) :: R).getD q' (0,0)).2 + 1 := by
        have h9 := hkr1
        rw [hq', hgblk q' hq'lt] at h9
        exact h9
      by_cases hcase : w0 + 1 ≤ (((v0,w0) :: R).getD q' (0,0)).2
      · exact ih (d - 1) (by omega) q' hq'lt hlev' hcase
      · -- the parent is at or below w0: q itself sits at exactly w0 + 1
        push Not at hcase
        refine ⟨q, hq, le0_block_root hr1 hMeq hdom q hq, ?_⟩
        omega

/-- Consecutive roots of a unit-climb one-root expansion chain along
row 0 by adjacent steps. -/
theorem roots_chain {G : PairSeq} {v0 w0 n : ℕ} :
    ∀ k', k' < n → ∀ k, k ≤ k' →
      Relation.ReflTransGen (nextrel0 (copyExp G [(v0,w0)] 1 n))
        (G.length + k) (G.length + k') := by
  have hone : ([(v0,w0)] : PairSeq).length = 1 := rfl
  have hXlen : (copyExp G [(v0,w0)] 1 n).length = G.length + n * 1 := by
    rw [← hone]
    exact copyExp_length ..
  have hent : ∀ k, k < n →
      entry (copyExp G [(v0,w0)] 1 n) 0 (G.length + k) = v0 + k := by
    intro k hk
    have h9 : entry (copyExp G [(v0,w0)] 1 n) 0
        (G.length + (k * ([(v0,w0)] : PairSeq).length + 0))
        = (([(v0,w0)] : PairSeq).getD 0 (0,0)).1 + k * 1 :=
      (entry_copyExp hk (by rw [hone]; omega)).1
    rw [show G.length + (k * ([(v0,w0)] : PairSeq).length + 0)
          = G.length + k by rw [hone]; omega] at h9
    rw [h9, List.getD_cons_zero]
    show (v0, w0).1 + k * 1 = v0 + k
    omega
  intro k'
  induction k' with
  | zero =>
    intro _ k hk
    have : k = 0 := by omega
    rw [this]
  | succ k' ih =>
    intro hk'n k hk
    rcases Nat.eq_or_lt_of_le hk with he | hlt
    · rw [he]
    · refine (ih (by omega) k (by omega)).tail ?_
      refine ⟨by rw [hXlen]; omega, by rw [hXlen]; omega, by omega,
        ?_, ?_⟩
      · rw [hent k' (by omega), hent (k' + 1) (by omega)]
        omega
      · intro l hl
        exfalso
        omega

/-- **The edge dichotomy** (mined exact, 28054/28054): below any row-1
edge, every row-0 descendant of its source with positive row 1 either
reaches the target along row 0 or equals it. -/
def dichOK (M : PairSeq) : Prop :=
  ∀ p q t, nextrel1 M p t → le0 M p q → q < t →
    0 < (M.getD q (0,0)).2 →
    le0 M q t ∨ M.getD q (0,0) = M.getD t (0,0)

/-- On the diagonal every pair below the bound is row-0 connected, so the
dichotomy holds by the left branch. -/
theorem dichOK_diagSeq (v : ℕ) : dichOK (diagSeq 0 v) := by
  intro p q t hnx hpq hqt hpos
  left
  have htlen := hnx.2.1
  rw [diagSeq0_length] at htlen
  exact le0_diagSeq (le_of_lt hqt) (by omega)

/-- The dichotomy restricts to truncations. -/
theorem dichOK_take {M : PairSeq} (h : dichOK M) (m : ℕ) :
    dichOK (M.take m) := by
  intro p q t hnx hpq hqt hpos
  have htm : t < m := by
    have := hnx.2.1
    rw [List.length_take] at this
    omega
  have htM : t < M.length := by
    have := hnx.2.1
    rw [List.length_take] at this
    omega
  have hnx' : nextrel1 M p t := (nextrel1_take_iff htm htM).1 hnx
  have hqm : q < m := by omega
  have hqM : q < M.length := by omega
  have hpq' : le0 M p q := (le0_take_iff hqm hqM).1 hpq
  rw [getD_take hqm] at hpos
  rcases h p q t hnx' hpq' hqt hpos with h9 | h9
  · exact Or.inl ((le0_take_iff htm htM).2 h9)
  · right
    rw [getD_take hqm, getD_take htm]
    exact h9

theorem dichOK_Pred {M : PairSeq} (h : dichOK M) : dichOK (Pred M) := by
  unfold Pred
  by_cases hl : M.length ≤ 1
  · rw [if_pos hl]
    exact h
  · rw [if_neg hl, List.dropLast_eq_take]
    exact dichOK_take h _

/-- The copy obligation for the edge dichotomy. -/
def copyDichOK (M : PairSeq) (n : ℕ) : Prop :=
  ∀ G v0 w0 (R : PairSeq) (lp : ℕ × ℕ) d0,
    M = G ++ ((v0,w0) :: R) ++ [lp] →
    M⟦n⟧ = copyExp G ((v0,w0) :: R) d0 n →
    (∀ p ∈ R, v0 < p.1) →
    nextR M (idx1 M (M.length - 1)) G.length (M.length - 1) →
    ((d0 = 0 ∧ idx1 M (M.length - 1) = 0) ∨ (0 < d0 ∧ w0 < lp.2 ∧
      lp.1 = v0 + d0 ∧ nextrel1 M G.length (M.length - 1))) →
    dichOK (M⟦n⟧)

/-- **The edge dichotomy along the standard closure**, modulo the copy
obligation: the truncation branches are unconditional. -/
theorem dichOK_ST_PS {M : PairSeq} (hM : ST_PS M)
    (hbad : ∀ N k, ST_PS N → dichOK N → 1 ≤ k → copyDichOK N k) : dichOK M := by
  induction hM with
  | diag v => exact dichOK_diagSeq v
  | @oper N k hN hk ih =>
    by_cases hL0 : N.length - 1 = 0
    · rw [oper_eq_self_of_short k hL0]
      exact ih
    by_cases hz : entry N 0 (N.length - 1) = 0 ∧ entry N 1 (N.length - 1) = 0
    · rw [oper_eq_pred_of_zero k hL0 hz]
      exact dichOK_Pred ih
    by_cases hp : hasParent N (idx1 N (N.length - 1)) (N.length - 1)
    case neg =>
      rw [oper_eq_pred_of_noParent k hL0 hz hp]
      exact dichOK_Pred ih
    case pos =>
      obtain ⟨G, v0, w0, R, d0, lp, hMeq, hX, hdom, -, hd0, hnxt⟩ :=
        oper_bad_blocks (by omega) hz hp hk
      exact hbad N k hN ih hk G v0 w0 R lp d0 hMeq hX hdom hnxt hd0

/-- The edge dichotomy transfers through a shared prefix. -/
theorem dichOK_of_take_eq {X Y : PairSeq} {m : ℕ}
    (hXY : X.take m = Y.take m) (hY : dichOK Y) :
    ∀ p q t, t < m → t < X.length → t < Y.length →
      nextrel1 X p t → le0 X p q → q < t → 0 < (X.getD q (0,0)).2 →
      le0 X q t ∨ X.getD q (0,0) = X.getD t (0,0) := by
  intro p q t htm htX htY hnx hpq hqt hpos
  have hgd : ∀ j, j < m → j < X.length → X.getD j (0,0) = Y.getD j (0,0) := by
    intro j hj hjX
    have h1 : (X.take m).getD j (0,0) = X.getD j (0,0) := getD_take hj
    have h2 : (Y.take m).getD j (0,0) = Y.getD j (0,0) := getD_take hj
    rw [← h1, hXY, h2]
  have hnx' : nextrel1 Y p t := by
    have h1 : nextrel1 (X.take m) p t := (nextrel1_take_iff htm htX).2 hnx
    rw [hXY] at h1
    exact (nextrel1_take_iff htm htY).1 h1
  have hpq' : le0 Y p q := by
    have h1 : le0 (X.take m) p q := (le0_take_iff (by omega) (by omega)).2 hpq
    rw [hXY] at h1
    exact (le0_take_iff (by omega) (by omega)).1 h1
  have hpos' : 0 < (Y.getD q (0,0)).2 := by
    rw [← hgd q (by omega) (by omega)]
    exact hpos
  rcases hY p q t hnx' hpq' hqt hpos' with h9 | h9
  · left
    have h1 : le0 (Y.take m) q t := (le0_take_iff htm htY).2 h9
    rw [← hXY] at h1
    exact (le0_take_iff htm htX).1 h1
  · right
    rw [hgd q (by omega) (by omega), hgd t htm htX]
    exact h9

/-- The edge dichotomy transfers to any window given by a drop of a
shared-prefix region: relations localize to the window. -/
theorem dichOK_window {X Y : PairSeq} {s sY m : ℕ}
    (hwin : ∀ w, w ≤ m → (X.drop s).take w = (Y.drop sY).take w)
    (hY : dichOK Y)
    (hmX : s + m ≤ X.length) (hmY : sY + m ≤ Y.length) :
    ∀ p q t, t < m →
      nextrel1 X (s + p) (s + t) → le0 X (s + p) (s + q) → q < t →
      0 < (X.getD (s + q) (0,0)).2 →
      le0 X (s + q) (s + t) ∨ X.getD (s + q) (0,0) = X.getD (s + t) (0,0) := by
  intro p q t htm hnx hpq hqt hpos
  -- localize to the X-window
  have hW := hwin m le_rfl
  have hXlen : m ≤ (X.drop s).length := by
    rw [List.length_drop]
    omega
  have hYlen : m ≤ (Y.drop sY).length := by
    rw [List.length_drop]
    omega
  -- getD correspondence
  have hgd : ∀ j, j < m →
      X.getD (s + j) (0,0) = Y.getD (sY + j) (0,0) := by
    intro j hj
    have h1 : (X.drop s).getD j (0,0) = ((X.drop s).take m).getD j (0,0) :=
      (getD_take hj).symm
    have h2 : ((Y.drop sY).take m).getD j (0,0)
        = (Y.drop sY).getD j (0,0) := getD_take hj
    have h3 := getD_drop (L := X) (n := s) (i := j) ((0,0) : ℕ × ℕ)
    have h4 := getD_drop (L := Y) (n := sY) (i := j) ((0,0) : ℕ × ℕ)
    rw [← h3, h1, hW, h2, h4]
  -- relations through the window: X-side down
  have hnx1 : nextrel1 (X.drop s) p t := by
    have h9 := (nextrel1_drop_iff (M := X) (k := s) (a := s + p)
      (b := s + t) (by omega) (by omega) (by omega)).2 hnx
    rwa [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left] at h9
  have hpq1 : le0 (X.drop s) p q := by
    have h9 := (le0_drop_iff (M := X) (k := s) (a := s + p)
      (b := s + q) (by omega) (by omega) (by omega)).2 hpq
    rwa [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left] at h9
  -- into the take, across, and up on the Y side
  have hnx2 : nextrel1 (Y.drop sY) p t := by
    have h9 : nextrel1 ((X.drop s).take m) p t :=
      (nextrel1_take_iff htm (by omega)).2 hnx1
    rw [hW] at h9
    exact (nextrel1_take_iff htm (by omega)).1 h9
  have hpq2 : le0 (Y.drop sY) p q := by
    have h9 : le0 ((X.drop s).take m) p q :=
      (le0_take_iff (m := m) (by omega) (by omega)).2 hpq1
    rw [hW] at h9
    exact (le0_take_iff (m := m) (by omega) (by omega)).1 h9
  have hnxY : nextrel1 Y (sY + p) (sY + t) := by
    have h9 := (nextrel1_drop_iff (M := Y) (k := sY) (a := sY + p)
      (b := sY + t) (by omega) (by omega) (by omega)).1
    rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left] at h9
    exact h9 hnx2
  have hpqY : le0 Y (sY + p) (sY + q) := by
    have h9 := (le0_drop_iff (M := Y) (k := sY) (a := sY + p)
      (b := sY + q) (by omega) (by omega) (by omega)).1
    rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left] at h9
    exact h9 hpq2
  have hposY : 0 < (Y.getD (sY + q) (0,0)).2 := by
    rw [← hgd q (by omega)]
    exact hpos
  rcases hY (sY + p) (sY + q) (sY + t) hnxY hpqY (by omega) hposY
    with h9 | h9
  · -- back down and across
    left
    have h10 := (le0_drop_iff (M := Y) (k := sY) (a := sY + q)
      (b := sY + t) (by omega) (by omega) (by omega)).2 h9
    rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left] at h10
    have h11 : le0 ((Y.drop sY).take m) q t :=
      (le0_take_iff htm (by omega)).2 h10
    rw [← hW] at h11
    have h12 : le0 (X.drop s) q t :=
      (le0_take_iff htm (by omega)).1 h11
    have h13 := (le0_drop_iff (M := X) (k := s) (a := s + q)
      (b := s + t) (by omega) (by omega) (by omega)).1
    rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left] at h13
    exact h13 h12
  · right
    rw [hgd q (by omega), hgd t htm]
    exact h9

/-- The edge dichotomy restricts to suffixes. -/
theorem dichOK_drop {M : PairSeq} (h : dichOK M) (k : ℕ) :
    dichOK (M.drop k) := by
  intro p q t hnx hpq hqt hpos
  have htM : k + t < M.length := by
    have h9 := hnx.2.1
    rw [List.length_drop] at h9
    omega
  have hnx' : nextrel1 M (k + p) (k + t) := by
    have h9 := (nextrel1_drop_iff (M := M) (k := k) (a := k + p)
      (b := k + t) (by omega) (by omega) (by omega)).1
    rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left] at h9
    exact h9 hnx
  have hpq' : le0 M (k + p) (k + q) := by
    have h9 := (le0_drop_iff (M := M) (k := k) (a := k + p)
      (b := k + q) (by omega) (by omega) (by omega)).1
    rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left] at h9
    exact h9 hpq
  have hpos' : 0 < (M.getD (k + q) (0,0)).2 := by
    rw [← getD_drop (L := M) (n := k) (i := q) ((0,0) : ℕ × ℕ)]
    exact hpos
  rcases h (k + p) (k + q) (k + t) hnx' hpq' (by omega) hpos' with h9 | h9
  · left
    have h10 := (le0_drop_iff (M := M) (k := k) (a := k + q)
      (b := k + t) (by omega) (by omega) (by omega)).2 h9
    rwa [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left] at h10
  · right
    rw [getD_drop, getD_drop]
    exact h9

/-- The edge dichotomy is shift-invariant. -/
theorem dichOK_shift {B : PairSeq} {d : ℕ} (h : dichOK B) :
    dichOK (B.map fun p => (p.1 + d, p.2)) := by
  intro p q t hnx hpq hqt hpos
  have htB : t < B.length := by
    have h9 := hnx.2.1
    rw [List.length_map] at h9
    exact h9
  have hgd : ∀ j, j < B.length →
      (B.map fun p => (p.1 + d, p.2)).getD j (0,0)
        = ((B.getD j (0,0)).1 + d, (B.getD j (0,0)).2) := by
    intro j hj
    rw [getD_eq_getElem' _ _ (by rw [List.length_map]; omega),
        List.getElem_map, ← getD_eq_getElem' _ (0,0) hj]
  have hnx' : nextrel1 B p t := (nextrel1_shift_iff htB).1 hnx
  have hpq' : le0 B p q := (le0_shift_iff).1 hpq
  have hqB : q < B.length := by omega
  have hpos' : 0 < (B.getD q (0,0)).2 := by
    rw [hgd q hqB] at hpos
    exact hpos
  rcases h p q t hnx' hpq' hqt hpos' with h9 | h9
  · exact Or.inl ((le0_shift_iff).2 h9)
  · right
    rw [hgd q hqB, hgd t htB, h9]

/-- The `k`-th copy window of the expansion is the shifted block. -/
theorem copyExp_copy_window {G B : PairSeq} {d0 n k : ℕ} (hk : k < n) :
    ∀ w, w ≤ B.length →
      ((copyExp G B d0 n).drop (G.length + k * B.length)).take w
        = ((B.map fun p => (p.1 + k * d0, p.2)).drop 0).take w := by
  intro w hw
  rw [List.drop_zero]
  have hsplit := copyExp_split G B d0 (le_of_lt hk)
  obtain ⟨m, hm⟩ : ∃ m, n - k = m + 1 := ⟨n - k - 1, by omega⟩
  rw [hm, List.range_succ_eq_map, List.flatMap_cons] at hsplit
  simp only [Nat.add_zero] at hsplit
  have hdrop : (copyExp G B d0 n).drop (G.length + k * B.length)
      = (B.map fun p => (p.1 + k * d0, p.2))
        ++ ((List.map Nat.succ (List.range m)).flatMap
            fun i => B.map fun p => (p.1 + (k + i) * d0, p.2)) := by
    conv_lhs => rw [hsplit]
    rw [show G.length + k * B.length = (copyExp G B d0 k).length from
          (copyExp_length ..).symm,
        List.drop_left]
  rw [hdrop, List.take_append_of_le_length (by rw [List.length_map]; omega)]

/-- **The same-copy instances of the copy dichotomy**: edges inside one
copy inherit the host block's dichotomy through the window, the shift and
the infix closures. -/
theorem dichOK_copy {G B : PairSeq} {d0 n k : ℕ} {lp : ℕ × ℕ}
    {M : PairSeq} (hM : dichOK M) (hMeq : M = G ++ B ++ [lp])
    (hk : k < n) :
    ∀ p q t, t < B.length →
      nextrel1 (copyExp G B d0 n) (G.length + k * B.length + p)
        (G.length + k * B.length + t) →
      le0 (copyExp G B d0 n) (G.length + k * B.length + p)
        (G.length + k * B.length + q) →
      q < t →
      0 < ((copyExp G B d0 n).getD (G.length + k * B.length + q) (0,0)).2 →
      le0 (copyExp G B d0 n) (G.length + k * B.length + q)
        (G.length + k * B.length + t)
      ∨ (copyExp G B d0 n).getD (G.length + k * B.length + q) (0,0)
        = (copyExp G B d0 n).getD (G.length + k * B.length + t) (0,0) := by
  intro p q t htm hnx hpq hqt hpos
  -- the block inherits the dichotomy, then shifts
  have hB : dichOK B := by
    have h1 : dichOK (M.drop G.length) := dichOK_drop hM G.length
    have h2 : M.drop G.length = B ++ [lp] := by
      rw [hMeq, List.append_assoc, List.drop_left]
    rw [h2] at h1
    have h3 : dichOK ((B ++ [lp]).take B.length) := dichOK_take h1 _
    have h4 : (B ++ [lp]).take B.length = B :=
      List.take_left' rfl
    rwa [h4] at h3
  have hBs : dichOK (B.map fun p => (p.1 + k * d0, p.2)) := dichOK_shift hB
  have hXlen : (copyExp G B d0 n).length = G.length + n * B.length :=
    copyExp_length ..
  have hnL : (k + 1) * B.length ≤ n * B.length :=
    Nat.mul_le_mul_right B.length (by omega)
  have hk1 : (k + 1) * B.length = k * B.length + B.length := by
    rw [Nat.add_mul, Nat.one_mul]
  exact dichOK_window (X := copyExp G B d0 n)
    (Y := B.map fun x => (x.1 + k * d0, x.2))
    (s := G.length + k * B.length) (sY := 0) (m := B.length)
    (copyExp_copy_window hk) hBs
    (by omega) (by rw [List.length_map]; omega) p q t htm hnx hpq hqt hpos

/-- **The prefix instances of the copy dichotomy** transfer through the
shared base. -/
theorem dichOK_pre {G B : PairSeq} {lp : ℕ × ℕ} {d0 n : ℕ} {M : PairSeq}
    (hM : dichOK M) (hMeq : M = G ++ B ++ [lp]) (hn : 1 ≤ n)
    (hB1 : 1 ≤ B.length) :
    ∀ p q t, t < G.length →
      nextrel1 (copyExp G B d0 n) p t →
      le0 (copyExp G B d0 n) p q → q < t →
      0 < ((copyExp G B d0 n).getD q (0,0)).2 →
      le0 (copyExp G B d0 n) q t
      ∨ (copyExp G B d0 n).getD q (0,0)
        = (copyExp G B d0 n).getD t (0,0) := by
  have htkXM : (copyExp G B d0 n).take (G.length + B.length)
      = M.take (G.length + B.length) := by
    have htkX : (copyExp G B d0 n).take (G.length + B.length)
        = G ++ B := by
      have h9 := copyExp_take_at (G := G) (B := B) (d0 := d0)
        (n := n) (k := 0) (q := B.length) (by omega) le_rfl
      simpa [copyExp] using h9
    have htkM : M.take (G.length + B.length) = G ++ B := by
      rw [hMeq]
      have h9 := hostM_take_at (G := G) (B := B) (lp := lp)
        (q := B.length) le_rfl
      rwa [List.take_length] at h9
    rw [htkX, htkM]
  have hXlen : (copyExp G B d0 n).length = G.length + n * B.length :=
    copyExp_length ..
  have hMlen : M.length = G.length + B.length + 1 := by
    rw [hMeq]
    exact hostM_length ..
  intro p q t ht hnx hpq hqt hpos
  exact dichOK_of_take_eq htkXM hM p q t (by omega)
    (by rw [hXlen]; have := Nat.mul_le_mul_right B.length hn; omega)
    (by omega) hnx hpq hqt hpos

theorem le0_trans {M : PairSeq} {a b c : ℕ}
    (h1 : le0 M a b) (h2 : le0 M b c) : le0 M a c :=
  ⟨h1.1, h2.2.1, h1.2.2.trans h2.2.2⟩

theorem le0_roots {G : PairSeq} {v0 w0 n k k' : ℕ}
    (hk' : k' < n) (hk : k ≤ k') :
    le0 (copyExp G [(v0,w0)] 1 n) (G.length + k) (G.length + k') := by
  have hone : ([(v0,w0)] : PairSeq).length = 1 := rfl
  have hXlen : (copyExp G [(v0,w0)] 1 n).length = G.length + n * 1 := by
    rw [← hone]
    exact copyExp_length ..
  exact ⟨by rw [hXlen]; omega, by rw [hXlen]; omega,
    roots_chain k' hk' k hk⟩

/-- Adjacent chains along any unit staircase window. -/
theorem rtg_stair {M : PairSeq} {s e : ℕ} (he : e < M.length)
    (hstair : ∀ j, s ≤ j → j < e → entry M 0 (j + 1) = entry M 0 j + 1) :
    ∀ b, b ≤ e → ∀ a, s ≤ a → a ≤ b →
      Relation.ReflTransGen (nextrel0 M) a b := by
  intro b
  induction b with
  | zero =>
    intro _ a _ ha
    have : a = 0 := by omega
    rw [this]
  | succ b ih =>
    intro hbe a hsa hab
    rcases Nat.eq_or_lt_of_le hab with hEq | hlt
    · rw [hEq]
    · refine (ih (by omega) a hsa (by omega)).tail ?_
      refine ⟨by omega, by omega, by omega, ?_, ?_⟩
      · rw [hstair b (by omega) (by omega)]
        omega
      · intro l hl
        exfalso
        omega

theorem le0_stair {M : PairSeq} {s e a b : ℕ} (he : e < M.length)
    (hstair : ∀ j, s ≤ j → j < e → entry M 0 (j + 1) = entry M 0 j + 1)
    (hsa : s ≤ a) (hab : a ≤ b) (hbe : b ≤ e) :
    le0 M a b :=
  ⟨by omega, by omega, rtg_stair he hstair b hbe a hsa hab⟩

/-- Over a staircase window, the parent-edge maximality pins every later
row 1 strictly above the split head's. -/
theorem split_row1_of_stair {X : PairSeq} {gX last : ℕ}
    (hedge : nextrel1 X gX last) (hlast : last < X.length)
    (hstair : ∀ j, gX ≤ j → j < last →
      entry X 0 (j + 1) = entry X 0 j + 1) :
    ∀ j, gX < j → j ≤ last → entry X 1 gX < entry X 1 j :=
  split_row1_strict hedge
    (fun j hj1 hj2 =>
      le0_stair hlast hstair (by omega) (by omega) (by omega))

/-- **The dichotomy pins row 1 above any edge source**: descendants of the
source with positive row 1 sit strictly above it — by the maximality
clause in the bridge case and by the target equality in the tie case. -/
theorem row1_gt_of_dichOK {X : PairSeq} {p t : ℕ}
    (hdich : dichOK X) (hedge : nextrel1 X p t) :
    ∀ q, p < q → le0 X p q → q < t → 0 < (X.getD q (0,0)).2 →
      (X.getD p (0,0)).2 < (X.getD q (0,0)).2 := by
  intro q hpq0 hpq hqt hpos
  have hC1 : (X.getD p (0,0)).2 < (X.getD t (0,0)).2 := by
    have h9 := hedge.2.2.2.1
    unfold entry at h9
    rw [if_neg one_ne_zero, if_neg one_ne_zero] at h9
    exact h9
  rcases hdich p q t hedge hpq hqt hpos with h9 | h9
  · have hmax := hedge.2.2.2.2.2 q ⟨hpq0, h9⟩
    unfold entry at hmax
    rw [if_neg one_ne_zero, if_neg one_ne_zero] at hmax
    omega
  · rw [h9]
    exact hC1

/-- **Retarget the final step of a row-0 chain forward** to a column with the
same row-0 entry, provided the closed interval `[ρ, b)` stays at or above that
level (so the last hop's between-condition still holds). -/
theorem le0_retarget {M : PairSeq} {a ρ b : ℕ}
    (h : le0 M a ρ) (haρ : a < ρ) (hρb : ρ < b) (hb : b < M.length)
    (heq : entry M 0 ρ = entry M 0 b)
    (hval : ∀ y, ρ ≤ y → y < b → entry M 0 b ≤ entry M 0 y) :
    le0 M a b := by
  obtain ⟨ha, hρ, hch⟩ := h
  refine ⟨ha, hb, ?_⟩
  rcases hch.cases_tail with he | ⟨x, hax, hxρ⟩
  · exfalso
    omega
  · refine hax.tail ?_
    obtain ⟨hx1, -, hx3, hx4, hx5⟩ := hxρ
    refine ⟨hx1, hb, by omega, by omega, ?_⟩
    intro j hj
    by_cases hjρ : j < ρ
    · have h9 := hx5 j ⟨hj.1, hjρ⟩
      omega
    · exact hval j (by omega) hj.2

/-- **Shorten a row-0 chain backward** to an interior column with the same
row-0 entry, when the open interval `(ρ, b)` stays at or above that level
(forcing the final step's source to lie below `ρ`). -/
theorem le0_shorten {M : PairSeq} {a ρ b : ℕ}
    (h : le0 M a b) (haρ : a ≤ ρ) (hρb : ρ < b) (hρ : ρ < M.length)
    (heq : entry M 0 ρ = entry M 0 b)
    (hval : ∀ y, ρ < y → y < b → entry M 0 b ≤ entry M 0 y) :
    le0 M a ρ := by
  obtain ⟨ha, hb, hch⟩ := h
  refine ⟨ha, hρ, ?_⟩
  rcases Nat.eq_or_lt_of_le haρ with he | hlt
  · rw [he]
  · rcases hch.cases_tail with he2 | ⟨x, hax, hxb⟩
    · exfalso
      omega
    · obtain ⟨hx1, -, hx3, hx4, hx5⟩ := hxb
      have hxρ : x < ρ := by
        by_contra hge
        push Not at hge
        rcases Nat.eq_or_lt_of_le hge with hEq | hlt2
        · rw [← hEq] at hx4
          omega
        · have h9 := hval x hlt2 hx3
          omega
      refine hax.tail ?_
      refine ⟨hx1, hρ, hxρ, by omega, ?_⟩
      intro j hj
      have h9 := hx5 j ⟨hj.1, by omega⟩
      omega

/-- **The copy-`k'` root is a strict row-0 pivot** over every later position
of the expansion (`0 < d0`): later copies sit at strictly higher levels and
the copy's own interior columns are strictly dominated. -/
theorem copyExp_root_pivot {G : PairSeq} {v0 w0 d0 n k' : ℕ} {R : PairSeq}
    (hd0 : 0 < d0) (hdom : ∀ x ∈ R, v0 < x.1) (hk' : k' < n) :
    ∀ y, G.length + k' * ((v0,w0)::R).length < y →
      y < (copyExp G ((v0,w0)::R) d0 n).length →
      v0 + k' * d0 < entry (copyExp G ((v0,w0)::R) d0 n) 0 y := by
  intro y hy1 hy2
  set B : PairSeq := (v0,w0)::R with hBdef
  have hL : 0 < B.length := by rw [hBdef]; simp
  have hXlen : (copyExp G B d0 n).length = G.length + n * B.length :=
    copyExp_length ..
  rw [hXlen] at hy2
  have hyg : G.length ≤ y := by
    have : G.length ≤ G.length + k' * B.length := Nat.le_add_right _ _
    omega
  obtain ⟨k, q, hk, hq, hyeq⟩ :=
    index_decomp hL (show y - G.length < n * B.length by omega)
  have hye : y = G.length + (k * B.length + q) := by omega
  rw [hye, (entry_copyExp hk hq).1]
  have hpos : k' * B.length < k * B.length + q := by omega
  have hBq : v0 ≤ (B.getD q (0,0)).1 := by
    rcases Nat.eq_zero_or_pos q with hq0 | hqp
    · rw [hq0, hBdef, List.getD_cons_zero]
    · obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      have hq'R : q' < R.length := by
        have := hq; rw [hBdef] at this; simp at this; omega
      rw [hBdef, List.getD_cons_succ]
      exact le_of_lt (hdom _ (getD_mem hq'R))
  rcases Nat.lt_trichotomy k k' with hkk | hkk | hkk
  · exfalso
    have hk1 : (k + 1) * B.length = k * B.length + B.length := by
      rw [Nat.add_mul, Nat.one_mul]
    have h2 : (k + 1) * B.length ≤ k' * B.length :=
      Nat.mul_le_mul_right B.length (by omega)
    omega
  · subst hkk
    have hqp : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h0 | h0
      · exfalso; rw [h0] at hpos; omega
      · exact h0
    have hBqs : v0 < (B.getD q (0,0)).1 := by
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      have hq'R : q' < R.length := by
        have := hq; rw [hBdef] at this; simp at this; omega
      rw [hBdef, List.getD_cons_succ]
      exact hdom _ (getD_mem hq'R)
    omega
  · have h3 : (k' + 1) * d0 = k' * d0 + d0 := by rw [Nat.add_mul, Nat.one_mul]
    have h2 : (k' + 1) * d0 ≤ k * d0 := Nat.mul_le_mul_right d0 (by omega)
    omega

/-- **The copy-`k'` root pivots over its own interior** with no `d0`
hypothesis — needed for the `d0 = 0` branch, where later copy roots tie. -/
theorem copyExp_root_pivot_local {G : PairSeq} {v0 w0 d0 n k' : ℕ} {R : PairSeq}
    (hdom : ∀ x ∈ R, v0 < x.1) (hk' : k' < n) :
    ∀ q, 0 < q → q < ((v0,w0)::R).length →
      v0 + k' * d0 <
        entry (copyExp G ((v0,w0)::R) d0 n) 0
          (G.length + (k' * ((v0,w0)::R).length + q)) := by
  intro q hqp hq
  set B : PairSeq := (v0,w0)::R with hBdef
  rw [(entry_copyExp hk' hq).1]
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  have hq'R : q' < R.length := by
    have := hq; rw [hBdef] at this; simp at this; omega
  rw [hBdef, List.getD_cons_succ]
  have := hdom _ (getD_mem hq'R)
  omega

end YAPSS
