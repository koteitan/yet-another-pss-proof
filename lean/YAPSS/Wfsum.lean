/-
Sum-layer reduction.  Lean port of `wfsum.thy`.

Within-level WF reduces to argument-level WF via the multiset extension
(Dershowitz–Manna), as in the PrSS proof.  An `NF` term is a non-increasing
sum `p₀(b₁)+…+p₀(bₖ)` (head subscript `0` by `inv2`, sibling subscripts `≤ 0`
by `cnf_tops_le`, non-increasing by `cnf`); on such sums `<o` is lex on the
argument lists, which embeds into the multiset extension of the argument
order.

Port note: Isabelle's `mult` (transitive closure of one-step) is replaced by
the one-step Dershowitz–Manna order `DMLT` (Mathlib's `IsDershowitzMannaLT`,
made parametric in the relation via a local `Preorder` instance); for a
transitive relation the two have the same well-founded parts, and every use
here exhibits a one-step witness anyway.

`wf_ArgsA` (the Buchholz-collapse core) is the sole `sorry`, exactly as in
the Isabelle source — that route is frozen there in favour of the value
normalisation `nrm` (see `task.md`).
-/
import YAPSS.Wf
import Mathlib.Data.Multiset.DershowitzManna

namespace YAPSS

open Three

/-! ## A parametric Dershowitz–Manna order -/

/-- One-step Dershowitz–Manna order over an arbitrary relation `r`
(definitionally `Multiset.IsDershowitzMannaLT` with `· < ·` replaced by
`r`). -/
def DMLT {α : Type*} (r : α → α → Prop) (M N : Multiset α) : Prop :=
  ∃ X Y Z, Z ≠ ∅ ∧ M = X + Y ∧ N = X + Z ∧ ∀ y ∈ Y, ∃ z ∈ Z, r y z

theorem DMLT.mono {α : Type*} {r r' : α → α → Prop} (h : ∀ a b, r a b → r' a b)
    {M N : Multiset α} (hMN : DMLT r M N) : DMLT r' M N := by
  obtain ⟨X, Y, Z, hZ, hM, hN, hYZ⟩ := hMN
  exact ⟨X, Y, Z, hZ, hM, hN, fun y hy =>
    let ⟨z, hz, hr⟩ := hYZ y hy
    ⟨z, hz, h y z hr⟩⟩

/-- A transitive well-founded relation has a well-founded Dershowitz–Manna
extension. -/
theorem wellFounded_dmlt {α : Type*} {r : α → α → Prop}
    (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c) (hwf : WellFounded r) :
    WellFounded (DMLT r) := by
  have hirr : ∀ a, ¬ r a a := by
    intro a
    induction hwf.apply a with
    | intro x _ ih => exact fun hxx => ih x hxx hxx
  have hasymm : ∀ a b, r a b → ¬ r b a := fun a b hab hba =>
    hirr a (htrans hab hba)
  letI : Preorder α :=
    { le := fun a b => r a b ∨ a = b
      lt := r
      le_refl := fun _ => Or.inr rfl
      le_trans := by
        rintro a b c (hab | rfl) (hbc | rfl)
        · exact Or.inl (htrans hab hbc)
        · exact Or.inl hab
        · exact Or.inl hbc
        · exact Or.inr rfl
      lt_iff_le_not_ge := by
        intro a b
        constructor
        · intro h
          refine ⟨Or.inl h, ?_⟩
          rintro (hba | rfl)
          · exact hasymm a b h hba
          · exact hirr _ h
        · rintro ⟨hab | rfl, hnb⟩
          · exact hab
          · exact absurd (Or.inr rfl) hnb }
  letI : WellFoundedLT α := ⟨hwf⟩
  exact Multiset.wellFounded_isDershowitzMannaLT

/-- Accessibility passes through the (parametric) multiset extension: a
multiset of `r`-accessible elements is `DMLT r`-accessible, even when `r` is
not globally well-founded.  (Isabelle's `accp_multp_olt0`, generalised.) -/
theorem acc_dmlt_of_acc {α : Type*} {r : α → α → Prop} (htrans : ∀ ⦃a b c⦄, r a b → r b c → r a c)
    {M : Multiset α} (hM : ∀ x ∈ M, Acc r x) : Acc (DMLT r) M := by
  set rA : α → α → Prop := fun x y => r x y ∧ Acc r x with hrA
  have htransA : ∀ ⦃a b c⦄, rA a b → rA b c → rA a c := fun _ _ _ hab hbc => ⟨htrans hab.1 hbc.1, hab.2⟩
  have hwfA : WellFounded rA := by
    have transfer : ∀ z, Acc r z → Acc rA z := fun z hz =>
      hz.rec fun z _ ih => Acc.intro z fun w hw => ih w hw.1
    exact ⟨fun x => Acc.intro x fun y hy => transfer y hy.2⟩
  have aux : ∀ M, Acc (DMLT rA) M → (∀ x ∈ M, Acc r x) → Acc (DMLT r) M := by
    intro M hacc
    induction hacc with
    | intro M _ ih =>
      intro hMacc
      refine Acc.intro M fun N hN => ?_
      obtain ⟨X, Y, Z, hZ, hNXY, hMXZ, hYZ⟩ := hN
      have accN : ∀ x ∈ N, Acc r x := by
        intro x hx
        rw [hNXY] at hx
        rcases Multiset.mem_add.1 hx with hx | hx
        · exact hMacc x (by rw [hMXZ]; exact Multiset.mem_add.2 (Or.inl hx))
        · obtain ⟨z, hz, hrz⟩ := hYZ x hx
          exact (hMacc z (by rw [hMXZ]; exact Multiset.mem_add.2 (Or.inr hz))).inv hrz
      have hNA : DMLT rA N M :=
        ⟨X, Y, Z, hZ, hNXY, hMXZ, fun y hy =>
          let ⟨z, hz, hrz⟩ := hYZ y hy
          ⟨z, hz, hrz, accN y (by rw [hNXY]; exact Multiset.mem_add.2 (Or.inr hy))⟩⟩
      exact ih N hNA accN
  exact aux M ((wellFounded_dmlt htransA hwfA).apply M) hM

/-! ## Sum arguments and summands -/

/-- The list of arguments along the sum chain. -/
def sargs : Three → List Three
  | Z => []
  | P _ b c => b :: sargs c

@[simp] theorem sargs_Z : sargs Z = [] := rfl
@[simp] theorem sargs_P (a : ℕ) (b c : Three) : sargs (P a b c) = b :: sargs c := rfl

/-- The argument multiset of a sum. -/
def margs (x : Three) : Multiset Three := ↑(sargs x)

/-- The order restricted to a class `A` (Isabelle's
`{(s,t). s <o t ∧ s ∈ A ∧ t ∈ A}`). -/
def oltOn (A : Set Three) (s t : Three) : Prop := s <o t ∧ s ∈ A ∧ t ∈ A

theorem oltOn_trans (A : Set Three) : ∀ ⦃a b c⦄, oltOn A a b → oltOn A b c → oltOn A a c :=
  fun _ _ _ h1 h2 => ⟨olt_trans h1.1 h2.1, h1.2.1, h2.2.2⟩

theorem ole_trans {x y z : Three} (h1 : x ≤o y) (h2 : y ≤o z) : x ≤o z := by
  rcases h1 with h1 | rfl
  · exact Or.inl (olt_ole_trans h1 h2)
  · exact h2

/-! ## `NF` terms are zero-top sums -/

theorem NF_lead0 {x : Three} (hx : x ∈ NF) {a : ℕ} {b c : Three}
    (he : x = P a b c) : a = 0 := by
  obtain ⟨M, hM, rfl⟩ := hx
  have inv : inv2 ((incpref M).map Prod.snd) := (nfinv_ST_PS hM).2
  have s0 := inv 0 (Nat.zero_le _)
  have sp : spine (translate M) = (incpref M).map Prod.snd := spine_translate_eq M
  have hsp : spine (translate M) = a :: spine b := by rw [he, spine_P]
  have h0 : ((incpref M).map Prod.snd).getD 0 0 = 0 := s0.2
  rw [← sp, hsp] at h0
  simpa using h0

theorem cnf_NF {x : Three} (hx : x ∈ NF) : cnf x := by
  obtain ⟨M, hM, rfl⟩ := hx
  exact cnf_ST_PS hM

theorem NF_zerotops {x : Three} (hx : x ∈ NF) : ∀ s ∈ tops x, s = 0 := by
  cases x with
  | Z => simp
  | P a b c =>
    have a0 : a = 0 := NF_lead0 hx rfl
    have hle : ∀ s ∈ tops c, s ≤ a := cnf_tops_le (cnf_NF hx)
    intro s hs
    rw [tops_P] at hs
    rcases List.mem_cons.1 hs with rfl | hs
    · exact a0
    · have := hle s hs
      omega

theorem sargs_le_hd {b c : Three} (hcnf : cnf (P 0 b c))
    (htops : ∀ s ∈ tops (P 0 b c), s = 0) {k : Three} (hk : k ∈ sargs c) :
    k ≤o b := by
  induction c generalizing b with
  | Z => simp at hk
  | P e f g ihf ihg =>
    have e0 : e = 0 := htops e (by simp)
    subst e0
    obtain ⟨-, nlt, cnfc⟩ := cnf_P_P.1 hcnf
    have nbf : ¬ b <o f := fun h => nlt (olt_P_P.2 (Or.inr (Or.inl ⟨rfl, h⟩)))
    have fb : f ≤o b := by
      rcases olt_total f b with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h nbf
    rw [sargs_P] at hk
    rcases List.mem_cons.1 hk with rfl | hk
    · exact fb
    · have htops' : ∀ s ∈ tops (P 0 f g), s = 0 := by
        intro s hs
        exact htops s (by rw [tops_P]; exact List.mem_cons_of_mem _ hs)
      exact ole_trans (ihg cnfc htops' hk) fb

theorem sargs_noninc {x : Three} (hcnf : cnf x)
    (htops : ∀ s ∈ tops x, s = 0) :
    (sargs x).Pairwise fun b f => f ≤o b := by
  induction x with
  | Z => simp
  | P a b c ihb ihc =>
    have a0 : a = 0 := htops a (by simp)
    subst a0
    have cnfc : cnf c := by
      cases c with
      | Z => trivial
      | P e f g => exact (cnf_P_P.1 hcnf).2.2
    have topsc : ∀ s ∈ tops c, s = 0 := fun s hs =>
      htops s (by rw [tops_P]; exact List.mem_cons_of_mem _ hs)
    have hd_le : ∀ k ∈ sargs c, k ≤o b := fun k hk =>
      sargs_le_hd hcnf htops hk
    rw [sargs_P]
    exact List.Pairwise.cons hd_le (ihc cnfc topsc)

theorem olt_sum_decomp {x y : Three}
    (t0x : ∀ s ∈ tops x, s = 0) (t0y : ∀ s ∈ tops y, s = 0) (hlt : x <o y) :
    ∃ pre bs fs, sargs x = pre ++ bs ∧ sargs y = pre ++ fs ∧
      ((bs = [] ∧ fs ≠ []) ∨ (bs ≠ [] ∧ fs ≠ [] ∧ bs.headI <o fs.headI)) := by
  induction x generalizing y with
  | Z =>
    obtain ⟨e, f, g, rfl⟩ : ∃ e f g, y = P e f g := by
      cases y with
      | Z => exact absurd hlt (not_olt_Z Z)
      | P e f g => exact ⟨e, f, g, rfl⟩
    exact ⟨[], [], f :: sargs g, by simp, by simp, Or.inl ⟨rfl, by simp⟩⟩
  | P a b c ihb ihc =>
    obtain ⟨e, f, g, rfl⟩ : ∃ e f g, y = P e f g := by
      cases y with
      | Z => exact absurd hlt (not_olt_Z _)
      | P e f g => exact ⟨e, f, g, rfl⟩
    have a0 : a = 0 := t0x a (by simp)
    have e0 : e = 0 := t0y e (by simp)
    subst a0; subst e0
    have disj : b <o f ∨ (b = f ∧ c <o g) := by
      rcases olt_P_P.1 hlt with h | ⟨-, h⟩ | ⟨-, h1, h2⟩
      · omega
      · exact Or.inl h
      · exact Or.inr ⟨h1, h2⟩
    rcases disj with hbf | ⟨rfl, hcg⟩
    · exact ⟨[], b :: sargs c, f :: sargs g, by simp, by simp,
        Or.inr ⟨by simp, by simp, by simpa using hbf⟩⟩
    · have topsc : ∀ s ∈ tops c, s = 0 := fun s hs =>
        t0x s (by rw [tops_P]; exact List.mem_cons_of_mem _ hs)
      have topsg : ∀ s ∈ tops g, s = 0 := fun s hs =>
        t0y s (by rw [tops_P]; exact List.mem_cons_of_mem _ hs)
      obtain ⟨pre, bs, fs, h1, h2, h3⟩ := ihc topsc topsg hcg
      exact ⟨b :: pre, bs, fs, by simp [h1], by simp [h2], h3⟩

theorem sorted_suffix_le_hd {pre bs : List Three} {k : Three}
    (sw : (pre ++ bs).Pairwise fun b f => f ≤o b)
    (kbs : k ∈ bs) (ne : bs ≠ []) :
    k ≤o bs.headI := by
  have swbs : bs.Pairwise fun b f => f ≤o b := (List.pairwise_append.1 sw).2.1
  obtain ⟨h, t, rfl⟩ : ∃ h t, bs = h :: t := by
    cases bs with
    | nil => exact absurd rfl ne
    | cons h t => exact ⟨h, t, rfl⟩
  have tl_le : ∀ z ∈ t, z ≤o h := (List.pairwise_cons.1 swbs).1
  rcases List.mem_cons.1 kbs with rfl | hk
  · exact Or.inr rfl
  · simpa using tl_le k hk

theorem olt_sum_mult {x y : Three} {A : Set Three}
    (t0x : ∀ s ∈ tops x, s = 0) (t0y : ∀ s ∈ tops y, s = 0)
    (cx : cnf x) (hlt : x <o y)
    (bx : ∀ s ∈ sargs x, s ∈ A) (byy : ∀ s ∈ sargs y, s ∈ A) :
    DMLT (oltOn A) (margs x) (margs y) := by
  obtain ⟨pre, bs, fs, d1, d2, d3⟩ := olt_sum_decomp t0x t0y hlt
  have fs_ne : fs ≠ [] := by
    rcases d3 with ⟨-, h⟩ | ⟨-, h, -⟩ <;> exact h
  refine ⟨↑pre, ↑bs, ↑fs, by simpa using fs_ne, ?_, ?_, ?_⟩
  · rw [margs, d1]
    exact (Multiset.coe_add pre bs).symm
  · rw [margs, d2]
    exact (Multiset.coe_add pre fs).symm
  · intro k hk
    have kbs : k ∈ bs := by simpa using hk
    have bs_ne : bs ≠ [] := by
      intro he
      rw [he] at kbs
      simp at kbs
    have hdlt : bs.headI <o fs.headI := by
      rcases d3 with ⟨h, -⟩ | ⟨-, -, h⟩
      · exact absurd h bs_ne
      · exact h
    have sw : (sargs x).Pairwise fun b f => f ≤o b := sargs_noninc cx t0x
    have khd : k ≤o bs.headI := sorted_suffix_le_hd (d1 ▸ sw) kbs bs_ne
    have klt : k <o fs.headI := ole_olt_trans khd hdlt
    have hdmem : fs.headI ∈ fs := by
      cases fs with
      | nil => exact absurd rfl fs_ne
      | cons h t => simp
    refine ⟨fs.headI, by simpa using hdmem, klt, ?_, ?_⟩
    · exact bx k (d1 ▸ List.mem_append_right pre kbs)
    · exact byy fs.headI (d2 ▸ List.mem_append_right pre hdmem)

/-! ## The general sum peel: `<o` on *any* CNF sums embeds into the multiset
extension of the order on the summand singletons (no zero-tops needed) -/

/-- The summand singletons of a sum. -/
def summands : Three → List Three
  | Z => []
  | P a b c => P a b Z :: summands c

@[simp] theorem summands_Z : summands Z = [] := rfl
@[simp] theorem summands_P (a : ℕ) (b c : Three) :
    summands (P a b c) = P a b Z :: summands c := rfl

theorem summands_shape {x s : Three} (hs : s ∈ summands x) :
    ∃ a c, s = P a c Z := by
  induction x with
  | Z => simp at hs
  | P a b c ihb ihc =>
    rw [summands_P] at hs
    rcases List.mem_cons.1 hs with rfl | hs
    · exact ⟨a, b, rfl⟩
    · exact ihc hs

/-- A summand-with-its-argument view (used for the size argument in
`lvl0_acc`; replaces Isabelle's `zip`-based bookkeeping). -/
theorem summands_sargs {x s : Three} (hs : s ∈ summands x) :
    ∃ a b, s = P a b Z ∧ b ∈ sargs x := by
  induction x with
  | Z => simp at hs
  | P a b c ihb ihc =>
    rw [summands_P] at hs
    rcases List.mem_cons.1 hs with rfl | hs
    · exact ⟨a, b, rfl, by simp⟩
    · obtain ⟨a', b', he, hb⟩ := ihc hs
      exact ⟨a', b', he, by rw [sargs_P]; exact List.mem_cons_of_mem _ hb⟩

theorem summands_le_hd {a : ℕ} {b c : Three} (hcnf : cnf (P a b c))
    {k : Three} (hk : k ∈ summands c) :
    k ≤o P a b Z := by
  induction c generalizing a b with
  | Z => simp at hk
  | P e f g ihf ihg =>
    obtain ⟨-, nlt, cnfc⟩ := cnf_P_P.1 hcnf
    have efab : P e f Z ≤o P a b Z := by
      rcases olt_total (P a b Z) (P e f Z) with h | h | h
      · exact absurd h nlt
      · exact Or.inr h.symm
      · exact Or.inl h
    rw [summands_P] at hk
    rcases List.mem_cons.1 hk with rfl | hk
    · exact efab
    · exact ole_trans (ihg cnfc hk) efab

theorem summands_noninc {x : Three} (hcnf : cnf x) :
    (summands x).Pairwise fun s t => t ≤o s := by
  induction x with
  | Z => simp
  | P a b c ihb ihc =>
    have cnfc : cnf c := by
      cases c with
      | Z => trivial
      | P e f g => exact (cnf_P_P.1 hcnf).2.2
    rw [summands_P]
    exact List.Pairwise.cons (fun k hk => summands_le_hd hcnf hk) (ihc cnfc)

theorem olt_summands_decomp {x y : Three} (hlt : x <o y) :
    ∃ pre bs fs, summands x = pre ++ bs ∧ summands y = pre ++ fs ∧
      ((bs = [] ∧ fs ≠ []) ∨ (bs ≠ [] ∧ fs ≠ [] ∧ bs.headI <o fs.headI)) := by
  induction x generalizing y with
  | Z =>
    obtain ⟨e, f, g, rfl⟩ : ∃ e f g, y = P e f g := by
      cases y with
      | Z => exact absurd hlt (not_olt_Z Z)
      | P e f g => exact ⟨e, f, g, rfl⟩
    exact ⟨[], [], P e f Z :: summands g, by simp, by simp, Or.inl ⟨rfl, by simp⟩⟩
  | P a b c ihb ihc =>
    obtain ⟨e, f, g, rfl⟩ : ∃ e f g, y = P e f g := by
      cases y with
      | Z => exact absurd hlt (not_olt_Z _)
      | P e f g => exact ⟨e, f, g, rfl⟩
    by_cases hef : a = e ∧ b = f
    · obtain ⟨rfl, rfl⟩ := hef
      have cg : c <o g := by
        rcases olt_P_P.1 hlt with h | ⟨-, h⟩ | ⟨-, -, h⟩
        · omega
        · exact absurd h (olt_irrefl b)
        · exact h
      obtain ⟨pre, bs, fs, h1, h2, h3⟩ := ihc cg
      exact ⟨P a b Z :: pre, bs, fs, by simp [h1], by simp [h2], h3⟩
    · have hdlt : P a b Z <o P e f Z := by
        rcases olt_P_P.1 hlt with h | ⟨rfl, h⟩ | ⟨rfl, rfl, -⟩
        · exact olt_P_P.2 (Or.inl h)
        · exact olt_P_P.2 (Or.inr (Or.inl ⟨rfl, h⟩))
        · exact absurd ⟨rfl, rfl⟩ hef
      exact ⟨[], P a b Z :: summands c, P e f Z :: summands g, by simp, by simp,
        Or.inr ⟨by simp, by simp, by simpa using hdlt⟩⟩

theorem olt_summands_mult {x y : Three} {A : Set Three}
    (cx : cnf x) (hlt : x <o y)
    (bx : ∀ s ∈ summands x, s ∈ A) (byy : ∀ s ∈ summands y, s ∈ A) :
    DMLT (oltOn A) ↑(summands x) ↑(summands y) := by
  obtain ⟨pre, bs, fs, d1, d2, d3⟩ := olt_summands_decomp hlt
  have fs_ne : fs ≠ [] := by
    rcases d3 with ⟨-, h⟩ | ⟨-, h, -⟩ <;> exact h
  refine ⟨↑pre, ↑bs, ↑fs, by simpa using fs_ne, ?_, ?_, ?_⟩
  · rw [d1]
    exact (Multiset.coe_add pre bs).symm
  · rw [d2]
    exact (Multiset.coe_add pre fs).symm
  · intro k hk
    have kbs : k ∈ bs := by simpa using hk
    have bs_ne : bs ≠ [] := by
      intro he
      rw [he] at kbs
      simp at kbs
    have hdlt : bs.headI <o fs.headI := by
      rcases d3 with ⟨h, -⟩ | ⟨-, -, h⟩
      · exact absurd h bs_ne
      · exact h
    have sw : (summands x).Pairwise fun s t => t ≤o s := summands_noninc cx
    have khd : k ≤o bs.headI := sorted_suffix_le_hd (d1 ▸ sw) kbs bs_ne
    have klt : k <o fs.headI := ole_olt_trans khd hdlt
    have hdmem : fs.headI ∈ fs := by
      cases fs with
      | nil => exact absurd rfl fs_ne
      | cons h t => simp
    refine ⟨fs.headI, by simpa using hdmem, klt, ?_, ?_⟩
    · exact bx k (d1 ▸ List.mem_append_right pre kbs)
    · exact byy fs.headI (d2 ▸ List.mem_append_right pre hdmem)

/-! ## The level-`m` argument classes and the descent of the residual core -/

def ArgsL (m : ℕ) : Set Three :=
  {b | ∃ x ∈ NF, maxsub x = m ∧ b ∈ sargs x}

theorem sargs_subset_ArgsL {x : Three} (hx : x ∈ NF) {m : ℕ} (hm : maxsub x = m) :
    ∀ b ∈ sargs x, b ∈ ArgsL m :=
  fun _ hb => ⟨x, hx, hm, hb⟩

/-- `cnf` is hereditary along the sum arguments. -/
theorem cnf_sargs {x b : Three} (hcnf : cnf x) (hb : b ∈ sargs x) : cnf b := by
  induction x with
  | Z => simp at hb
  | P a b' c ihb ihc =>
    have cb : cnf b' := by
      cases c with
      | Z => exact cnf_P_Z.1 hcnf
      | P e f g => exact (cnf_P_P.1 hcnf).1
    have cc : cnf c := by
      cases c with
      | Z => trivial
      | P e f g => exact (cnf_P_P.1 hcnf).2.2
    rw [sargs_P] at hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact cb
    · exact ihc cc hb

theorem cnf_ArgsL {m : ℕ} {b : Three} (hb : b ∈ ArgsL m) : cnf b := by
  obtain ⟨x, hx, -, hbx⟩ := hb
  exact cnf_sargs (cnf_NF hx) hbx

/-- Summand singletons of the level-`m` arguments, and their arguments. -/
def SingA (m : ℕ) : Set Three :=
  {s | ∃ b ∈ ArgsL m, s ∈ summands b}

def ArgsA (m : ℕ) : Set Three :=
  {c | ∃ a, P a c Z ∈ SingA m}

theorem summands_subset_SingA {m : ℕ} {b : Three} (hb : b ∈ ArgsL m) :
    ∀ s ∈ summands b, s ∈ SingA m :=
  fun _ hs => ⟨b, hb, hs⟩

def singdest : Three → ℕ × Three
  | Z => (0, Z)
  | P a c _ => (a, c)

/-! ## Level 0: the base of the ladder (PrSS-style accessibility)

At level `0` all subscripts are `0`, so the singleton order never drops a
subscript and the PrSS argument (hereditary multisets, Dershowitz–Manna
accessibility) closes outright: `<o` is WF on the class of CNF terms with
`maxsub = 0`.  This is the base case of the level ladder; the induction step
(level `m` from levels `< m`) is the Buchholz-collapse core, still open. -/

def lvl0 (t : Three) : Prop := cnf t ∧ maxsub t = 0

def olt0 (c f : Three) : Prop := c <o f ∧ lvl0 c ∧ lvl0 f

theorem transp_olt0 : ∀ ⦃a b c⦄, olt0 a b → olt0 b c → olt0 a c :=
  fun _ _ _ h1 h2 => ⟨olt_trans h1.1 h2.1, h1.2.1, h2.2.2⟩

theorem cnf_summands {x s : Three} (hcnf : cnf x) (hs : s ∈ summands x) :
    cnf s := by
  induction x with
  | Z => simp at hs
  | P a b c ihb ihc =>
    have cb : cnf b := by
      cases c with
      | Z => exact cnf_P_Z.1 hcnf
      | P e f g => exact (cnf_P_P.1 hcnf).1
    have cc : cnf c := by
      cases c with
      | Z => trivial
      | P e f g => exact (cnf_P_P.1 hcnf).2.2
    rw [summands_P] at hs
    rcases List.mem_cons.1 hs with rfl | hs
    · exact cnf_P_Z.2 cb
    · exact ihc cc hs

theorem maxsub_summands_le {x s : Three} (hs : s ∈ summands x) :
    maxsub s ≤ maxsub x := by
  induction x with
  | Z => simp at hs
  | P a b c ihb ihc =>
    rw [summands_P] at hs
    rcases List.mem_cons.1 hs with rfl | hs
    · simp
      omega
    · have := ihc hs
      simp at this ⊢
      omega

/-- Structural size of a term. -/
def tsize : Three → ℕ
  | Z => 1
  | P _ b c => tsize b + tsize c + 1

theorem sargs_tsize {x b : Three} (hb : b ∈ sargs x) : tsize b < tsize x := by
  induction x with
  | Z => simp at hb
  | P a b' c ihb ihc =>
    rw [sargs_P] at hb
    rcases List.mem_cons.1 hb with rfl | hb
    · simp only [tsize]
      omega
    · have := ihc hb
      simp only [tsize]
      omega

theorem lvl0_summands {u : Three} (hu : lvl0 u) :
    ∀ s ∈ summands u, lvl0 s := by
  intro s hs
  refine ⟨cnf_summands hu.1 hs, ?_⟩
  have h1 := maxsub_summands_le hs
  have h2 := hu.2
  omega

/-- The order embeds sums into multisets of summands (level-0 instance). -/
theorem olt0_summands_dmlt {w t : Three} (h : olt0 w t) :
    DMLT olt0 ↑(summands w) ↑(summands t) := by
  obtain ⟨wt, lw, lt'⟩ := h
  have base : DMLT (oltOn {s | lvl0 s}) ↑(summands w) ↑(summands t) :=
    olt_summands_mult lw.1 wt (lvl0_summands lw) (lvl0_summands lt')
  exact base.mono fun a b ⟨hab, ha, hb⟩ => ⟨hab, ha, hb⟩

theorem Z_acc0 : Acc olt0 Z :=
  Acc.intro Z fun y hy => absurd hy.1 (not_olt_Z y)

/-- A sum is accessible once its summand multiset is. -/
theorem sum_acc {v : Three} (lv : lvl0 v)
    (hacc : Acc (DMLT olt0) (↑(summands v) : Multiset Three)) :
    Acc olt0 v := by
  have aux : ∀ M : Multiset Three, Acc (DMLT olt0) M →
      ∀ w, lvl0 w → ↑(summands w) = M → Acc olt0 w := by
    intro M hM
    induction hM with
    | intro M _ ih =>
      intro w lw hw
      refine Acc.intro w fun v hv => ?_
      have lv' : lvl0 v := hv.2.1
      have step : DMLT olt0 ↑(summands v) M := hw ▸ olt0_summands_dmlt hv
      exact ih _ step v lv' rfl
  exact aux _ hacc v lv rfl

/-- The level-0 singleton constructor preserves accessibility (no subscript
can drop below `0`, so all predecessors of `p₀(b)` are sums of `p₀(dᵢ)` with
`dᵢ <o b`: accessible by the accessibility induction on `b`). -/
theorem sing0_acc {b : Three} (hb : Acc olt0 b) (lb : lvl0 b) :
    Acc olt0 (P 0 b Z) := by
  induction hb with
  | intro b _ ih =>
    refine Acc.intro _ fun v hv => ?_
    obtain ⟨vlt, lv, lPb⟩ := hv
    cases v with
    | Z => exact Z_acc0
    | P a d e =>
      have a0 : a = 0 := by
        have := lv.2
        simp at this
        omega
      subst a0
      have dlt : d <o b := by
        rcases olt_P_P.1 vlt with h | ⟨-, h⟩ | ⟨-, -, h⟩
        · omega
        · exact h
        · exact absurd h (not_olt_Z _)
      have ld : lvl0 d := by
        refine ⟨?_, ?_⟩
        · cases e with
          | Z => exact cnf_P_Z.1 lv.1
          | P e1 e2 e3 => exact (cnf_P_P.1 lv.1).1
        · have := lv.2
          simp at this
          omega
      -- every summand of `v` is `p₀(d')` with `d' ≤o d <o b`, hence
      -- accessible by the accessibility induction hypothesis on `b`
      have summacc : ∀ s ∈ (↑(summands (P 0 d e)) : Multiset Three), Acc olt0 s := by
        intro s hs
        have sv : s ∈ summands (P 0 d e) := by simpa using hs
        obtain ⟨a', d', he, hd'⟩ := summands_sargs sv
        have ls : lvl0 s := lvl0_summands lv s sv
        have a'0 : a' = 0 := by
          have := ls.2
          rw [he] at this
          simp at this
          omega
        have d'le : d' ≤o d := by
          rw [summands_P] at sv
          rcases List.mem_cons.1 sv with hse | hse
          · rw [he] at hse
            obtain ⟨-, h2, -⟩ := Three.P.inj hse
            exact Or.inr h2
          · have hle : s ≤o P 0 d Z := summands_le_hd lv.1 hse
            rw [he, a'0] at hle
            rcases hle with hlt | heq
            · rcases olt_P_P.1 hlt with h | ⟨-, h⟩ | ⟨-, -, h⟩
              · omega
              · exact Or.inl h
              · exact absurd h (not_olt_Z _)
            · obtain ⟨-, h2, -⟩ := Three.P.inj heq
              exact Or.inr h2
        have d'b : d' <o b := ole_olt_trans d'le dlt
        have ld' : lvl0 d' := by
          refine ⟨?_, ?_⟩
          · have := cnf_summands lv.1 sv
            rw [he] at this
            exact cnf_P_Z.1 this
          · have := ls.2
            rw [he] at this
            simp at this
            omega
        have : Acc olt0 (P 0 d' Z) := ih d' ⟨d'b, ld', lb⟩ ld'
        rw [he, a'0]
        exact this
      have hmacc : Acc (DMLT olt0) (↑(summands (P 0 d e)) : Multiset Three) :=
        acc_dmlt_of_acc transp_olt0 summacc
      exact sum_acc lv hmacc

/-- **Master**: every level-0 CNF term is accessible (strong induction on
size; the sum arguments are proper subterms). -/
theorem lvl0_acc {t : Three} (lt' : lvl0 t) : Acc olt0 t := by
  generalize hs : tsize t = n
  induction n using Nat.strong_induction_on generalizing t with
  | _ n ihn =>
    subst hs
    cases t with
    | Z => exact Z_acc0
    | P a b c =>
      have summacc : ∀ s ∈ (↑(summands (P a b c)) : Multiset Three), Acc olt0 s := by
        intro s hs
        have sv : s ∈ summands (P a b c) := by simpa using hs
        obtain ⟨a', d', he, hd'⟩ := summands_sargs sv
        have ls : lvl0 s := lvl0_summands lt' s sv
        have a'0 : a' = 0 := by
          have := ls.2
          rw [he] at this
          simp at this
          omega
        have ld' : lvl0 d' := by
          refine ⟨?_, ?_⟩
          · have := cnf_summands lt'.1 sv
            rw [he] at this
            exact cnf_P_Z.1 this
          · have := ls.2
            rw [he] at this
            simp at this
            omega
        have hsize : tsize d' < tsize (P a b c) := sargs_tsize hd'
        have haccd : Acc olt0 d' := ihn (tsize d') hsize ld' rfl
        have : Acc olt0 (P 0 d' Z) := sing0_acc haccd ld'
        rw [he, a'0]
        exact this
      have hmacc : Acc (DMLT olt0) (↑(summands (P a b c)) : Multiset Three) :=
        acc_dmlt_of_acc transp_olt0 summacc
      exact sum_acc lt' hmacc

theorem wf_olt0 : WellFounded olt0 := by
  refine ⟨fun x => ?_⟩
  by_cases hx : lvl0 x
  · exact lvl0_acc hx
  · exact Acc.intro x fun y hy => absurd hy.2.2 hx

/-! ## The residual core, two levels in

WF of `<o` on the arguments (of any subscript) occurring inside the level-`m`
sum arguments.  The level-`0` instance follows from the base theorem
`wf_olt0`; the induction step (level `m` from levels `< m`) is the
Buchholz-collapse core — `sorry` exactly as in the Isabelle source (route
frozen there in favour of the `nrm` value normalisation, see `task.md`). -/

theorem wf_ArgsA (m : ℕ) : WellFounded (oltOn (ArgsA m)) := by
  sorry

theorem wf_SingA (m : ℕ) : WellFounded (oltOn (SingA m)) := by
  have wflex : WellFounded (Prod.Lex (· < · : ℕ → ℕ → Prop) (oltOn (ArgsA m))) :=
    WellFounded.prod_lex wellFounded_lt (wf_ArgsA m)
  refine Subrelation.wf ?_ (InvImage.wf singdest wflex)
  rintro s t ⟨hlt, hsS, htS⟩
  have hsS' := hsS
  have htS' := htS
  obtain ⟨bs, hbs, hss⟩ := hsS'
  obtain ⟨bt, hbt, hst⟩ := htS'
  obtain ⟨a, c, rfl⟩ := summands_shape hss
  obtain ⟨e, f, rfl⟩ := summands_shape hst
  have cA : c ∈ ArgsA m := ⟨a, hsS⟩
  have fA : f ∈ ArgsA m := ⟨e, htS⟩
  show Prod.Lex _ _ (a, c) (e, f)
  rcases olt_P_P.1 hlt with h | ⟨rfl, h⟩ | ⟨-, -, h⟩
  · exact Prod.Lex.left _ _ h
  · exact Prod.Lex.right _ ⟨h, cA, fA⟩
  · exact absurd h (olt_irrefl Z)

theorem wf_ArgsL (m : ℕ) : WellFounded (oltOn (ArgsL m)) := by
  have wfdm : WellFounded (DMLT (oltOn (SingA m))) :=
    wellFounded_dmlt (oltOn_trans _) (wf_SingA m)
  refine Subrelation.wf ?_ (InvImage.wf (fun b => ↑(summands b)) wfdm)
  rintro b f ⟨hlt, hbA, hfA⟩
  exact olt_summands_mult (cnf_ArgsL hbA) hlt
    (summands_subset_SingA hbA) (summands_subset_SingA hfA)

/-- The level-`m` within-level relation. -/
def levelRel (m : ℕ) (w x : Three) : Prop :=
  w <o x ∧ x ∈ NF ∧ w ∈ NF ∧ maxsub w = m ∧ maxsub x = m

theorem wf_level_from_args (m : ℕ) : WellFounded (levelRel m) := by
  have wfdm : WellFounded (DMLT (oltOn (ArgsL m))) :=
    wellFounded_dmlt (oltOn_trans _) (wf_ArgsL m)
  refine Subrelation.wf ?_ (InvImage.wf margs wfdm)
  rintro w x ⟨hlt, hx, hw, hmw, hmx⟩
  exact olt_sum_mult (NF_zerotops hw) (NF_zerotops hx) (cnf_NF hw) hlt
    (sargs_subset_ArgsL hw hmw) (sargs_subset_ArgsL hx hmx)

theorem wfE_from_args : WellFounded RnfE := by
  refine ⟨fun x => ?_⟩
  have aux : ∀ (m : ℕ) (x : Three), Acc (levelRel m) x → maxsub x = m →
      Acc RnfE x := by
    intro m x hacc
    induction hacc with
    | intro x _ ih =>
      intro hmx
      refine Acc.intro x fun w hw => ?_
      obtain ⟨hlt, hxNF, hwNF, hms⟩ := hw
      exact ih w ⟨hlt, hxNF, hwNF, by omega, hmx⟩ (by omega)
  exact aux (maxsub x) x ((wf_level_from_args (maxsub x)).apply x) rfl

/-! ## Top-level: PSS termination, modulo the argument core -/

theorem wf_Rnf : WellFounded Rnf :=
  wf_Rnf_from_within_level wfE_from_args

/-- **PSS termination** (pure-lex, ordinal-free), modulo `wf_ArgsA` — the
sole remaining obligation of the whole development: WF of `<o` on the
level-`m` argument class (the Buchholz collapse core). -/
theorem PSS_terminates : WellFounded stepRel :=
  step_terminates wf_Rnf

end YAPSS
