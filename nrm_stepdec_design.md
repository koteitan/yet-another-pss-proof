# Design: proving `nrm_step_dec` / `nrm_order_pres` term-structurally

Status: 2026-06-13. Supersedes the DEAD spanOK/dichOK/msfx combinatorial
approach (those are false PROXIES for a true term-level statement; see memory
`nrm-campaign-status`). This is the disciplined paper sketch required before
new Lean (soundness-discipline rule 3), grounded in:
- Buchholz 1987 *An independence result for (Π¹₁-CA)+BI* (../Buchholz_1987_BHydra…pdf) — METHOD.
- Koteitan, *Upper-Branch-Ignoring (上枝無視) モデル* (../UserBlog_Koteitan_…html) — forest STRUCTURE.
- The actual Lean target in `YAPSS/Nrm.lean`.

## 1. The real architecture (verified by reading Nrm.lean / Proofs.lean / Mechanized.lean)

- `NT` ≡ `translate : PairSeq → Three`, `Three = Z | P (a:ℕ) b c` = `p_a(b)+c`,
  `<o` = subscript-first lex order.
- `m_step_decreases : translate (M⟦n⟧) <o translate M` — **DONE** (Mechanized.lean:1061).
- `wf_olt_wf3 : <o` is wellfounded on Buchholz-OT terms `wf3` — **DONE** (Otembed).
- `nrm : Three → Three` normalizes any term to a `wf3` term of the same ψ-value:
  `nrm Z = Z`, `nrm (P a b c) = ins a (proj a (nrm b)) (nrm c)`.
  `proj u b` = iterated-max collapse: while `bad = {g ∈ Glist u b : ¬ g <o b}`
  nonempty, replace `b` by `max_o bad`. `ins a X t` = insert principal `p_a(X)`
  into sum `t` with absorption.
- **Sole core sorry: `nrm_order_pres {v u} (hv: v∈NF)(hu: u∈NF)(h: v<o u) : nrm v <o nrm u`** (Nrm.lean:210).
- `nrm_step_dec` (the step-only decrease, Nrm.lean:231) is currently DERIVED from
  `nrm_order_pres` + `m_step_decreases`.

### KEY LEVER
`PSS_terminates_nrm` (Nrm.lean:238) uses **only `nrm_step_dec`** via
`InvImage (fun M => nrm (translate M)) wf_olt_wf3` — it does NOT need the general
`nrm_order_pres`. So either target discharges termination; the general one is
strictly harder. We aim at the general `nrm_order_pres` because the verified
spine (below) proves it directly and uniformly; `nrm_step_dec` is then a corollary.

## 2. Verified soundness (disciplined, closure+6 — past the re-entry depth)

`tools/audit_nrm_deep.py`, `tools/probe_proj_mono.py`. Model = `valnorm.nrm/proj`
+ `fast_pss.oper` (same defs as Lean). All at closure+6 (re-entry = audit+1, so
this is past the depth where the 7 prior false invariants first broke):

| statement | checks | violations |
|---|---|---|
| `nrm_step_dec` (step pairs) | 2,345 | 0 |
| `nrm_order_pres` (general NF pairs) | 90,094 | 0 |
| advice E6 §1 + dichOK §2 re-entry hosts (real oper step) | n=1,2,3 | 0 collapse |
| **P-MONO** `b<o b' ⟹ proj u b ≤o proj u b'` | 1,505,047 | **0** |
| **NRM-MONO** `b<o b' ⟹ nrm b ≤o nrm b'` (NF subterms) | 4,305,645 | **0** |

⟹ The target is TRUE deep, *including at the exact re-entry hosts where
spanOK/dichOK/msfx are false*. The dead combinatorial invariants were false
proxies. proj/nrm monotonicity is the structural spine.

## 3. The proof spine (the plan)

```
proj_mono  : b ≤o b'  →  proj u b ≤o proj u b'            -- KEY LEMMA
ins_mono   : b ≤o b' (+ heads ok) → ins a b t ≤o ins a b' t', etc.
nrm_mono   : b ≤o b' → nrm b ≤o nrm b'                    -- induction via proj_mono, ins_mono
strictness : on NF, v <o u → nrm v ≠ nrm u (no collapse)  -- uses standardness
nrm_order_pres = nrm_mono (≤) + strictness (≠)  ⟹  nrm v <o nrm u
```

This mirrors Buchholz: `proj` is the PSS analog of the collapse `D_v`, and its
**monotonicity** is what makes the term order well-defined (Buchholz gets this
by construction of `T_v` / the `C_u` coefficient condition; we must prove it for
the iterated-max `proj`). NB (user): `D_v`=ψ ≠ `proj`=p, so not a literal port —
we reprove monotonicity for `proj`'s actual fixpoint definition.

### 3a. `proj_mono` — FALSE on wf3; the domain obstacle (verified)
`probe_proj_domain.py` (closure-independent, small terms): `proj_mono` is
**FALSE on general wf3** — 7,291 reversals. Minimal cex: `b = D0(D1 0 + D0 0)
<o b' = D1 0` but `proj0 b = D1 0 + D0 0 >o proj0 b' = D1 0` (collapsing the
smaller principal `D0(..)` *uncovers* a hidden larger value). So the clean
unconditional structural induction does NOT go through.

`probe_nf_domain.py` + membership check: the cex is invisible to the NF probe
because `b = D0(D1 0+D0 0) ∉ Args_0` (it occurs only as an arg of `D_1`), while
`b' = D1 0 ∈ Args_0`. The true monotonicity domain is `Args_u` := {args of `D_u`
principals across NF translates}, compared at the matching level `u`.
Candidate static invariants H1/H2 (arg levels ≤ a) do NOT cut it (NF translates
violate them too, 734/775). **Characterizing `Args_u` statically risks the same
elusive-combinatorial trap that killed spanOK/dichOK (discipline rule 1).**

### 3a'. VALUE REFRAME — the cleaner primary route
On wf3 terms, `<o` coincides with the ψ-value (ordinal) order (the OT property;
`wf_olt_wf3` is its wellfoundedness half). `nrm t` is wf3 and `ψ(nrm t) = ψ(t)`.
Hence `nrm v <o nrm u ⟺ ψ(nrm v) < ψ(nrm u) ⟺ ψ(v) < ψ(u)`. So:

> **`nrm_order_pres` ⟺ on NF, `<o` agrees with ψ-value order**
> (no collapse: distinct-value; no reversal: order matches value).

The off-NF cex `y₂=p₀(p₁ y₁) <o y₁=p₀(p₁(p₁ 0))`, `ψ(y₂)=ψ(y₁)` (Nrm.lean:205)
is exactly an NF-order≠value pair, and its pair seq is NON-standard — so
standardness (the UBI valid-forest condition) is precisely what forces
NF-order = value. This is Buchholz's "coefficient/`C_u` condition ⟹ term order =
value order", reproved for PSS standard forms. This route does NOT require
characterizing `Args_u` or proving `proj_mono` directly; proj/nrm monotonicity
becomes a downstream consequence of value-preservation + (order=value on wf3).
**Prereqs to locate/establish in Lean:** (i) order=value on wf3 (search Otembed
for a ψ-value map and an order-iso lemma; `wf_olt_wf3` may already carry it);
(ii) `ψ(nrm t) = ψ(t)` (nrm value-preservation — likely the design intent of nrm);
(iii) NF-order = value (the standardness crux, the genuine remaining hard core).

### 3b. Strictness from standardness (the NF hypothesis)
The off-NF counterexample (Nrm.lean:205) `y₂=p₀(p₁(y₁)) <o y₁=p₀(p₁(p₁ 0))`,
`nrm y₂ = nrm y₁`, has non-standard pair seq `(0,0)(1,1)(2,0)(3,1)(4,1)`. So the
≤→< upgrade MUST consume standardness (`ST_PS`, row-1 parenthood). In UBI terms:
standardness = the forest is a *valid* parent forest (every row-y node's parent
found by the row-(y-1) ancestor-chain rule), which forbids the collapsing
configuration. This is where the UBI model earns its place: it characterizes
exactly the standard forests, and the no-collapse property should be a forest
invariant (NOT a window-anchor — avoid the dead family).

## 4. The d0=0 re-entry, handled explicitly (discipline rule 3)
In `m_step_decreases` (Mechanized.lean:984–1033) the base `core` splits:
- **d0>0** (ascending copies): copies form ONE tree with leading subscript
  `w0 < lp.2` (core_i1). Buchholz analog: `dom = ℕ` successor/limit step.
- **d0=0** (exact copies, RE-ENTRY): "next copy re-opens at `v0`" (core_i0,
  right branch). This is the hard core. Under `nrm`: the re-entered exact copies
  are *value-collapsed* by `proj` (they re-open at the same level, so proj's
  iterated-max merges them) — and the monotonicity spine (proj_mono) treats this
  uniformly: re-entry does NOT need a special anchor, because we never bound
  row-1 by a finite anchor; we only use `proj_mono` + no-collapse-on-NF. The +6
  audit confirms step_dec holds at the exact re-entry hosts. So the re-entry is
  absorbed by the monotonicity argument, which is precisely why the
  anchor-family failed and this should not.

## 5. Next empirical pre-checks (before/with Lean, per discipline)
1. Sharpen `proj_mono`: is `proj u` monotone for ALL Three, or only on the
   wf3/NF-subterm domain? (Determines whether the Lean lemma needs a domain
   hypothesis.) Probe all-Three small terms for a reversal.
2. `ins_mono` exact statement (heads condition) — probe.
3. Strictness: characterize the no-collapse forest invariant on NF; probe which
   standardness fact (row-1 parenthood clause) is the minimal one used.

## 6. Concrete Lean lemma list (VALUE ROUTE — dependency order)

Existing machinery to reuse: `oV : Three → Ordinal` with `oV (P a b c) =
psi a (oV b) + oV c` (Otembed:18-25); `oV_order_pres : wf3 v → wf3 u → olt v u
→ oV v < oV u` (Otembed:298, the wf3 half — DONE); `wf3_nrm`, `proj_wf3`,
`proj_G`, `wf3_ins`, the `Cset`/`Ccond`/`psi_strict_mono_arg`/`C_build` apparatus.

1. **`psi_proj : psi (oV (proj a b)) a = psi (oV b) a`** — the OUTER ψ_a is
   invariant under proj at level a. NB `oV (proj a b) = oV b` is FALSE in general
   (proj changes the value); only ψ_a of it is preserved (Buchholz: ψ_a is
   constant on the interval up to the critical value; Nrm.lean:7-9). Induct on
   `tsize b` along `proj`'s recursion; each collapse step
   `b ↦ g* = max_o {g∈Glist a b : g≥o b}` satisfies `psi (oV g*) a = psi (oV b) a`
   (the coefficient `g*≥o b` is exactly the "critical value reached" so ψ_a
   plateaus from `oV b` to `oV g*`). FIRST TARGET.

   **ENGINE sub-lemma `psi_plateau`** (the precise obligation, against the actual
   `proj`/`Glist`/`maxo` defs in Nrm.lean:38-88):
   `g ∈ Gterm a b → ¬ olt g b → psi (oV g) a = psi (oV b) a`.
   Then `psi_proj` by `Nat.strong_induction_on (tsize b)` along `proj`'s
   recursion: base (filter `(Glist a b).filter (¬ olt · b) = []` → `proj a b = b`,
   refl); step (`proj a b = proj a g*`, `g* = maxo gs.headI gs.tail ∈ filtered ⊆
   Gterm a b` with `¬ olt g* b`; `tsize g* < tsize b` by `Gterm_tsize`; IH gives
   `psi (oV (proj a g*)) a = psi (oV g*) a`, and `psi_plateau` gives
   `psi (oV g*) a = psi (oV b) a`). The reusable `maxo_hdtl_in`,
   `mem_Glist`, `List.mem_of_mem_filter`, `Gterm_tsize` are already in Nrm.lean.
   `psi_plateau` itself is the genuine ordinal work: `g ∈ Gterm a b` = `g` is an
   `a`-coefficient of `b`; the `Cset`/`psiRes` apparatus (Psi.lean:65-291,
   esp. `below_psi_mem_Cset`, `psi_mono_arg`, `psi_unfold`, `Cset_psi_closed`)
   plus the `ccnd`/`allprinc_lt` pattern from `oV_order_pres` should show ψ_a does
   not jump between `oV b` and `oV g`. CAUTION: term-order `¬olt g b` does NOT
   give `oV b ≤ oV g` off-wf3 — the plateau must be argued from coefficient
   membership (Cset), not from a value inequality.
2. **`oV_ins : wf3 b → wf3 c → oV (ins a b c) = oV (P a b c)`** — absorption
   preserves value. Worked out: `ins a b Z = P a b Z` (refl); `ins a b (P e f g)`
   = (else) `P a b (P e f g) = P a c` (refl) | (then, `a<e ∨ (a=e ∧ olt b f)`)
   `P e f g = c`, so need `oV (P a b c) = oV c`, i.e. `psi (oV b) a + oV c = oV c`
   — absorption, holds iff `psi (oV b) a < ψ_e(oV f)` (leading additive-principal
   term of `oV c`; `ξ + ψ = ψ` for ξ<ψ additive-principal). Sub-cases:
   • `a < e`: `psi (oV b) a < Om (a+1) ≤ Om e ≤ psi (oV f) e` (`psi_lt_Om_succ`,
     `Om_mono`, `Om_le_psi`) — i.e. `psi_subscript_jump`.
   • `a = e ∧ olt b f`: need `psi (oV b) a < psi (oV f) a` = `psi_strict_mono_arg`
     from `oV b < oV f` (= `oV_order_pres` on wf3 `b,f`) + `oV b ∈ Cset(psiRes(oV b))(oV b) a`
     (the ccnd coefficient membership, available for wf3 — same pattern as
     oV_order_pres's argument case, Otembed:336-356). **Needs the wf3 hyps**;
     in the nrm use `ins a (proj a (nrm b)) (nrm c)` both args are wf3
     (`proj_wf3∘wf3_nrm`, `wf3_nrm`), so the hyps are discharged. Requires the
     absorption fact `addprinc δ → ξ < δ → ξ + δ = δ` (find in Mathlib or via
     `psi_add_principal`/`add_absorp`).
3. **`oV_nrm : oV (nrm t) = oV t`** — induction from 1,2:
   `oV(nrm(P a b c)) = oV(ins a (proj a (nrm b)) (nrm c)) =_2 psi a (oV(proj a (nrm b))) + oV(nrm c) =_1 psi a (oV(nrm b)) + oV(nrm c) = psi a (oV b)+oV c`.
4. **`oV_order_refl : wf3 x → wf3 y → oV x < oV y → olt x y`** — the converse of
   `oV_order_pres` on wf3, via olt-trichotomy on wf3 (olt linear on wf3) + the
   forward direction. Cheap.
5. **`oV_nf_order_pres : v∈NF → u∈NF → olt v u → oV v < oV u`** — THE HARD CORE.
   The wf3 proof `oV_order_pres` uses wf3's `Gterm` conditions; NF terms are not
   wf3, so this must instead use STANDARDNESS (`ST_PS`, the UBI valid-forest /
   row-1-parenthood invariant) to control where `oV(P a b c)`'s principal lands.
   The off-NF cex (Nrm.lean:205) is precisely an NF-violating pair, so
   standardness is exactly what's consumed. Verified true at +6 (0 reversal/
   collapse). Strategy TBD: likely adapt the `allprinc_lt`/`Cset` argument with
   a standardness-derived substitute for the G-condition; or route via `nrm`
   (since `oV∘nrm=oV` and `nrm` lands in wf3, relate the raw olt to the nrm'd
   one using standardness). This is where UBI structure must be turned into a
   value statement.
6. **Assemble `nrm_order_pres`**: `nrm v, nrm u` wf3 (`wf3_nrm`); want
   `olt (nrm v)(nrm u)`; by (4) suffices `oV(nrm v) < oV(nrm u)`; by (3)
   `= oV v < oV u`; by (5) from `olt v u` on NF. ∎
   Then `nrm_step_dec` is the special case `v=translate(M⟦n⟧), u=translate M`
   (via `m_step_decreases`), discharging `PSS_terminates_nrm`.

Lemmas 1-4 are clean value-arithmetic (tractable, do first). Lemma 5 is the
irreducible hard core and the ONLY place standardness/UBI enters — and it is a
VALUE statement, not a combinatorial window invariant, so it escapes the dead
spanOK/dichOK family.

## PROGRESS
- **lemma 4 `oV_order_refl` — DONE & kernel-checked** (Nrm.lean, commit 98ef189):
  `wf3 x → wf3 y → oV x < oV y → olt x y` (olt-trichotomy + oV_order_pres).
- **lemma 2 `oV_ins` — DONE & kernel-checked** (Nrm.lean, commit b2f815a).

## ⚠️ CORRECTED DIFFICULTY (this turn): `psi_proj` IS A HARD CORE = Buchholz collapsing lemma
§7's "lemmas 1-3 low-risk" was WRONG. `oV_ins` (2) and `oV_order_refl` (4) ARE
easy (done). But **`psi_proj` (1) / its engine `psi_plateau` is the Buchholz
*collapsing lemma* and is genuinely hard — comparable to the original core.**
Analysis this turn:
- Tried to reduce the obligation `psi(oV b)a ∉ Cset(psiRes(oV g))(oV g)a` to
  NEC `oV t ∈ C_a(α) → ∀x∈Gterm a t, oV x < α`. **NEC IS FALSE**: the plateau
  lets `psi(oV g)a ∈ C_a(α)` even when `oV g ≥ α` (via `psi α' a = psi(oV g)a`
  for some `α'<α`). So necessity-of-coefficients fails.
- The obligation `psi(oV b)a ∉ C_a(oV g)` is ≈ the plateau itself (circular via
  simple Cset arguments). The codebase has only the SUFFICIENCY direction
  (`oV_order_pres`, `Ccond_of_lt`/`C_build`); the collapsing/constancy direction
  is NOT formalized.
- ψ NON-INJECTIVITY (= the plateau) makes all the natural converses
  interdependent (psi_strict_mono_arg's converse, NEC, the obligation all
  reduce to each other). Need Buchholz's genuine simultaneous development.
**Needed ordinal module (Buchholz collapsing, to formalize):**
  (M1) additive-principal form: `δ ∈ C_v(α)`, `δ` add-principal, `Om v ≤ δ <
       Om(v+1)` ⟹ `∃ ξ<α, ξ∈C_v(α), δ = psi ξ v` (level forced by disjoint
       Om-ranges — TRUE & provable, induction on Citer stage; insufficient alone).
  (M2) `oV b ∉ C_a(oV b)` from the OT3 failure `∃g∈Gterm a b, ¬olt g b`
       (the ordinal form of "b is not a-reduced").
  (M3) converse strict-mono / constancy: `α<β ∧ α∉C_a(α) ⟹ psi α a = psi β a`
       (the actual collapsing fact; the hard interdependent core).
  Then `psi_plateau`: from g∈Gterm a b, ¬olt g b get `oV b∉C_a(oV b)` (M2) ⟹
  `psi(oV b)a = psi(oV g)a` (M3). This is textbook Buchholz — TRUE, but a real
  formalization effort (several interdependent ordinal lemmas).
NB: the value route is still the right route (clear classical targets, vs the
dead combinatorial families and the stuck syntactic route), but the difficulty
is now honestly TWO hard cores: `psi_proj` (Buchholz collapsing, M1-M3) and
`oV_nf_order_pres` (standardness/UBI). Lemmas 2,3,4 are/were the easy glue.

## DEEPER FINDINGS on `psi_proj` (this turn — guides the collapsing development)
Proven building blocks (all kernel-checked): `psi_form_of_mem` (M1),
`psi_eq_of_notMem` (the bridge: `α≤β ∧ psi α v∉C_v(β) → psi α v = psi β v`,
Otembed), `proj_oV_mem_C` (the proj fixpoint is a-reduced: `oV p∈C_a(oV p)`).
So `psi_proj` reduces to the per-step obligation **`psi(oV t)a ∉ C_a(oV g*)`**.
KEY FRAMING FINDINGS:
- **MUST prove `psi_proj` PER-STEP** (induction along proj's recursion), NOT via
  the fixpoint: for multi-step proj, intermediate coefficients drop below `oV p`,
  so `C_build` would give `oV b∈C_a(oV p)` and the plateau collapses. Per-step,
  `g*` = MAX coefficient `≥o t`, so `oV g* = α` is exactly the BOUNDARY and is
  the blocking coefficient (`g*∈Gterm a t`, `oV g* = oV g* ≮ oV g*`).
- The obligation ≡ the NECESSITY direction of the C-characterization
  `oV t ∈ C_a(α) ⟺ ∀x∈Gterm a t, oV x < α`. The codebase has only SUFFICIENCY
  (`C_build`/`Ccond_of_lt`). **NEITHER project (Lean nor Isabelle ord/) has the
  necessity/collapsing lemma** (checked otembed.thy: only sufficiency; nrm.thy
  is value-free + sorry). So it is genuine unformalized territory — the classical
  Buchholz normal-form/collapsing lemma.
- CAUTION: `M1` alone is INSUFFICIENT (the plateau lets `psi(oV t)a = psi ξ a`,
  `ξ<oV g*`, with no contradiction). And NEC may need MORE than `wf3` — the ψ
  non-injectivity (plateau) means even a-reduced `oV g*∈C_a(oV g*)` can have
  plateau points `ξ<oV g*` with `psi ξ a = psi(oV g*)a`. The necessity direction
  likely needs a careful simultaneous induction (Buchholz §1) establishing the
  exact C-membership characterization for OT values — a focused multi-lemma
  ordinal development. This is the honest remaining shape of hard core 1.

## NEC IS PROVABLE — value-bound done, arg-extraction is the precise gap
Big positive update: the earlier "NEC is false via plateau" worry was WRONG.
`psi_strict_mono_mem` rules out the plateau membership. NEC reduces the
obligation: `psi(oV b)a ∉ C_a(oV g*)` ⟸ NEC on `P a b Z` (oV = psi(oV b)a, a
pure principal), since `g*∈Gterm a (P a b Z)` and NEC would force `oV g*<oV g*`.
- **NEC value-bound (DONE-able): `psi(oV b)a ∈ C_a(α) → oV b < α`.** Proof:
  M1 → `psi(oV b)a = psi ζ a`, `ζ<α`, `ζ∈C_a(α)`; `psi_strict_mono_mem` →
  `psi(oV b)a < psi α a`; contrapositive of `psi_mono_arg` (oV b≥α → psi(oV b)a
  ≥ psi α a) → `oV b < α`. CLEAN, uses only proven lemmas.
- **Remaining gap = arg-extraction / recursion into deeper coefficients.** NEC
  needs `∀x∈Gterm a b, oV x<α` too (the critical `g*∈Gterm a b`). Recursing
  needs `oV b ∈ C_a(α)` (have only `oV b<α`) and, for the head principal,
  `psi(oV b')a' ∈ C → oV b' ∈ C` — which FAILS naively due to the plateau
  (M1 gives `psi ζ a' = psi(oV b')a'` with `ζ ≠ oV b'` possible). This
  plateau-in-recursion is the genuine Buchholz NEC technical core. Likely needs
  a strengthened simultaneous induction (Buchholz §1) or a CNF/wf3 structural
  argument for sum/arg decomposition. Proven tools ready: `psi_form_of_mem`(M1),
  `psi_strict_mono_mem`, `psi_eq_of_notMem`, `proj_oV_mem_C`.

## COLLAPSING MODULE — pieces cracked + precise remaining sub-frontiers
Proven sorry-free this turn (Otembed, toward `psi_proj`/NEC):
`psi_form_of_mem`(M1, band-v add-principal members are psi_v values),
`psi_eq_of_notMem`(plateau bridge), `psi_strict_mono_mem`(ζ∈C_v(α),ζ<α→psi ζ v<
psi α v), `psi_arg_lt_of_mem`(psi β v∈C_v(α)→β<α, LEVEL v), `Cset_add_split`
(C_v(α) closed under CNF-summand extraction — the SUM half of NEC), `proj_oV_mem_C`.
**NEC needs wf3** (arg-extraction `psi β v∈C→β∈C` is FALSE in general: a plateau
point β∉C can have `psi β v=psi ζ v∈C`). NEC-wf3 induction path:
- t=P a' b' c' (wf3): `Cset_add_split` (r=oV c'<δ=psi(oV b')a' by headle) →
  `psi(oV b')a'∈C ∧ oV c'∈C`. Tail: IH on c' (oV c'∈C, wf3 c'). ✓ structure.
- HEAD remaining sub-frontier: need `oV b'<α` from `psi(oV b')a'∈C_v(α)` with
  a'≥v (b'∈Gterm v t). `psi_arg_lt_of_mem` is LEVEL-v only; at level a'≠v the
  proof breaks (psi_strict_mono_mem/psi_notMem are level-specific: `psi α a'`
  may BE in C_v(α) for a'≠v). So need a CROSS-LEVEL `psi_arg_lt` (psi β a'∈
  C_v(α), a'≥v → β<α) — genuinely subtle, the next real sub-lemma.
- Then recurse into Gterm v b': needs oV b'∈C (have only oV b'<α) → uses wf3
  canonicity (Ccond_of_lt: wf3 principal → oV(arg)∈C_a'(oV arg)) — the
  canonicity propagation. This is where wf3 is essential.
Honest: collapsing core = several more cross-level/canonicity lemmas. ~half the
pieces cracked this turn. C2 (oV_nf_order_pres, standardness) untouched.

### UPDATE: cross-level RESOLVED; 3 NEC subtleties pinned (research-grade)
- RESOLVED: `Cset_level_mono` + `psi_arg_lt_of_mem_cross` (v≤a', psi β a'∈C_v(α)
  →β<α). So NEC's SPINE coefficients at any level a'≥v are bounded. ✓
- `Cset_add_split` proven but GENUINELY needs `r<δ` (dropping it breaks the
  ψ-case via absorption `δ+r=r`, e.g. δ=1,r=ω). So it peels only STRICTLY-
  decreasing CNF.
- 3 confirmed subtleties blocking a naive NEC: (i) head-arg-behind-collapse
  (arg-extraction `psi β v∈C→β∈C` FALSE via plateau); (ii) level mismatch
  (wf3-canonicity gives C at level a'≥v, need level v, `C_v⊆C_{a'}` wrong way);
  (iii) repeated principals (`wf3(P a b c)` allows `c=P a b c'`=ψ_a(b)·2, so
  `oV c<psi(oV b)a` FALSE → Cset_add_split can't peel; needs multiplicity-aware
  peeling-from-right or a CNF-list lemma).
⟹ NEC = a careful NESTED induction (tsize×level) with wf3 spine structure
(spinesub_le/headle/allprinc_lt_spine) + repeat handling. All 13 supporting
lemmas this turn SUPPORT it; the assembly is a focused multi-session formalization
of Buchholz's normal-form/collapsing lemma (unformalized in BOTH projects).
`psi_proj` IS TRUE (= nrm value-preservation, the design intent).

### CONCRETE NEC EXECUTION ROADMAP (next session)
Target: `NEC : wf3 t → oV t ∈ C_v(α) → ∀ x ∈ Gterm v t, oV x < α`. Then the
obligation `psi(oV b)a ∉ C_a(oV g*)` follows (apply NEC to `P a b Z` at level a;
`g*∈Gterm a b` would force `oV g*<oV g*`); and `psi_proj` follows via
`psi_eq_of_notMem`. Roadmap:
1. **Spine-principal extraction lemma** `oV t∈C_v(α) → wf3 t → every spine
   principal psi(oV bi)ai of oV t (ai≥v) is ∈C_v(α)`. Induction on the Three
   tail (P a0 b0 c0 → head + c0). Head/tail split needs Cset extraction with
   REPEAT handling: when head(c0)=head(P a0 b0 Z) (equal principal), peel via a
   multiplicity-aware lemma (`ψ_a(b)·(k+1)+s ∈C, head(s)≤ψ_a(b) → ψ_a(b)∈C`,
   provable since the leading ψ_a(b) is NOT absorbed — the absorption-break of
   Cset_add_split only happens when δ < r's head, which CNF-decreasing forbids).
   Build this `Cset_lead_split` (head(r)≤δ instead of r<δ) — the right
   generalization of `Cset_add_split` for CNF.
2. For each spine principal psi(oV bi)ai∈C_v(α): `psi_arg_lt_of_mem_cross`
   (ai≥v) → oV bi<α (the `{bi}` part of Gterm v t). ✓ (cross-level done).
3. Deep recursion (Gterm v bi): need oV bi∈C_v(α). NOT obtainable from
   psi(oV bi)ai∈C (arg-extraction false). RESOLUTION: recurse via wf3-canonicity
   — wf3 bi → oV bi∈C_{ai}(oV bi) (Ccond_of_lt). Then NEST: prove a level-indexed
   NEC `NEC_lvl : wf3 t → oV t∈C_w(β) → ∀x∈Gterm w t, oV x<β` and recurse on bi
   at LEVEL ai with β:=α (need oV bi∈C_{ai}(α): from oV bi<α + oV bi∈C_{ai}(oV bi)
   ⊆C_{ai}(α) via CC_mono). Then Gterm ai bi<α. The level-[v,ai) coefficients of
   bi are handled because bi's spine subscripts are ≤ai (wf3_spinesub_le) so
   Gterm v bi = Gterm ai bi when... CHECK: is Gterm v bi = Gterm ai bi for wf3 bi
   with lead bi ≤ ai? Gterm w collects args of principals with subscript ≥w;
   bi's principals have subscript ≤ lead bi ≤ ai. So principals with subscript in
   [v, ai) ARE collected by Gterm v but maybe not Gterm ai. NEED: lead bi and the
   spine vs v. If lead bi < v: Gterm v bi=∅ (no principal ≥v), trivial. This
   needs care — the level bookkeeping is the crux of the nested induction.
KEY tools ready: Cset_add_split, Cset_level_mono, psi_arg_lt_of_mem_cross,
psi_form_of_mem, wf3_spinesub_le, Ccond_of_lt, wf3_headle, allprinc_lt_spine.
Estimated: a focused session building Cset_lead_split + the nested NEC_lvl.

### DONE (this continued session): spine-extraction machinery, all sorry-free
- `Cset_add_split` GENERALIZED to `r < δ+r` (handles repeated principals; the
  Cset_lead_split goal — DONE, cleaner than expected).
- `olt_cons_tail`, `oV_tail_lt` (supplies `r<δ+r`), `head_tail_mem`
  (oV(P a b c)∈C_v(α) → ψ_a(oV b)∈C ∧ oV c∈C). 17 lemmas total this turn.

### THE IRREDUCIBLE WALL (precise, for fresh attack)
NEC-wf3 `wf3 t → oV t∈C_v(α) → ∀x∈Gterm v t, oV x<α`, induction on tsize t,
t=P a b c. TAIL (Gterm v c): `head_tail_mem`→oV c∈C_v(α), IH(c). ✓. HEAD {b}:
cross-level psi_arg_lt → oV b<α. ✓. **HEAD-ARG DEEP (Gterm v b): THE WALL.**
- Need oV b∈C_v(α) to recurse IH(b, level v). Have only oV b<α + (wf3 t ⟹)
  oV b∈C_a(oV b) (Ccond, level a) ⊆ C_a(α). LEVEL MISMATCH: have C_a(α) (a≥v),
  need C_v(α); `C_v⊆C_a` is the wrong direction.
- Can't extract oV b∈C from ψ_a(oV b)∈C (arg-extraction FALSE, plateau).
- Can't bound oV x<α (x∈Gterm a b) from oV b<α (collapse: oV x can exceed oV b).
- Recursing on b at level a covers Gterm a b but NOT Gterm v b's level-[v,a)
  coefficients (from b's lower spine principals); those need oV b∈C_v(α) again.
CANDIDATE FRESH DIRECTIONS (none cracked yet):
  (A) Strengthen IH to carry C-membership at ALL levels ≤ lead, proven by a
      simultaneous induction with C_build (the NEC⟺C_build mutual recursion,
      broken by tsize well-foundedness — but the head-arg has smaller tsize, so
      maybe IH(b) gives BOTH "Gterm v b<α ⟸ oV b∈C_v(α)" AND a way to get
      oV b∈C_v(α) from the wf3 spine + oV b<α).
  (B) Prove the dedicated lemma `wf3 b → oV b < α → (∀ spine principal ψ_{a'}(d)
      of b with a'≥v: ψ_{a'}(d) ∈ C_v(α))` directly by induction on b's spine,
      using oV_tail_lt/head_tail_mem-style extraction INSIDE b — but this needs
      oV b∈C_v(α) as the entry, same wall.
  (C) Reformulate via Buchholz's actual NF proof (Buchholz [2] / the 1986 ψ
      paper ../Buchholz_1986_psi...pdf): the standard proof of "C_v(α) = {oV t :
      Gterm v t < α}" likely uses a transfinite induction on α or a direct
      structural argument we haven't replicated. CHECK that paper next.
  (D) Maybe NEC at level v is FALSE for the head-arg deep coefficients and the
      RIGHT statement bounds Gterm at the term's OWN levels (a level-indexed
      Gterm matching the spine), making the recursion level-consistent. Re-derive
      what the obligation EXACTLY needs (g*∈Gterm a b, level a = obligation level)
      and whether a level-a-only NEC suffices (avoiding the [v,a) gap).
Next concrete: read Buchholz 1986 ψ paper for the NF/C-characterization proof
structure (direction C), OR pursue (D) — the obligation only needs level a, so a
level-MATCHED NEC (`b wf3 → ψ_a(oV b)∈C_a(α) → ∀x∈Gterm a b, oV x<α`) might avoid
the [v,a) gap entirely (Gterm a, level a → no lower-level range). Verify (D) first.

## ★ BREAKTHROUGH (direction C): Buchholz 1986 has the C-characterization
Read ../Buchholz_1986_psi...pdf §1. The key facts:
- **Lemma 1.9**: `γ∈C_u(α) ⟺ G_u γ ⊆ α`, where `G_u γ` = Buchholz's coefficient
  set (the ordinal analog of Three's `Gterm u`). The `⟹` is EXACTLY NEC. Proven
  by induction on the C-rank `min{n: γ∈C_0^n(ε)}` (NOT tsize), using 1.4(c).
- **Lemma 1.4(c)**: `Ω_v ≤ ψ_u ξ ∈ C_v(α) ∧ ξ∈C_u(ξ) ⟹ ξ∈α∩C_v(α)`. So
  **ARG-EXTRACTION `ψ_a(oV b)∈C_v(α) → oV b∈C_v(α)` HOLDS when oV b is CANONICAL
  (`oV b∈C_a(oV b)`)** — which wf3 PROVIDES (Ccond: wf3(P a b c)→oV b∈C_a(oV b)).
  My earlier "arg-extraction false via plateau" was for NON-canonical args only.
  THIS BREAKS THE WALL: NEC's head-arg recursion gets `oV b∈C_v(α)` from
  `ψ_a(oV b)∈C_v(α)` (head_tail_mem) + canonicity (wf3), then recurses.
- Supporting: 1.4(a) (unique ψ-rep for canonical args), 1.4(b) (`γ∈C_v(α)`,
  `Ω_v≤γ∈P` → `∃u ξ, γ=ψ_u ξ ∧ ξ∈α∩C_v(α)∩C_u(ξ)` — M1 + CANONICAL witness),
  1.2(e) `γ∈C_v(α)⟺P(γ)⊆C_v(α)`, 1.5 `C_v(α)∩Ω_{v+1}=ψ_v α`.
- **CAVEAT (Lean port):** Lean's `Cstep` (Psi.lean:59) OMITS Buchholz's
  canonicity side-condition `ξ∈C_u(ξ)` on the ψ-generator (Buchholz Remark p.197:
  the SETS are equal, but his lemmas use the canonical generation). So my M1
  (`psi_form_of_mem`) gives a witness `ζ∈C_v(α)` with `ψ_a ζ=ψ_a(oV b)` but NOT
  necessarily `ζ` canonical / `ζ=oV b` (the `ζ<oV b` plateau case). Need either:
  (i) the canonical-witness M1 (Buchholz 1.4(b)) — show the Lean C_v(α) = the
  canonically-generated set, OR (ii) prove arg_extract directly: from
  `oV b∈C_a(oV b)` + `ψ_a ζ=ψ_a(oV b)` + `ζ∈C_v(α)`, the `oV b≤ζ` subcase forces
  `oV b=ζ∈C_v(α)` (psi_strict_mono_arg rules out `oV b<ζ`); the `ζ<oV b` subcase
  needs the canonical-rep argument (oV b is the canonical/minimal rep so... TBD).

### CONCRETE NEXT (port plan)
Define `arg_extract : oV b∈C_a(oV b) → ψ_a(oV b)∈C_v(α) → oV b∈C_v(α)` (1.4(c)
specialized; the `ζ<oV b` subcase is the remaining ordinal lemma — likely needs
"canonical rep is minimal in its plateau" or the C-set generation equivalence).
Then NEC by induction on tsize: head principal → head_tail_mem → ψ_a(oV b)∈C_v(α)
→ arg_extract (wf3 canonicity) → oV b∈C_v(α) → IH(b). Tail → IH(c). WALL BROKEN
modulo arg_extract. This is the path to psi_proj → oV_nrm → termination.

### OLD PROGRESS (oV_ins detail)
- **lemma 2 `oV_ins` — DONE & kernel-checked** (Nrm.lean, commit b2f815a).
  Final signature: `oV_ins (wb : wf3 b) (wc : wf3 c) (hGb : ∀ x ∈ Gterm a b,
  olt x b) : oV (ins a b c) = oV (P a b c)`. In the nrm use the args are
  `proj a (nrm b)` / `nrm c`, so `wb=proj_wf3∘wf3_nrm`, `wc=wf3_nrm`,
  `hGb=proj_G`.
- **lemma 1 `psi_proj` — NEXT.** Take `wf3 b` (every term in `proj`'s recursion
  on a wf3 seed `nrm b` is wf3, via `wf3_Gterm`). Statement:
  `psi_proj (wb : wf3 b) : psi (oV (proj a b)) a = psi (oV b) a`. Strong
  induction on `tsize b` along proj; engine is `psi_plateau`.
  - **`psi_plateau` reduced (wf3 form):** `wf3 b → wf3 g → g ∈ Gterm a b →
    ¬ olt g b → psi (oV g) a = psi (oV b) a`. Via olt-trichotomy on wf3:
    `g = b` (refl) or `olt b g`. In the `olt b g` case `oV_order_pres` gives
    `oV b < oV g`, so `psi (oV b) a ≤ psi (oV g) a` (`psi_mono_arg`); the reverse
    `psi (oV g) a ≤ psi (oV b) a` needs **`psi (oV b) a ∉ Cset (psiRes (oV g)) (oV g) a`**
    (then `psi (oV g) a = sInf{γ∉…} ≤ psi (oV b) a` via `csInf_le'`). THE precise
    remaining obligation. It should hold because `g ∈ Gterm a b` with `oV b<oV g`
    means `oV b` is built from a principal `ψ_{a'}(oV g)` (a'≥a) with `oV g>oV b`
    — the "non-normal/critical" config where `ψ_a` plateaus. Needs Cset analysis
    (`below_psi_mem_Cset`, `Cset_psi_closed`, `psi_notMem`, `CC_mono`). HARD CORE
    of the value lemmas — focused ordinal proof.
- After `psi_proj`: **lemma 3 `oV_nrm`** is a short induction
  (`oV(nrm(P a b c)) =oV_ins= oV(P a (proj a (nrm b)) (nrm c)) = psi(oV(proj a (nrm b)))a
  + oV(nrm c) =psi_proj= psi(oV(nrm b))a + oV(nrm c) =IH= psi(oV b)a+oV c`).

## 7. Viability note (disciplined, before committing): VALUE route is NEW territory
The Isabelle source `ord/nrm.thy` states explicitly: *"the ψ-semantics only
**motivates** nrm; the chain below **never mentions values**."* So BOTH projects
deliberately pursued a value-FREE syntactic proof of `nrm_order_pres` and left
it `sorry`. The value route here is UNATTEMPTED by either — it is not validated
by the source, which is both the opportunity (the syntactic route is stuck) and
the risk (untrodden; psi_plateau / oV_nf_order_pres may have their own walls).
Why it should still be better: it ELIMINATES reasoning about the messy `nrm`
fixpoint (via `oV∘nrm = oV`), REUSES the proven `oV_order_pres` Cset/psi
scaffold (Otembed:298, so psi_plateau is "more of the same" tractable ordinal
work the codebase already does), and ISOLATES standardness into the single value
statement (5). KEY VIABILITY QUESTION to resolve early: is (5) `oV_nf_order_pres`
genuinely easier than the raw syntactic `nrm_order_pres`? Both need the
standardness insight; the bet is that comparing raw `oV` values (clean `oV_P`/
`allprinc_lt` structure + existing scaffold) beats comparing `nrm`-fixpoints.
Decision: PURSUE the value route; prove lemmas 1-4 first (they are unconditional
and low-risk and immediately establish `oV∘nrm = oV`), which also independently
confirms nrm's value-preservation — then attack (5) with the scaffold in hand.
If (5) proves no easier than syntactic, fall back to the source's syntactic
route but armed with the UBI valid-forest characterization for standardness.
```

## ★ THIS SESSION (2026-06-14): general collapsing DONE; arg_extract pinned to SBC
Reduction chain re-confirmed and SHARPENED:
  `psi_proj` ⟸ per-step `psi(oV b)a = psi(oV g*)a` (g*=max{g∈Gterm a b:¬olt g b})
            ⟸ obligation `psi(oV b)a ∉ C_a(oV g*)` (via `psi_eq_of_notMem`, oV b≤oV g*)
  NEC (`wf3 t → oV t∈C_v(α) → ∀x∈Gterm v t, oV x<α`) head-arg recursion
            ⟸ `arg_extract` (`v≤a, oV b∈C_a(oV b), ψ_a(oV b)∈C_v(α) → oV b∈C_v(α)`)
            ⟸ **SBC** (`psi_strict_below_canonical`: `β∈C_a(β), ξ<β → ψ_a ξ < ψ_a β`).
SBC closes arg_extract's hard subcase: M1 gives ζ∈C_v(α), ζ<α, ψ_a ζ=ψ_a(oV b);
β:=oV b canonical ⟹ (psi_strict_mono_arg) ξ≤β; SBC ⟹ ζ=β (¬ζ<β) ⟹ oV b=ζ∈C_v(α).

**PROVEN this session (sorry-free, kernel-checked = [propext,Classical.choice,Quot.sound], full build 949 jobs green), in Otembed.lean after `collapse_succ`:**
- `Cset_limit_sub` (C-set continuity from below): β succ-limit, 0<β, x∈C_v(β) →
  ∃δ<β, x∈C_v(δ). Citer-stage induction; base bound-independent (δ=0); +/ψ
  generators bounded by binary `max` (β limit). [The ⊆ half of C-limit-continuity;
  ⊇ is `CC_mono`.]
- `collapse_le` (GENERAL COLLAPSING / plateau): ∀β α, α≤β → (∀γ∈[α,β), γ∉C_a(γ))
  → ψ_a α = ψ_a β. Transfinite induction on β: succ iterates `collapse_succ`
  (1.6(a)); limit uses `Cset_limit_sub` to show ψ_a α∉C_a(β) ⟹ ψ_a β≤ψ_a α.
- `Cset_lt_psi_of_lt_Om` (**Buchholz 1.5**, the useful ⊆ half): x∈C_a(α) ∧
  x<Ω_{a+1} → x<ψ_a α (i.e. C_a(α)∩Ω_{a+1}=ψ_a α). Clean Citer-stage induction;
  KEY non-circularity: ψ-generator ψ_u(ξ) with bound forces u≤a; u=a case has
  ξ<α AND ξ∈C_a(α) (it's a Citer member!), so Cset_psi_closed gives ψ_a ξ∈C_a(α)
  ⟹ ψ_a ξ≠ψ_a α ⟹ <. Gives SBC for the β<Ω_{a+1} region directly (β∈C_a(β),
  β<Ω_{a+1} ⟹ β<ψ_a β ⟹ ξ<β<ψ_a β ⟹ ξ∈C_a(β) ⟹ clean case). **β≥Ω_{a+1} (e.g.
  oV b=ψ_{a+1}(0)) still needs the higher-band recursion = the genuine core.**

**SBC status — successor case PROVABLE, LIMIT case = the irreducible nut:**
Proof of SBC (β∈C_a(β), ξ<β, suppose ψ_a ξ=ψ_a β=:W): if ξ∈C_a(β) then
Cset_psi_closed gives W=ψ_a ξ∈C_a(β) ⊥ psi_notMem. So ξ∉C_a(β), W≤ξ<β, and
∀γ∈[ξ,β) noncanon (γ∈C_a(γ) would give psi_strict_mono_arg γ<β ⟹ ψ_a γ<ψ_a β,
but ψ_a γ=W=ψ_a β by collapse on [ξ,β)).
- **β=δ+1 (succ): DONE-able.** δ∈[ξ,β) noncanon (δ∉C_a(δ)). `Cset_succ_eq` ⟹
  C_a(δ+1)=C_a(δ), so β=δ+1∈C_a(β)=C_a(δ). Then **`succ_mem`** (clean Citer-stage
  lemma, UNPROVEN-but-easy: `x+1∈C_v(α) → x∈C_v(α)`; base downward-closed; sum
  case z must be succ since x+1 succ, peel via Cset_add_closed; ψ-case: ψ value
  additive-principal+succ ⟹ =1 ⟹ x=0∈base) gives δ∈C_a(δ) ⊥ δ noncanon.
- **β limit: OPEN (genuine Buchholz core).** Continuity: β∈C_a(β)=⋃_{δ<β}C_a(δ),
  take δ∈[ξ,β), β∈C_a(δ), δ noncanon, W=ψ_a δ≤δ<β, β>ψ_a δ. Derived structural
  fact (useful, unproven): **C_a(δ)∩[ψ_a δ, Ω_{a+1}) = ∅** — members ≥ψ_a δ need a
  ψ_{u>a} summand (≥Ω_{a+1}); sums of <ψ_a δ stay <ψ_a δ (additive-principal);
  ψ_{u≤a} gen ≤... <ψ_a δ. So if β<Ω_{a+1} we'd get β∈ the empty gap ⊥. BUT β may
  be ≥Ω_{a+1} (big canonical), where C_a(δ) legitimately has large members ⟹ no
  contradiction by this argument. ⟹ limit case needs the FULL band-recursive
  simultaneous induction (handle u>a bands), = Buchholz's actual 1.9 proof. This
  is the multi-session core; collapse_le is its succ-engine prerequisite.
NEXT: (i) land `succ_mem` (clean) + SBC-successor as standalone if useful; (ii)
crack SBC-limit via band-recursion or read Buchholz 1986 §1 1.9 C-rank induction
(NOT tsize) for the exact limit handling; (iii) then arg_extract→NEC→psi_proj.
