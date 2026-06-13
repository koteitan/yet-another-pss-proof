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
