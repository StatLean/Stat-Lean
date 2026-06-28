# as-chain-piq — BUILD the π_q scaffold inside chaining_dyadic_sum_finiteCover (prescriptive)

You are a Lean 4 proof subagent on branch `as/chain-piq` (based on `as/chain-dec`). Project:
**StatLean** — read `CLAUDE.md` (§2,§6,§7). `srun` allocation: plain `lake build`, ITERATE to GREEN.
Never `lake update`. **CRITICAL: prior passes kept re-isolating the whole construction as one `sorry`.
You must NOT do that. You must CREATE the named sub-definitions/lemmas below and PROVE the mechanical
ones. The decomposition is GIVEN — do not redesign it, type it in and fill it.**

## Touch-set (edit ONLY this file)
`StatLean/AsymptoticStatistics/EmpiricalProcess/Maximal.lean`. The lemma `chaining_dyadic_sum_finiteCover`
(~L2233) currently has body `sorry`. Build the scaffold below ABOVE it, then prove it by assembly.
Reusable & proved: `tight_chain_level_bound` (finite-class per-level leaf), `tight_chain_telescope_bound`,
`tight_envelope_truncation_bound`, `chaining_l2_slice_pointwise_bound` (G_n L²-Lipschitz:
`|G_n fhat − G_n ghat| ≤ C·δq` when `∫(fhat−ghat)² < δq²`), `bracketing_dyadicComparison_le`,
`finite_sup_bound`. Defs: `supNormOver F z := ⨆ f ∈ F, ENNReal.ofReal |z f|` (FunctionClass.lean:56);
`HasFiniteBracketingCover F ε r P := ∃ k l u, (∀ i, IsEpsBracket ε (l i) (u i) r P) ∧ (∀ f∈F, ∃ i, ∀ x,
l i x ≤ f x ∧ f x ≤ u i x)` (Bracketing.lean); `IsEpsBracket ε l u r P` includes `eLpNorm (u−l) r P <
ENNReal.ofReal ε`.

## The scaffold to TYPE IN (named `private`; stub proofs with `sorry`, then fill 1–4,6; isolate only 5)
Work `noncomputable`. Let `ε q := δq / 2 ^ q`. From `hN_fin q : bracketingNumber (ε q) F 2 P ≠ ⊤`,
`HasFiniteBracketingCover F (ε q) 2 P` holds (the `⨅` is `< ⊤`); `Classical.choice` it to get
`Nq q : ℕ`, `chainL q chainU q : Fin (Nq q) → Ω → ℝ` with the bracket + cover properties. Define the
selector `chainSel q f : Fin (Nq q) := Classical.choose (cover f hf)` (for `f ∈ F`) and
`chainPi q f : Ω → ℝ := chainL q (chainSel q f)`.

1. **`chainPi_bracket`** (mechanical): for `f ∈ F`, `∀ x, chainPi q f x ≤ f x ∧ f x ≤ chainU q (chainSel q f) x`,
   and `eLpNorm (fun x => f x − chainPi q f x) 2 P ≤ ENNReal.ofReal (ε q)` (from `chainPi q f ≤ f ≤ chainU`,
   so `|f − chainPi q f| ≤ |chainU − chainL|`, and the bracket's `eLpNorm < ε q`).
2. **`chainPi_link_le_finiteSup`** (mechanical, the key reduction): for every `f ∈ F`,
   `|empiricalProcess P n (X·ξ) (chainPi (q+1) f − chainPi q f)| ≤
    ⨆ (p : Fin (Nq (q+1)) × Fin (Nq q)), |empiricalProcess P n (X·ξ) (chainL (q+1) p.1 − chainL q p.2)|`
   (the link is one of the finitely many `chainL(q+1) j − chainL q i`). Hence
   `supNormOver F (fun f => empiricalProcess … (chainPi (q+1) f − chainPi q f) ξ) ≤
    ENNReal.ofReal (⨆ p, |…|)`, and `ξ ↦ ⨆ p, |…|` is `Measurable` (FINITE sup of measurables —
   `Finset.measurable_… ` / `measurable_iSup` over the Fintype `Fin _ × Fin _`).
3. **`chain_link_level_bound`** (mechanical, via the leaf): apply `tight_chain_level_bound` with
   `ι := Fin (Nq (q+1)) × Fin (Nq q)`, `g p := chainL (q+1) p.1 − chainL q p.2`, `ε := ε q`, checking
   `hg_bdd` (truncate; the bracket fns are envelope-bounded) and `hg_var` (`∫ g_p² ≤ (2 ε q)²` from
   step 1's `L²` bound), getting `∫⁻ supNormOver F |G_n(link_q)| ≤ K·(ε q)·√log(1 + Nq q · Nq (q+1))`.
4. **`chainPi_l2_tendsto`** (mechanical): `eLpNorm (fun x => f x − chainPi q f x) 2 P ≤ ofReal (ε q) → 0`
   as `q → ∞` (since `ε q = δq/2^q → 0`); hence by `chaining_l2_slice_pointwise_bound`,
   `empiricalProcess … (chainPi q f) ξ → empiricalProcess … f ξ`.
5. **`chain_telescope_reconstruction`** (THE DEEP STEP — attempt; if it resists leave it as the SOLE
   `sorry`, precisely typed): pointwise telescoping
   `empiricalProcess … f ξ = empiricalProcess … (chainPi 0 f) ξ + ∑' q, empiricalProcess … (chainPi (q+1) f − chainPi q f) ξ`
   (from step 4 + `chainPi 0` coarsest), then `supNormOver`-subadditivity (`⨆ f |a f + ∑ b q f| ≤
   ⨆ f |a f| + ∑ q ⨆ f |b q f|`) + `lintegral_tsum` ⇒
   `∫⁻ supNormOver F G_n ≤ ∫⁻ supNormOver F |G_n(chainPi 0 ·)| + ∑' q, ∫⁻ supNormOver F |G_n(link_q)|`.
6. **assemble `chaining_dyadic_sum_finiteCover`** (mechanical): bound the `chainPi 0` term and each
   `∫⁻ link_q` (step 3) by `K·(ε q)·√log(1+Nq q·…)`; fold `√log(1+Nq q·Nq(q+1)) ≤ √2·√log(Nq q)+…`
   and the leaf `K` into the target `2·∑ (ε(q+1))·√log(Nq q)`; add `tight_envelope_truncation_bound`
   for `+2√n·tail`. Match the stated RHS (its `bracketingNumber (ε q) F 2 P` via `ENat.recTopCoe`
   equals `Nq q` under `hN_fin`).

## Outcome (priority)
- BEST: all built ⇒ 0-sorry. GOOD (expected): 1,2,3,4,6 proved; ONLY `chain_telescope_reconstruction`
  (step 5) `sorry`. **Do NOT regress to a single whole-construction `sorry` — that fails the pass.**
  If a mechanical step needs a tiny side-lemma, make it a named `private` lemma, don't sorry the whole.

## Constraints
No `axiom`/`admit`; reuse the leaves; named `private` helpers. **Finish on `lake build
StatLean.AsymptoticStatistics.EmpiricalProcess.Maximal` exit 0.** Commit to `as/chain-piq`
(`as(empirical): build π_q scaffold + level bound + assembly; isolate telescoping (step 5)`).

## DONE
Build exits 0. Report: build status, final sorry count, and WHICH named sub-lemmas are proved vs
`sorry` (target: only `chain_telescope_reconstruction`).
