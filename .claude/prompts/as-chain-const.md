# as-chain-const — relax the over-tight constant, close links-to-target, attempt telescoping

You are a Lean 4 proof subagent on branch `as/chain-const` (based on `as/chain-piq`). Project:
**StatLean** — read `CLAUDE.md` (§2,§6,§7). `srun`: plain `lake build`, ITERATE to GREEN. Never
`lake update`. The π_q scaffold + helpers are PROVED; 2 lemmas remain `sorry`
(`chain_links_le_target` ~L2340, `chain_telescope_reconstruction` ~L2299). Close them.

## Root cause to fix FIRST: the literal constant `2` is too tight
The target chain (`tight_maximal_inequality`, `tight_supNorm_chaining_bound`,
`tight_supNorm_chaining_dyadic_sum`, `chaining_dyadic_sum_finiteCover`, `chain_links_le_target`) is
stated with literal `ENNReal.ofReal 2 *`. But the proved leaves carry universal constants
(`tight_chain_level_bound`'s `∃ K` from `finite_sup_bound`; `tight_envelope_truncation_bound`'s `×4`),
so the honest chained bound is `C₁·J + C₂·√n·tail` with `C₁ = 2K`, `C₂ = 4` (or similar) — NOT `2`.
`chain_links_le_target` cannot close at `2`. **Relax the constant throughout this file's chain to honest
explicit constants.**

### How to relax (touch-set = Maximal.lean ONLY)
Replace the two literal `ENNReal.ofReal 2 *` factors in EACH of `chain_links_le_target`,
`chaining_dyadic_sum_finiteCover`, `tight_supNorm_chaining_dyadic_sum`, `tight_supNorm_chaining_bound`,
and **`tight_maximal_inequality`** by explicit constants. Cleanest: introduce
`noncomputable def chainConst : ℝ := <the honest value, e.g. 2 * (finite_sup_bound's K) >` and
`chainTailConst : ℝ := 4`, OR state each as `∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∫⁻ … ≤ ofReal C₁ * J +
ofReal C₂ * (√n·tail)`. Prefer **two named `def` constants** so the statements stay clean and
`tight_maximal_inequality`'s conclusion is `ofReal chainConst * J + ofReal chainTailConst * (√n·tail)`.
Propagate the same constants up the chain (each lemma's `2` → the matching `chainConst`/`chainTailConst`).
**Note for the downstream de-laundering:** the framework hypothesis `hChainBound_outer`
(DonskerBracketing.lean) also has literal `2`; it will be relaxed/removed in a separate unit — you do
NOT touch DonskerBracketing.lean here, just make `tight_maximal_inequality` honest with `chainConst`.

## Sorry 1 — `chain_links_le_target` (now closeable with the honest constant)
With the relaxed `chainConst`/`chainTailConst`: termwise-bound `∑' q ∫⁻ supNormOver(link_q)` by
`∑' q K·(δq/2^q)·√log(1+N_q·N_{q+1})` (the proved per-level helper), fold
`√log(1+N_q·N_{q+1}) ≤ 2·√log N_q` and `K`, the `δq/2^q = 2·δq/2^{q+1}` shift, into
`chainConst·(∑' q (δq/2^{q+1})·√log N_q)`; the `π 0` term into the same; the envelope tail via
`tight_envelope_truncation_bound` into `chainTailConst·√n·tail`. With `chainConst` free, the arithmetic
closes.

## Sorry 2 — `chain_telescope_reconstruction` (the deep step; constant-independent)
`∫⁻ supNormOver F G_n ≤ (∫⁻ supNormOver F (G_n∘π_0)) + ∑' q ∫⁻ supNormOver F (G_n∘link_q)`. Per-`f`
telescoping `G_n f = G_n(π_0 f) + ∑' q G_n(link_q f)` (from the PROVED `π_q → f` in `L²` +
`chaining_l2_slice_pointwise_bound`); `ofReal`-mono + `⨆`-subadditivity + the `⨆∑ ≤ ∑⨆` interchange
(`ENNReal`) + `lintegral_tsum` (measurability of `ξ ↦ supNormOver(link_q)` is PROVED). If the
per-`f` tsum identity genuinely resists, isolate JUST it as one named `private` `sorry`
(`chain_telescope_pointwise`) and prove the rest. Aim for 0-sorry.

## Constraints
No `axiom`/`admit`; do NOT touch DonskerBracketing.lean or the proved leaves/helpers; named `private`
helpers / the two `chainConst` defs. **Finish on `lake build
StatLean.AsymptoticStatistics.EmpiricalProcess.Maximal` exit 0.** Commit to `as/chain-const`
(`as(empirical): honest chaining constant + close links-to-target; (attempt) telescoping`).

## DONE
Build exits 0. Report: build status, final sorry count, the honest `chainConst`/`chainTailConst`
values, which of the 2 closed, and any residual named debt (target: only `chain_telescope_pointwise`
if anything).
