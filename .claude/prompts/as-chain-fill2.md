# as-chain-fill2 — close the last 2 chaining sorries (links-to-target + telescoping)

You are a Lean 4 proof subagent on branch `as/chain-fill2` (based on `as/chain-piq`). Project:
**StatLean** — read `CLAUDE.md` (§2,§6,§7). `srun`: plain `lake build`, ITERATE to GREEN. Never
`lake update`. The π_q scaffold + helpers are BUILT and proved; only 2 named lemmas remain `sorry`.
Close them; do NOT re-isolate or restructure the scaffold.

## Touch-set (edit ONLY this file)
`StatLean/AsymptoticStatistics/EmpiricalProcess/Maximal.lean`. The 2 sorries:

### Sorry 1 — `chain_links_le_target` (~L2340, MECHANICAL — do first)
```
(∫⁻ ξ, supNormOver F (G_n (π 0 f)) ∂μ) + ∑' q, ∫⁻ ξ, supNormOver F (G_n (π(q+1)f − π q f)) ∂μ
  ≤ 2·(∑' q, ofReal(δq/2^{q+1}) · √log(bN(δq/2^q)))  +  2·√n·∫⁻|Φ|·𝟙{δq√n<|Φ|}
```
The proved helpers give, for each `q`, `∫⁻ supNormOver F (G_n(π(q+1)f−π q f)) ≤ K·(δq/2^q)·√log(1+N_q·N_{q+1})`
(the finite-family link level bound, already proved as a `private` lemma — find it, name likely
`chain_link_level_bound`/similar). Steps:
- bound the `∑' q` termwise (`ENNReal.tsum_le_tsum`) by `∑' q, K·(δq/2^q)·√log(1+N_q·N_{q+1})`;
- fold `√log(1+N_q·N_{q+1}) ≤ √log(N_q²·… ) ≤ 2·√log N_q` (for `N_q,N_{q+1} ≥ 1`; `Real.log` monotone,
  `Real.sqrt` monotone) and the constant `K`, plus the index shift `δq/2^q = 2·(δq/2^{q+1})`, into
  `2·(∑' q, ofReal(δq/2^{q+1})·√log N_q)`. (Reindex/`tsum` comparison; the `bN(δq/2^q)` in the target
  via `ENat.recTopCoe` equals `N_q` since `hN_fin`.)
- the `π 0` term: it's the `q=0`-scale link from the coarsest bracket — bound it by (a multiple of) the
  `q=0` summand or `tight_chain_level_bound` at scale `δq`, absorbed into the constant `2`;
- add `tight_envelope_truncation_bound` for the `+2·√n·tail`.
This is finite/algebraic given the proved per-level bound. If the constant won't close at literal `2`,
it MUST (the target is fixed) — push the `√2`/`K` folding and the `∑ δq/2^{q+1} = δq` slack.

### Sorry 2 — `chain_telescope_reconstruction` (~L2299, THE DEEP STEP)
```
∫⁻ ξ, supNormOver F G_n ∂μ
  ≤ (∫⁻ ξ, supNormOver F (G_n (π 0 f)) ∂μ) + ∑' q, ∫⁻ ξ, supNormOver F (G_n (π(q+1)f − π q f)) ∂μ
```
Roadmap:
1. **Per-`f`, per-`ξ` telescoping identity.** `π q f → f` in `L²(P)` is proved (the
   `chainPi_l2_tendsto`/bracket-width helper); `chaining_l2_slice_pointwise_bound` ⇒
   `G_n(π q f) ξ → G_n f ξ`. The finite telescoping `G_n(π Q f) = G_n(π 0 f) + ∑_{q<Q} G_n(π(q+1)f−π q f)`
   is `Finset.sum_range_succ`-style; take `Q→∞` ⇒ `G_n f = G_n(π 0 f) + ∑' q, G_n(π(q+1)f − π q f)`
   (the tsum converges because the partial sums → `G_n f − G_n(π 0 f)`). So pointwise
   `|G_n f ξ| ≤ |G_n(π 0 f) ξ| + ∑' q, |G_n(π(q+1)f − π q f) ξ|`.
2. **⨆ over `F` (subadditivity).** `supNormOver F (G_n) = ⨆ f∈F, ofReal|G_n f|`. From step 1 +
   `ofReal` mono + `ofReal_add` + `ENNReal.iSup_add_iSup_le`/`iSup_le`:
   `supNormOver F G_n ≤ supNormOver F (G_n∘π_0) + ⨆ f∈F, ∑' q, ofReal|G_n(link_q f)|`, and
   `⨆ f ∑' q (…) ≤ ∑' q ⨆ f (…)` (`iSup`–`tsum` interchange, `ENNReal.iSup_tsum_le`/`tsum_iSup` —
   search the exact name; for `ℝ≥0∞` the `⨆∑ ≤ ∑⨆` direction holds). ⇒
   `supNormOver F G_n ≤ supNormOver F (G_n∘π_0) + ∑' q, supNormOver F (G_n∘link_q)`.
3. **`∫⁻` (monotone + additive).** `lintegral_mono` step 2, then `lintegral_add_left`/
   `lintegral_tsum` (need measurability of `ξ ↦ supNormOver F (G_n∘link_q)` — PROVED in the scaffold)
   ⇒ the target.
If step 1's tsum-convergence/identity genuinely resists, isolate JUST that as ONE named `private`
`sorry` (`chain_telescope_pointwise`) and prove steps 2–3 from it. Aim for 0-sorry.

## Constraints
No `axiom`/`admit`; reuse the proved scaffold/helpers; named `private` helpers only. **Finish on
`lake build StatLean.AsymptoticStatistics.EmpiricalProcess.Maximal` exit 0.** Commit to `as/chain-fill2`
(`as(empirical): close chain_links_le_target + chain_telescope_reconstruction`).

## DONE
Build exits 0. Report: build status, final sorry count (0 ideal), which of the 2 closed, and any
residual named debt.
