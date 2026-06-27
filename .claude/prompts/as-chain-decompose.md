# as-chain-decompose — decompose & fill the chaining core; isolate ONLY the telescoping

You are a Lean 4 proof subagent on branch `as/chain-dec` (based on `as/chain-dyadic`). Project:
**StatLean** — read `CLAUDE.md` (§2,§6,§7). In an `srun` allocation: plain `lake build`, ITERATE to
GREEN. Never `lake update`. **Your job is to BUILD the mechanical steps, not just re-isolate.** Prior
passes kept restating the whole core as one `sorry`; this time you must DECOMPOSE into the named
sub-lemmas below, prove the mechanical ones, and leave AT MOST the single telescoping lemma `sorry`.

## State (reuse; do not redo)
`StatLean/AsymptoticStatistics/EmpiricalProcess/Maximal.lean` has `chaining_dyadic_sum_finiteCover`
(~L2245, body = 1 `sorry`) — the finite-cover case (`hN_fin : ∀ q, bracketingNumber (δq/2^q) F 2 P ≠ ⊤`).
Proved & reusable: `bracketing_dyadicComparison_le`, the three leaves (`tight_chain_level_bound`,
`tight_chain_telescope_bound`, `tight_envelope_truncation_bound`), `chaining_envelope_from_bracket`,
`chaining_l2_slice_pointwise_bound`, `finite_sup_bound`, `Bracketing.lean`'s
`bracketingNumber`/`HasFiniteBracketingCover`/`IsEpsBracket`.

## Touch-set (edit ONLY this file)
Replace the single `sorry` of `chaining_dyadic_sum_finiteCover` with a proof that calls these NEW
named `private` sub-lemmas (define them just above it; stub each with `sorry`, then fill 1,2,4):

**Sub-lemma 1 — `chaining_piq_def` + `chaining_piq_supNorm_measurable` (BUILD).**
From `hN_fin q`, `bracketingNumber (δq/2^q) F 2 P` is a finite `N_q`; obtain a minimal finite
`(δq/2^q)`-bracket cover via `HasFiniteBracketingCover` (it's the `⨅` witness — use `Nat.find`/
`Classical.choice`). Define `π q f := l_{σ_q f}` where `σ_q f` = least bracket index containing `f`.
Prove `ξ ↦ supNormOver F (fun f => empiricalProcess P n (X·ξ) (π q f))` and the link version
`ξ ↦ supNormOver F (fun f => empiricalProcess P n (X·ξ) (π (q+1) f - π q f))` are `Measurable`/
`AEStronglyMeasurable`: each is a FINITE `⨆_{i<N_q}` (resp. `⨆_{i<N_q, j<N_{q+1}}`) of measurable
`ξ ↦ empiricalProcess … (fixed bracket fn)`, so `Finset.measurable_biSup`/`measurable_iSup`. **Finite,
mechanical.**

**Sub-lemma 2 — `chaining_link_level_bound` (BUILD, via the leaf).**
`∫⁻ ξ, supNormOver F |G_n(π(q+1)·−π q·)| ∂μ ≤ K·(δq/2^q)·√log(1+N_q)`. The link class is the FINITE set
`{π(q+1)f − π q f : f∈F}` (≤ `N_q·N_{q+1}` functions), `L²`-norm `≤ 2·δq/2^q`, sup post-truncation
`≤ √n·(δq/2^{q+1})/(1+√log(1+N_{q+1}))`; feed to `tight_chain_level_bound`. **Mechanical given Sub-lemma 1.**

**Sub-lemma 3 — `chaining_telescope_reconstruction` (THE DEEP ONE — attempt, else leave as the SOLE sorry).**
`∫⁻ ξ, supNormOver F G_n ∂μ ≤ (∑' q, ∫⁻ supNormOver F |G_n(π(q+1)·−π q·)|) + (the π_0 / envelope-tail term)`.
Pointwise: `G_n f = G_n(π_0 f) + ∑_q G_n(π(q+1)f − π q f)` because `π_q f → f` in `L²(P)` (bracket width
`→0`) ⇒ `G_n(π_q f) → G_n f` (`chaining_l2_slice_pointwise_bound` gives `G_n`'s `L²`-Lipschitz control);
then `supNormOver F`-subadditivity + `lintegral_tsum`. If this resists, leave `chaining_telescope_reconstruction`
as the ONLY `sorry` with a precise docstring — that is a MUCH smaller, sharper debt than the current whole
core, and is the genuine win for this pass.

**Sub-lemma 4 — assemble `chaining_dyadic_sum_finiteCover` (BUILD).**
Combine: Sub-lemma 3 bounds the LHS by `∑_q (link bound) + tail`; Sub-lemma 2 bounds each link by
`K·(δq/2^q)·√log(1+N_q)`; fold `√log(1+N_q) ≤ √2·√log N_q` (`Real.log`-monotone, `1+N_q ≤ N_q²` for
`N_q≥1`) and the leaf constant `K` into the target's `2·(∑ (δq/2^{q+1})·√log N_q)`; add
`tight_envelope_truncation_bound` for `+2√n·tail`. **Mechanical given 2,3.** Verify the constant closes
to `2` (the dyadic sum `∑ δq/2^{q+1} = δq` gives slack); if not literally `2`, you may NOT change the
target here (it's fixed by `tight_maximal_inequality`) — absorb into the `√2`/`K` folding.

## Outcome targets (in priority order)
- BEST: all four built ⇒ `chaining_dyadic_sum_finiteCover` 0-sorry ⇒ whole file 0-sorry.
- GOOD (expected): Sub-lemmas 1,2,4 built; ONLY `chaining_telescope_reconstruction` left as 1 named
  `sorry`. This is real progress (the deepest step isolated; everything else proved).
- Do NOT regress to "whole core is one sorry" — that wastes the pass.

## Constraints
No `axiom`/`admit`; reuse the leaves; named `private` helpers. **Finish on `lake build
StatLean.AsymptoticStatistics.EmpiricalProcess.Maximal` exit 0.** Commit to `as/chain-dec`
(`as(empirical): decompose chaining core — π_q+level+assembly built, telescoping isolated`).

## DONE
Build exits 0. Report: build status, final sorry count + WHICH sub-lemma(s) remain `sorry` (target:
only `chaining_telescope_reconstruction`), and confirm Sub-lemmas 1,2,4 are proved.
