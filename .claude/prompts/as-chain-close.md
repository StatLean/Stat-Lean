# as-chain-close — close the 2 chaining lemmas (hN2 now threaded): links-fold + telescoping

You are a Lean 4 proof subagent on branch `as/chain-close` (based on `hc/maximal-nondegen`). Project:
**StatLean** — read `CLAUDE.md` (§2,§6,§7). `srun`: plain `lake build`, ITERATE to GREEN 0-sorry.
Never `lake update`. The full π_q scaffold + helpers + the non-triviality hypothesis `hN2` are in
place (threaded through the chain by the laptop). **Two `sorry`s remain; close BOTH.**

## Touch-set (edit ONLY this file): `…/EmpiricalProcess/Maximal.lean`
First `lake build` to confirm the just-added `hN2` threading compiles. If there's a threading error
(e.g. the `hN2N`/`exact_mod_cast` derivation in `chaining_dyadic_sum_finiteCover`, or a call-site arg
order), FIX it minimally — the intended shape is: `chain_links_le_target` takes `(hN2 : ∀ q, 2 ≤ N q)`;
`chaining_dyadic_sum_finiteCover`/`tight_supNorm_chaining_dyadic_sum`/`tight_supNorm_chaining_bound`/
`tight_maximal_inequality` take `(hN2 : ∀ q, 2 ≤ bracketingNumber (δq/2^q) F 2 P)` and pass it down.

### Sorry 1 — `chain_links_le_target` (NOW SOUND via `hN2 : ∀ q, 2 ≤ N q`)
The L²-degenerate counterexample is excluded: `hN2 q : 2 ≤ N q` ⇒ `Real.log (N q) ≥ Real.log 2 > 0` ⇒
`√log N_q ≥ √log 2 > 0`, so the RHS dyadic sum `∑_q (δq/2^{q+1})·√log N_q ≥ √log 2 · δq/2 > 0` no longer
collapses. Close it: bound the `π_0` term and each link integral `∫⁻ supNormOver(link_q)` by the PROVED
per-level helper `K·(δq/2^q)·√log(1+N_q·N_{q+1})`, fold `√log(1+N_q·N_{q+1}) ≤ 2√log N_q` (uses
`N_q,N_{q+1} ≥ 1`) and the leaf constant `K` into the existential `C₁·(∑_q (δq/2^{q+1})·√log N_q)`;
envelope tail via `tight_envelope_truncation_bound` into `C₂·√n·tail`. Choose `C₁,C₂` large enough
(existential — the `hN2` lower bound on the RHS gives the slack to absorb the `π_0` term and the
constants). This is now provable; it was only blocked by the missing `hN2`.

### Sorry 2 — `chain_telescope_reconstruction` (the a.e.-pointwise telescoping)
Its signature already provides `π` and `hπ_L2 : ∀ f ∈ F, Tendsto (fun q => eLpNorm (f − π q f) 2 P)
atTop (𝓝 0)` (the L²-convergence, PROVED). Target:
`∫⁻ supNormOver F G_n ≤ ∫⁻ supNormOver F (G_n∘π_0) + ∑' q ∫⁻ supNormOver F (G_n∘link_q)`.
Route (A.E.-pointwise, NOT a fresh L² argument): `empiricalProcess P n (X·ξ) f` is LINEAR in `f` and
depends on `f` only via the `n` sample values + `∫f dP`. From `hπ_L2` (⇒ `π q f → f` in `L²`, hence a
subsequence a.e., and `∫π_q f dP → ∫f dP` by dominated convergence with `|π_q f| ≤ 1`), get
`empiricalProcess … (π q f) ξ → empiricalProcess … f ξ` for a.e. `ξ`; the finite telescoping
`G_n(π_Q f) = G_n(π_0 f) + ∑_{q<Q} G_n(π_{q+1}f − π_q f)` is `Finset.sum_range_succ` + `empiricalProcess`
linearity in `f` (prove the linearity helper if absent). Limit ⇒ `|G_n f| ≤ |G_n(π_0 f)| + ∑' q |G_n(link_q f)|`;
then `supNormOver` = `⨆ f∈F ofReal|·|`, `⨆`-subadditivity + `⨆∑ ≤ ∑⨆` (`ENNReal`) + `lintegral_mono`
+ `lintegral_add` + `lintegral_tsum` (link-sup measurability is PROVED in the scaffold).
If the a.e. limit alone resists, isolate JUST it as one named `private` `sorry`; but aim for 0-sorry.

## Constraints
No `axiom`/`admit`; do NOT touch DonskerBracketing.lean / the leaves / the `hN2` signatures (just USE
`hN2`); named `private` helpers. **Finish on `lake build StatLean.AsymptoticStatistics.EmpiricalProcess.Maximal`
exit 0.** Commit to `as/chain-close`
(`as(empirical): close chain_links_le_target (via hN2) + chain_telescope_reconstruction — chaining 0-sorry`).

## DONE
Build exits 0; **0 sorry**. Report: build status, final sorry count, confirm both lemmas closed (and
that the hN2 threading compiled / any fix you made), and the existential constants.
