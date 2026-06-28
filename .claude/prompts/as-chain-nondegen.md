# as-chain-nondegen — add the non-triviality hypothesis (LAPTOP-APPROVED) + close both chaining lemmas

You are a Lean 4 proof subagent on branch `as/chain-nondegen` (based on `as/chain-final`). Project:
**StatLean** — read `CLAUDE.md` (§2,§6,§7). `srun`: plain `lake build`, ITERATE to GREEN 0-sorry.
Never `lake update`. The π_q scaffold + helpers are PROVED; existential chain constants are in place.
A prior pass correctly diagnosed that the tight bound is **UNSOUND for L²-degenerate `F`** (singleton:
all `bracketingNumber = 1` ⇒ RHS `∑√log N_q = 0` but LHS `|G_n f| > 0`; counterexample documented in
`chain_links_le_target`'s docstring). **The laptop has APPROVED the fix: add a non-triviality
hypothesis.** Your job: add it and close BOTH remaining `sorry`s.

## Touch-set (edit ONLY this file): `…/EmpiricalProcess/Maximal.lean`

### Step 1 — add the non-triviality hypothesis to the chain
To `chain_links_le_target`, `chain_telescope_reconstruction` (if it needs it), `chaining_dyadic_sum_finiteCover`,
`tight_supNorm_chaining_dyadic_sum`, `tight_supNorm_chaining_bound`, and **`tight_maximal_inequality`**,
add a hypothesis ruling out the degenerate case. Use whichever is cleanest to thread AND suppliable by a
non-degenerate class:
  `(hNontriv : ∀ q : ℕ, 2 ≤ bracketingNumber (δq / 2 ^ q) F 2 P)`
(per-scale `N_q ≥ 2`, so `√log N_q ≥ √log 2 > 0`). If a single `hJ_pos : ∀ δ' > 0, 0 < bracketingEntropyIntegral δ' F P`
is easier to consume, use that and DERIVE `N_q ≥ 2` from it where needed — but `hNontriv` (per-scale)
is the direct form. **This hypothesis is supplied downstream:** the framework
`isPDonsker_of_finite_bracketing_entropy_integral` already carries `hJ_pos`, and the half-line class has
`halfLineClass_J_pos` proved — so adding it does NOT block the de-laundering (a later unit threads it).

### Step 2 — close `chain_links_le_target` (now SOUND with `hNontriv`)
With `N_q ≥ 2`: `√log N_q ≥ √log 2 > 0`, so the RHS dyadic sum `∑_q (δq/2^{q+1})·√log N_q ≥ √log 2 ·
∑_q δq/2^{q+1} = √log 2 · δq/2 > 0` — the RHS no longer collapses. The π_0 term and each link term
(via the PROVED per-level helper `K·(δq/2^q)·√log(1+N_q·N_{q+1})`) fold into the existential `C₁·(∑_q …)`
(`√log(1+N_q N_{q+1}) ≤ 2√log N_q` etc.); envelope tail via `tight_envelope_truncation_bound`. The
counterexample is excluded, so the bound holds; close it 0-sorry with the existential constants.

### Step 3 — close `chain_telescope_reconstruction` (the a.e.-pointwise telescoping)
`∫⁻ supNormOver F G_n ≤ ∫⁻ supNormOver F (G_n∘π_0) + ∑' q ∫⁻ supNormOver F (G_n∘link_q)`. Use the A.E.
route (NOT L²): `empiricalProcess P n (X·ξ) f = √n·((1/n)∑_i f(X_i ξ) − ∫f dP)` is LINEAR in `f` and
depends on `f` only via the finite sample + `∫f dP`. `π_Q f → f` a.e.-`P` (bracket `P`-width →0), so
`(1/n)∑_i π_Q f(X_i ξ) → (1/n)∑_i f(X_i ξ)` a.s. (finite sum, a.e. each point) and `∫π_Q f dP → ∫f dP`
(dominated, `|π_Q f|≤1`) ⇒ `G_n(π_Q f) ξ → G_n f ξ` a.s. Finite telescoping `G_n(π_Q f) = G_n(π_0 f)
+ ∑_{q<Q} G_n(π_{q+1}f − π_q f)` via `Finset.sum_range_succ` + `empiricalProcess` linearity in `f`
(prove the linearity helper `empiricalProcess … (a−b) = empiricalProcess … a − empiricalProcess … b`).
Limit ⇒ `|G_n f| ≤ |G_n(π_0 f)| + ∑' q |G_n(link_q f)|`; then `supNormOver` = `⨆ f∈F ofReal|·|`,
`⨆`-subadditivity + `⨆∑ ≤ ∑⨆` (`ENNReal`) + `lintegral_mono`/`lintegral_add`/`lintegral_tsum`
(link-sup measurability PROVED). Aim 0-sorry; if the a.e. limit alone resists, isolate JUST it as one
named `private` `sorry` and prove the rest.

## Constraints
No `axiom`/`admit`; do NOT touch DonskerBracketing.lean / the leaves; named `private` helpers. **Finish
on `lake build StatLean.AsymptoticStatistics.EmpiricalProcess.Maximal` exit 0.** Commit to
`as/chain-nondegen` (`as(empirical): non-triviality hyp + close chaining 0-sorry (vdV 19.34, loose const)`).

## DONE
Build exits 0; **0 sorry** is the goal. Report: build status, final sorry count, the exact non-triviality
hypothesis added (so I thread it in de-laundering), and confirm both lemmas closed.
