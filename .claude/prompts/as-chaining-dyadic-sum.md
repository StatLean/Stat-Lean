# as-chaining-dyadic-sum — close the LAST sorry: tight_supNorm_chaining_dyadic_sum

You are a Lean 4 proof subagent on branch `as/chain-dyadic` (based on `as/maximal-tight-fill`).
Project: **StatLean** — read `CLAUDE.md` (§2,§6,§7). In an `srun` allocation: plain `lake build`,
ITERATE to GREEN 0-sorry. Never `lake update`.

## State (3 prior passes got us here — DO NOT redo these)
`StatLean/AsymptoticStatistics/EmpiricalProcess/Maximal.lean`:
* `tight_maximal_inequality` + `tight_supNorm_chaining_bound` — PROVED modulo the ONE lemma below.
* `bracketing_dyadicComparison_le` — PROVED 0-sorry (`∑_q (δq/2^{q+1})·√log N_[](δq/2^q) ≤ 2·J_[](δq)`).
* The three leaves PROVED: `tight_chain_level_bound`, `tight_chain_telescope_bound`,
  `tight_envelope_truncation_bound`. Helpers `chaining_envelope_from_bracket`,
  `chaining_l2_slice_pointwise_bound`, `finite_sup_bound`.

## Touch-set (edit ONLY this file) — the single remaining `sorry`
`tight_supNorm_chaining_dyadic_sum` (~L2245, sorry at ~L2270): for iid `X`, envelope `Φ`, `δq>0`,
`n≥1`,
```
∫⁻ ξ, supNormOver F (G_n) ∂μ
  ≤ 2·(∑' q, (δq/2^{q+1})·√log N_[](δq/2^q, F, L²P)) + 2·√n·∫⁻|Φ|·𝟙{δq√n<|Φ|} ∂P
```
(the `√log N` via `ENat.recTopCoe`). `tight_supNorm_chaining_bound` already feeds this through
`bracketing_dyadicComparison_le` to get the `2·J_[](δq)` form, so closing THIS finishes the file.

## The construction (vdV §19.6 dyadic chaining — decompose into named `private` sub-lemmas, fill bottom-up)
**First, the `⊤` shortcut:** if `bracketingNumber (δq/2^q) F 2 P = ⊤` for some `q`, the RHS sum is `⊤`
(`ENat.recTopCoe ⊤`), so `le_top` closes it. So assume all `N_q := bracketingNumber (δq/2^q) F 2 P`
finite (handle via `rcases` on `= ⊤`).

1. **`π_q` measurable selection (the key brick).** At scale `ε_q = δq/2^q` take a minimal finite
   `ε_q`-bracket cover `{[l_i^q, u_i^q]}_{i<N_q}` (from `bracketingNumber` being the `⨅`; obtain the
   witness with `Nat.find`/`Classical.choice` on `HasFiniteBracketingCover`). Define `π_q : (Ω→ℝ) →
   (Ω→ℝ)` sending `f ↦ l_{σ(f)}^q` where `σ(f)` is the least `i` with `f ∈ [l_i^q,u_i^q]`. The point:
   `π_q` takes only `N_q` VALUES, so `f ↦ G_n(π_q f)` and `supNormOver F (G_n ∘ π_q)` reduce to a
   **finite** `⨆_{i<N_q}`, which is `Measurable`/`AEStronglyMeasurable` in `ξ` (finite sup of
   measurables — `Finset.measurable_iSup`). This is the `AEStronglyMeasurable` gap; it is FINITE, not
   over all of `F`.
2. **Per-level link bound.** The link `π_{q+1}f − π_q f` lies in a finite class of `≤ N_q·N_{q+1}`
   functions, with `L²`-norm `≤ ε_q + ε_{q+1} ≤ 2ε_q` and (post-truncation at `√n·ε_{q+1}`) sup
   `≤ √n·ε_{q+1}/(1+√log(1+N_{q+1}))`. Apply `tight_chain_level_bound` ⇒
   `∫⁻ supNormOver (links) |G_n| ≤ K·ε_q·√log(1+N_q)`.
3. **Telescoping identity.** Pointwise in `ξ` and `f`: `G_n(f) = G_n(π_{Q}f) + ∑_{q<Q}
   G_n(π_{q+1}f − π_q f)` and `π_Q f → f` in `L²(P)` as `Q→∞` (bracket width `ε_Q→0`), giving
   `G_n(π_Q f) → G_n(f)` so `G_n(f) = G_n(π_0 f) + ∑_{q} G_n(π_{q+1}f − π_q f)` (use
   `chaining_l2_slice_pointwise_bound` for the `G_n`-continuity-in-`L²` step if it provides it).
   Take `supNormOver F`, then `⨆`-subadditivity + `lintegral_tsum`/`lintegral_iSup` ⇒
   `∫⁻ supNormOver F G_n ≤ ∑_q ∫⁻ supNormOver(links_q) |G_n|`. The `π_0` term is absorbed (it's the
   `q=0` link from the trivial coarsest bracket, or bound it by the `q=0` summand).
4. **Assemble** steps 2,3 ⇒ `∫⁻ supNormOver F G_n ≤ ∑_q K·ε_q·√log(1+N_q)`, fold the constant `K`
   and the `√log(1+N_q)` vs `√log N_q` (use `Real.log` monotonicity; `1+N_q ≤ N_q²` for `N_q≥1` so
   `√log(1+N_q) ≤ √2·√log N_q`) into the stated `2·(∑ (δq/2^{q+1})√log N_q)`; add the envelope tail
   via `tight_envelope_truncation_bound` for the `+2√n·tail`.

The constant `2`: the leaves carry universal constants (`finite_sup_bound`'s sub-Gaussian `K`,
`tight_envelope_truncation_bound`'s `×4`). The `2`-normalization holds because the dyadic sum
`∑ δq/2^{q+1} = δq` leaves slack; verify the arithmetic closes to `≤ 2·(…)`. If the literal `2` is
genuinely unattainable and the honest constant is some explicit `C`, you MAY change BOTH this lemma's
and `tight_maximal_inequality`'s stated constant to `C` consistently (and note it) — but check that
`chaining_integral_universal_K`'s use site (DonskerBracketing, where `hChainBound_outer` is consumed)
only needs *a* finite constant, so any explicit `C` is fine downstream.

## Fallback (last resort)
If the telescoping `L²`-convergence (step 3) genuinely resists, isolate JUST that as ONE named
`private` sorry lemma `chaining_telescope_L2_reconstruction` with a precise statement, and prove
everything else — that is the single deepest measure-theoretic step. But aim for 0-sorry.

## Constraints
No `axiom`/`admit`; do not weaken the leaves or `tight_maximal_inequality`'s role. Named `private`
helpers. **Finish on `lake build StatLean.AsymptoticStatistics.EmpiricalProcess.Maximal` exit 0.**
Commit to `as/chain-dyadic`
(`as(empirical): close tight_supNorm_chaining_dyadic_sum — π_q selection + telescoping, 0-sorry`).

## DONE
`lake build StatLean.AsymptoticStatistics.EmpiricalProcess.Maximal` exits 0; **0 sorry**. Report build
status, sorry count, and whether the constant stayed `2` or changed to an explicit `C`.
