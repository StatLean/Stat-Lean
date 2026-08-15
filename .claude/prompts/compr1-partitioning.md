# Lane D — comp/r1-partitioning: jackknife + bias reduction + holdout + K-fold

READ `.claude/prompts/compr1-_common.md` FIRST and obey every shared rule.

## Touch-set (the ONLY files you may modify)

1. `StatLean/ComputationalStatistics/Resampling/Jackknife.lean`
2. `StatLean/ComputationalStatistics/Resampling/JackknifeBias.lean`
3. `StatLean/ComputationalStatistics/Partitioning/Holdout.lean`
4. `StatLean/ComputationalStatistics/Partitioning/KFold.lean`
(+ `LANE-REPORT.md`)

Build gate: `lake build` of those four modules (one line).

You may USE (compiling, possibly still sorried):
`ForMathlib/PiMoments.lean` (`integral_avg_eval_pi`),
`ForMathlib/PiMarginal.lean` (`pi_map_precomp_succAbove`, `pi_map_deleteSplit`).

## Targets and proof sketches

### Jackknife (pure `Fin`-sum algebra — no measure theory; do first)

- `jackknifed_eq` (eq. (3.8)): unfold; `Finset.sum_sub_distrib`,
  `Finset.sum_const`, `Finset.mul_sum`; `((n:ℝ)+1)⁻¹ * ((n+1) * A - n * Σ) …` —
  `field_simp` with `((n:ℝ)+1) ≠ 0` (`Nat.cast_add_one_ne_zero` or
  `positivity`-derived) then `ring`.
- `jackknifed_eq_sub_biasEstimate` (eq. (3.12)): rewrite with `jackknifed_eq`;
  unfold `jackknifeBiasEstimate`; `ring`.
- `jackknifePseudoValue_mcEstimate`: unfold everything;
  `(n+1) * ((n+1))⁻¹ * Σ_all − n * (n)⁻¹ * Σ_deleted`; kill the inverses
  (`mul_inv_cancel₀`; for the `n = 0` corner of `n * (n:ℝ)⁻¹` note the deleted
  sum over `Fin 0` is `0`, so the term vanishes either way — case
  `rcases Nat.eq_zero_or_pos n` if needed); then
  `Fin.sum_univ_succAbove (fun k => g (x k)) i` : `Σ_all = g (x i) + Σ_deleted`.
- `jackknifed_mcEstimate`: sum the previous over `i`: pseudovalues are
  `g (x i)`, so `jackknifed = ((n+1))⁻¹ Σ g(xᵢ) = mcEstimate g x`
  (mind `mcEstimate`'s cast: `((n+1 : ℕ) : ℝ)` vs `(n:ℝ)+1` — `push_cast`).
- `jackknifeVariance_mcEstimate`: rewrite pseudovalues and jackknifed by the
  two previous lemmas; the summand becomes `(g (x i) − mcEstimate g x)²`.

### JackknifeBias

- `integral_jackknifeMean`: unfold; swap integral and finite sum
  (`integral_finset_sum` — integrability of each
  `fun x => T' (jackknifeDelete i x)` from `hT'` transported along
  `pi_map_precomp_succAbove` via `Integrable` of a map — search
  `MeasureTheory.integrable_map_measure` / `Integrable.comp_measurable`;
  note `jackknifeDelete i x = x ∘ i.succAbove` definitionally). Each summand:
  `∫ T' (x ∘ i.succAbove) ∂P^{n+1} = ∫ T' ∂((P^{n+1}).map (· ∘ i.succAbove))
  = ∫ T' ∂P^n` by `integral_map` (AEMeasurable of the precomposition:
  `measurable_pi_lambda _ fun j => measurable_pi_apply _`) +
  `pi_map_precomp_succAbove`. Then `((n+1))⁻¹ * (n+1) * ∫T' = ∫T'`.
- `integral_jackknifed`: rewrite `jackknifed_eq` under the integral
  (`integral_congr` is overkill — `simp only [jackknifed_eq]`), then
  `integral_sub`/`integral_const_mul` (integrability of `jackknifeMean T'`
  from the summand integrability above) + `integral_jackknifeMean`.
- `jackknife_bias_reduction`: plug `hTn`, `hTn'` into `integral_jackknifed`;
  pure field algebra:
  `(n+1)(θ + a₁/(n+1) + a₂/(n+1)²) − n(θ + a₁/n + a₂/n²)
   = θ + a₂(1/(n+1) − 1/n) = θ − a₂/((n+1)n)`.
  `field_simp` with `(n:ℝ) ≠ 0` (from `NeZero n`) and `(n:ℝ)+1 ≠ 0`; `ring`.

### Holdout

- `holdout_unbiased`: this is `integral_avg_eval_pi` at `g := ℓ h` verbatim
  (unfold `mcEstimate`, `predictionRisk`).
- `holdout_integrated`: `Measure.integral_prod` (Fubini for the product of two
  probability measures; needs `hint`) → inner integral over the test block is
  `holdout_unbiased` at `h := A s` (using `hloss s`); conclude with
  `integral_congr_ae`/`Filter.EventuallyEq.integral` or plain `integral_congr`
  pointwise equality.

### KFold

- `loo_unbiased` (do before kFold — same skeleton, fewer layers): unfold
  `looEstimate`; `integral_finset_sum` (each summand integrable: transport
  `hint` along `pi_map_deleteSplit i` — the map
  `x ↦ (x i, x ∘ i.succAbove)`… CAREFUL: `pi_map_deleteSplit` produces the
  pair `(deleted coordinate, rest)` with the law `P ⊗ P^n`, while `hint` is
  stated on `(Fin n → Z) × Z` with law `(P^n) ⊗ P` — bridge with
  `Measure.prod_swap`/`integral_map` of `Prod.swap`, or transport through the
  map `x ↦ (x ∘ i.succAbove, x i)` and prove its law is `(P^n).prod P` by
  composing `pi_map_deleteSplit` with the swap: `Measure.map_map` +
  `Measure.prod_swap`). Each summand
  `∫ ℓ (A (x ∘ i.succAbove)) (x i) ∂P^{n+1}
   = ∫ p, ℓ (A p.1) p.2 ∂((P^n).prod P)` (by `integral_map` along that
  composite) `= ∫ s, ∫ z, ℓ (A s) z ∂P ∂P^n` (`Measure.integral_prod`, `hint`)
  `= ∫ s, predictionRisk D ℓ (A s) ∂P^n` — the same value for every `i`, so
  the outer `((n+1))⁻¹ Σ` collapses (`Finset.sum_const`, `card_univ`).
- `kFold_unbiased`: identical skeleton one type-level up: the base space is
  `W := Fin m → Z` with measure `Q := Measure.pi (fun _ => D)` (a probability
  measure — instance should be found automatically); folds live in
  `Fin (K+1) → W` with law `Q^{K+1}`; `jackknifeDelete k z = z ∘ k.succAbove`;
  apply the LOO argument with `(W, Q)` in place of `(Z, D)` and the inner
  statistic `fun (s, t) => mcEstimate (ℓ (A s)) t`; after Fubini the inner
  integral over the held-out fold `t ~ Q = P^m` is
  `∫ t, mcEstimate (ℓ (A s)) t ∂(pi_m D) = predictionRisk D ℓ (A s)` by
  `holdout_unbiased` (with `hloss s`, `[NeZero m]`).
