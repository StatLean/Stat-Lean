# Close the 2 sorries in MEstimator/ScoreSubGaussian.lean (GLM score sub-Gaussianity)

Lean 4 / Mathlib proof engineer on `StatLean` (read repo `CLAUDE.md`). Pin `v4.29.1`. ON the cluster.

## CRITICAL build discipline
- Check with **plain foreground** `lake build StatLean.HighDimensionalStatistics.MEstimator.ScoreSubGaussian`
  and read the output. **NEVER** background a build (`&`), **NEVER** `until pgrep`/`sleep` poll loops,
  **NEVER** nested `srun`/`sbatch`. When it shows 0 errors and 0 sorries, STOP.

## Scope
- **Only edit** `StatLean/HighDimensionalStatistics/MEstimator/ScoreSubGaussian.lean`. Keep signatures/docstrings.
- **READ FIRST** `StatLean/HighDimensionalStatistics/Lasso/RandomNoise.lean` — its `colInner_isSubGaussian`
  is the structural template for `score_coord_isSubGaussian` (sum of independent scaled sub-Gaussians,
  `HasSubgaussianMGF.sum_of_iIndepFun`, proxy monotonicity, centered ⇒ `IsSubGaussian`). Mirror it; the
  ONLY difference is the per-term sub-Gaussianity is *derived* here (gap 1) instead of assumed.

## Gap 1 — `score_term_hasSubgaussianMGF`: `Vᵢⱼ = (ψ'(ηᵢ) − yᵢ)·xᵢⱼ` is `HasSubgaussianMGF` with proxy `B²xᵢⱼ²`
`HasSubgaussianMGF X c` has two fields: `mgf_le : ∀ t, mgf X μ t ≤ exp (c·t²/2)` and
`integrable_exp_mul : ∀ t, Integrable (fun ω => exp (t·X ω)) μ`.
Let `η := linPred M.X M.θstar i`, `a := M.X i j`. The variable is `fun ω => (M.ψ' η − M.y i ω) * a`
`= fun ω => a*M.ψ' η + (-a) * M.y i ω` (a constant plus a scalar multiple of `yᵢ`).
- **MGF identity:** `mgf (fun ω => a*M.ψ' η + (-a)*M.y i ω) μ t`. Use `mgf` of `const + (c • yᵢ)`:
  `mgf (fun ω => k + Y ω) μ t = exp (t*k) * mgf Y μ t` (find it — `mgf_const_add`/compute from the
  integral `∫ exp(t*(k+Yω)) = exp(t k)∫exp(t Yω)`), and `mgf (fun ω => c * M.y i ω) μ t = mgf (M.y i) μ (c*t)`
  (`mgf_const_mul`/`mgf_smul_left`). With `c = -a`: `mgf (M.y i) μ (-a*t)`, then `M.hmgf i (-a*t)`:
  `= exp (ψ(η + (-a*t)) − ψ η)`. Combine: `mgf Vᵢⱼ μ t = exp (t*a*ψ' η) * exp (ψ(η − a*t) − ψ η)`
  `= exp (ψ(η + s) − ψ η − s*ψ' η)` with `s := -a*t` (since `t*a*ψ' η = -s*ψ' η`). Algebra: `Real.exp_add`, `ring`.
- **Bound:** `psi_taylor_upper M.ψ M.ψ' M.ψ'' M.B M.hψ' M.hψ'' M.hψ''_le η s` gives
  `ψ(η+s) − ψ η − s*ψ' η ≤ B²/2 * s²`, and `s² = a²t²`, so `mgf Vᵢⱼ μ t ≤ exp (B²/2 * (a²t²)) = exp ((B²a²)·t²/2)`
  (`Real.exp_le_exp`). That is `mgf_le` for proxy `⟨B²a², _⟩`.
- **Integrability:** `integrable_exp_mul`: `exp(t·Vᵢⱼ) = exp(t*a*ψ' η) * exp((-a*t)*yᵢ)`; the second factor
  is integrable because `mgf (M.y i) μ (-a*t)` exists finitely (it equals `exp(...)` by `M.hmgf`). Find the
  Mathlib route: `integrable_exp_mul_of_…` or derive from `M.hmgf` ⇒ `Integrable (fun ω => exp ((-a*t)*M.y i ω))`.
  If integrability resists, lift it to a named `private lemma … := … sorry` (single isolated debt) and finish the rest.

## Gap 2 — `score_coord_isSubGaussian`: `scoreCoord M j = (1/n)∑ᵢ Vᵢⱼ` sub-Gaussian, proxy `B²C²/n`
Mirror `colInner_isSubGaussian` (RandomNoise.lean):
- Independence of `{Vᵢⱼ}ᵢ`: from `M.hindep` (the `M.y i` are `iIndepFun`), `iIndepFun.comp` with
  `fun i x => (M.ψ' (linPred …) - x) * M.X i j` (measurable). Like RandomNoise `hY_indep`.
- Each `Vᵢⱼ` is `HasSubgaussianMGF` proxy `B²(M.X i j)²` (gap 1). `HasSubgaussianMGF.sum_of_iIndepFun`
  ⇒ `∑ᵢ Vᵢⱼ` has proxy `∑ᵢ B²(M.X i j)²`. Rescale by `1/n` (`HasSubgaussianMGF.const_mul`/`.smul`, proxy `×(1/n)²`)
  to get `scoreCoord` with proxy `(1/n²)·∑ᵢ B²(M.X i j)²`. Upgrade `≤ B²C²/n` via
  `hC : IsColumnNormalized M.X C` (i.e. `∑ᵢ (M.X i j)² ≤ n*C²`) + proxy monotonicity (RandomNoise `hproxy_le`).
- `scoreCoord` is centered (`Vᵢⱼ` centered ⇒ `IsSubGaussian` from `HasSubgaussianMGF` of the centered var):
  `unfold IsSubGaussian; simp [mean = 0]` — but the cleanest is RandomNoise's final move
  (`HasSubgaussianMGF` ⇒ mean 0, `isSubGaussian_iff` / `IsSubGaussian` unfold). Mind `scoreCoord`'s
  `(1/n) * ∑ …` shape vs `∑ (1/n)*…` — `Finset.mul_sum` to align.

Report the final `lake build` line (0 sorries) and `#print axioms score_coord_isSubGaussian` (note any isolated integrability debt).
