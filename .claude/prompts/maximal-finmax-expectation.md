Read CLAUDE.md (repo root) first and obey it — §2, §6 (search tools), §7, §9, §10.
Use `./tools/where.sh`, `./tools/loogle.sh '"name"'`, `./tools/check.sh '<name>'`. Never `lake update`.

# CONTEXT
`StatLean/ConcentrationInequalities/Maximal/FiniteMaximal.lean` ALREADY EXISTS with:
- `theorem tail_max_le` — PROVEN (union-bound tail `μ{t < ⨆ⱼ Xⱼ} ≤ d·exp(−t²/2σ²)`).
- `theorem expectation_max_le` — currently a NAMED `sorry`: the expectation bound
  `∫ (fun ω => ⨆ j, X j ω) ∂μ ≤ σ * Real.sqrt (2 * Real.log d)` for `d ≥ 1` centered
  sub-Gaussian `X : Fin d → Ω → ℝ`, each `IsSubGaussian (X j) σ² μ`.

# TASK — CLOSE THE `expectation_max_le` sorry to ZERO sorry.
The whole file must build with ZERO sorries afterward. Do NOT touch `tail_max_le` (keep it) or any
other declaration's statement. Only fill in `expectation_max_le`'s proof (add private helper lemmas
above it if useful).

# PROOF (Lu-BDA §4.2, the Jensen + MGF argument)
For `λ > 0`:
  `exp(λ · E[max]) ≤ E[exp(λ·max)]`            (Jensen, `exp` convex — `add_pow_le`? no: use
       `Real.add_pow_le_pow_mul_pow_of_sq_le_sq`? NO. Use `ConvexOn.exp` + `ConvexOn.map_integral_le`
       / `MeasureTheory.integral_exp_le`-style, OR `Real.exp_le_… ` — search:
       `./tools/loogle.sh '"convexOn_exp"'`, `./tools/loogle.sh '"map_integral_le"'`,
       `./tools/loogle.sh '"jensen"'`; Mathlib `ConvexOn.map_centerMass_le` / `inner_le_weight_mul_Lp` —
       pick what gives `exp (∫ f) ≤ ∫ exp f` for a probability measure.)
  `E[exp(λ·max)] = E[maxⱼ exp(λ Xⱼ)] ≤ E[∑ⱼ exp(λ Xⱼ)] = ∑ⱼ E[exp(λ Xⱼ)] ≤ d · exp(λ²σ²/2)`
       (max ≤ sum of nonnegatives; linearity; per-`j` use `HasSubgaussianMGF.mgf_le` from
       `IsSubGaussian (X j)` — note `mgf` is `∫ exp(λ·(Xⱼ − E Xⱼ))`, and `E Xⱼ = 0` here so it equals
       `∫ exp(λ Xⱼ)`; integrability of each from `HasSubgaussianMGF.integrable_exp_mul`).
Taking `log` (monotone) and dividing by `λ > 0`:
  `E[max] ≤ log d / λ + λ σ² / 2`.
Optimize `λ = sqrt(2 log d / σ²)` (needs `σ² > 0`, `d ≥ 2` so `log d > 0`; handle `d = 1`/`σ = 0`
corners separately — for `d = 1`, `log 1 = 0` and `max = X₀` with `E X₀ = 0 = σ√0`; for `σ = 0`,
the bound is `≤ 0` and `X` is a.e. its mean `0`). Result: `E[max] ≤ sqrt(2 σ² log d) = σ sqrt(2 log d)`.

Key Mathlib bricks to confirm: `convexOn_exp`, a Jensen lemma giving `exp (μ[f]) ≤ μ[exp ∘ f]` for
`IsProbabilityMeasure`, `Real.exp_log`, `Real.log_le_log`, `Real.le_sqrt`/`Real.sqrt_eq_iff`,
`Finset.exp_sum`?, `Finset.single_le_sum`, `Finset.sup'_le`. The `σ = 0` / `d = 1` corners may need
`Real.sqrt` lemmas; document any constant you must weaken in the docstring.

If the Jensen step `exp(∫) ≤ ∫ exp` is genuinely missing from Mathlib (unlikely — search hard, it's
`ConvexOn.map_integral_le` or similar), extract it as ONE named helper lemma and prove IT; do not
leave `expectation_max_le` itself sorried.

# TOUCH-SET: ONLY `StatLean/ConcentrationInequalities/Maximal/FiniteMaximal.lean`.
# BUILD: lake build StatLean.ConcentrationInequalities.Maximal.FiniteMaximal
# DONE = build exits 0, ZERO sorries (the whole file). Commit
(`conc(maximal): close expectation_max_le — E[max] ≤ σ√(2 log d) (Lu-BDA §4.2)`). Report build status
+ exact sorry count (must be 0) + any constant deviation. Independently re-verified.
