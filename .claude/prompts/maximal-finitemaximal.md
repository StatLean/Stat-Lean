Read CLAUDE.md (repo root) first and obey it — §2, §6 (search tools), §7, §9, §10.
Use `./tools/where.sh`, `./tools/loogle.sh '"name"'`, `./tools/check.sh '<name>'`. Never `lake update`.

# CONTEXT
`StatLean/ConcentrationInequalities/SubGaussian/Defs.lean` defines (do NOT modify):
`def IsSubGaussian (X) (σ2 : ℝ≥0) (μ) := HasSubgaussianMGF (fun ω => X ω - ∫ x, X x ∂μ) σ2 μ`
and `isSubGaussian_iff`. Mathlib's `ProbabilityTheory.HasSubgaussianMGF` gives the raw-MGF bound
(`mgf … t ≤ exp(σ2 t²/2)`) and a union/`measure_ge_le` tail.

# TASK
Create `StatLean/ConcentrationInequalities/Maximal/FiniteMaximal.lean`
(namespace `StatLean.ConcentrationInequalities`) formalizing Lu *Big Data Analysis* §4.2
**Finite Maximal Inequality** (`thm:finite-maximal`): given `d ≥ 1` sub-Gaussian variables
`X : Fin d → Ω → ℝ`, each `IsSubGaussian (X j) σ² μ` with `∫ X j = 0` (centered), NOT necessarily
independent:

1. Expectation bound: `∫ (fun ω => ⨆ j, X j ω) ∂μ ≤ σ * Real.sqrt (2 * Real.log d)`.
   (Finite `Fin d` max — use `Finset.univ.sup'`/`Finset.max'` for the finite maximum, not `iSup`.)
2. Tail bound: for `0 ≤ t`, `μ {ω | t < ⨆ j, X j ω} ≤ ENNReal.ofReal (d * exp(−t²/(2σ²)))`.

# PROOF (book §4.2)
- Tail: union bound `μ(⋃ j {X j > t}) ≤ ∑ j μ{X j > t} ≤ d · exp(−t²/2σ²)`, each term from the
  one-sided sub-Gaussian tail (`HasSubgaussianMGF.measure_ge_le`, same brick as
  `SubGaussian/TailBounds.lean`; read that file for the ENNReal bridge). Use `measure_biUnion_finset_le`
  / `measure_iUnion_fintype_le` and `Finset.sum_le_card_nsmul`.
- Expectation: Jensen on the convex `exp`: `exp(λ·E[max]) ≤ E[exp(λ·max)] = E[max_j exp(λ X_j)]
  ≤ ∑_j E[exp(λ X_j)] ≤ d·exp(λ²σ²/2)`; take `log`, divide by `λ`, optimize `λ = √(2 log d / σ²)`
  to get `σ√(2 log d)`. Mathlib: `mgf` bound from `HasSubgaussianMGF.mgf_le`, `Real.add_pow_le_pow_mul_pow_of_sq_le_sq`
  is NOT needed; the key analytic step is `inner_le_nnorm`-free — it's `Real.log`/`Real.exp` monotonicity
  + the per-`j` mgf bound. Integrability of the max-exp from the per-term `HasSubgaussianMGF.integrable_exp_mul`.

`d ≥ 1` (`[NeZero d]` or `0 < d`) is `-- USER-INPUT: d ≥ 1; Lu-BDA §4.2 (thm:finite-maximal)`.
Centeredness `∫ X j = 0` is `-- USER-INPUT: E[X_j]=0; Lu-BDA §4.2`. Document any weakened constant.

# TOUCH-SET
Create/modify ONLY `StatLean/ConcentrationInequalities/Maximal/FiniteMaximal.lean`. Do NOT touch
`Defs.lean`, the umbrella, `StatLean.lean`, lakefile/manifest/toolchain, `notes/`.

# BUILD
  lake build StatLean.ConcentrationInequalities.Maximal.FiniteMaximal

# DONE = build exits 0; ZERO sorries; §2 tags; small commit
(`conc(maximal): finite maximal inequality (Lu-BDA §4.2 thm:finite-maximal)`). Print declaration
names, build status, constant deviations. The expectation half is the harder one — if after a
genuine effort only the tail half closes, commit the tail half PROVEN and leave the expectation
bound as a single named `sorry` lemma `expectation_max_le` with a one-line note; do NOT fake it.
