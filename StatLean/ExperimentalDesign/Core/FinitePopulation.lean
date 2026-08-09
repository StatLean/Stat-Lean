import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators

/-!
# Finite-population summaries: total, mean, variance

Design-based inference regards the experimental (or survey) units as a *fixed finite
population* `U` carrying a *deterministic* quantity `y : U → ℝ`; all randomness enters
later, through the randomization or sampling design.  This file records the
deterministic population summaries
$$Y = \sum_{i} y_i, \qquad \bar y = \frac1N \sum_i y_i, \qquad
  S^2_y = \frac{1}{N-1}\sum_i (y_i - \bar y)^2, \qquad N = |U|,$$
and their elementary algebra: centering, the computational form of the sum of squared
deviations, nonnegativity and degeneracy of `S²`, and behaviour under translation and
scaling.

Keeping these summaries deterministic — never entangled with a design — is the load-
bearing convention of the whole `ExperimentalDesign` area: unbiasedness statements
read `pmfExpect D (statistic) = populationMean y` with the right-hand side a pure
function of the data.

## Main results

* `populationTotal`, `populationMean`, `populationVariance` — the summaries.
* `sum_sub_populationMean` — centered values sum to zero.
* `sum_sq_sub_populationMean` — `∑ (yᵢ − ȳ)² = ∑ yᵢ² − N ȳ²`.
* `populationVariance_nonneg`, `populationVariance_eq_zero_iff` — degeneracy.
* `populationMean_add`, `populationMean_smul`, `populationVariance_smul`,
  `populationVariance_add_const` — affine equivariance.

**Reference.** The finite model of experimental data — a fixed set of units, all used,
with fixed unit values — is Mead's "finite model": R. Mead, *The Design of
Experiments*, Cambridge University Press, 1988, §9.4–§9.5 (the finite model and its
contrast with the infinite model).  The `N − 1` normalisation of `S²` is the standard
finite-population variance of survey sampling.  (`Mead §9.4`.)

**Proof formalization notes.**
* Edge behaviour is by Lean's `(0:ℝ)⁻¹ = 0` convention: for `U` empty the mean is `0`;
  for `N ≤ 1` the variance is `0`.  Statements that would be false degenerately carry
  explicit cardinality hypotheses (`Nonempty U`, `2 ≤ Fintype.card U`).
* `populationVariance_eq_zero_iff` requires `2 ≤ N`: for `N ≤ 1` the variance is `0`
  by convention while the right-hand side is vacuously true, so the statement happens
  to hold, but we keep the hypothesis to match the honest mathematical content.
-/

namespace StatLean.ExperimentalDesign

variable {U : Type*} [Fintype U]

/-- The **population total** `Y = ∑ᵢ yᵢ` of a deterministic finite-population quantity
(`Mead §9.4`, the finite model). -/
noncomputable def populationTotal (y : U → ℝ) : ℝ := ∑ i, y i

/-- The **population mean** `ȳ = N⁻¹ ∑ᵢ yᵢ`.  Edge behaviour: `0` for the empty
population (`(0:ℝ)⁻¹ = 0`). -/
noncomputable def populationMean (y : U → ℝ) : ℝ :=
  (Fintype.card U : ℝ)⁻¹ * ∑ i, y i

/-- The **finite-population variance** `S² = (N−1)⁻¹ ∑ᵢ (yᵢ − ȳ)²`, with the survey-
sampling `N − 1` normalisation.  Edge behaviour: `0` when `N ≤ 1`. -/
noncomputable def populationVariance (y : U → ℝ) : ℝ :=
  ((Fintype.card U : ℝ) - 1)⁻¹ * ∑ i, (y i - populationMean y) ^ 2

/-- The total is `N` times the mean (degenerately `0 = 0` for the empty population). -/
theorem populationTotal_eq_card_mul_mean (y : U → ℝ) :
    populationTotal y = (Fintype.card U : ℝ) * populationMean y := by
  sorry

/-- Centered population values sum to zero. -/
theorem sum_sub_populationMean [Nonempty U] (y : U → ℝ) :
    ∑ i, (y i - populationMean y) = 0 := by
  sorry

/-- The population mean of a constant is that constant. -/
theorem populationMean_const [Nonempty U] (c : ℝ) :
    populationMean (fun _ : U => c) = c := by
  sorry

/-- Additivity of the population mean. -/
theorem populationMean_add (y z : U → ℝ) :
    populationMean (fun i => y i + z i) = populationMean y + populationMean z := by
  sorry

/-- Homogeneity of the population mean. -/
theorem populationMean_smul (c : ℝ) (y : U → ℝ) :
    populationMean (fun i => c * y i) = c * populationMean y := by
  sorry

/-- Computational form of the centered sum of squares:
`∑ (yᵢ − ȳ)² = ∑ yᵢ² − N ȳ²`. -/
theorem sum_sq_sub_populationMean [Nonempty U] (y : U → ℝ) :
    ∑ i, (y i - populationMean y) ^ 2
      = ∑ i, y i ^ 2 - (Fintype.card U : ℝ) * populationMean y ^ 2 := by
  sorry

/-- The finite-population variance is nonnegative (including the degenerate `N ≤ 1`
cases, where it is `0` by convention). -/
theorem populationVariance_nonneg (y : U → ℝ) : 0 ≤ populationVariance y := by
  sorry

/-- The finite-population variance of a constant vanishes. -/
theorem populationVariance_const (c : ℝ) :
    populationVariance (fun _ : U => c) = 0 := by
  sorry

/-- For a population with at least two units, zero variance characterises constancy. -/
theorem populationVariance_eq_zero_iff
    -- LEAN-ONLY: rules out the `N ≤ 1` convention cases; no scope change
    (h2 : 2 ≤ Fintype.card U) (y : U → ℝ) :
    populationVariance y = 0 ↔ ∀ i j, y i = y j := by
  sorry

/-- Quadratic scaling of the finite-population variance. -/
theorem populationVariance_smul (c : ℝ) (y : U → ℝ) :
    populationVariance (fun i => c * y i) = c ^ 2 * populationVariance y := by
  sorry

/-- Translation invariance of the finite-population variance. -/
theorem populationVariance_add_const (y : U → ℝ) (c : ℝ) :
    populationVariance (fun i => y i + c) = populationVariance y := by
  sorry

end StatLean.ExperimentalDesign
