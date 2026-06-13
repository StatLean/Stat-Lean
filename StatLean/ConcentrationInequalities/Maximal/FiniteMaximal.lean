import StatLean.ConcentrationInequalities.SubGaussian.TailBounds
import Mathlib.Data.Fintype.Order

/-!
# Finite Maximal Inequality — Lu-BDA §4.2, `thm:finite-maximal`

We formalize Lu, *Big Data Analysis* §4.2 for `d ≥ 1` centered sub-Gaussian random
variables `X : Fin d → Ω → ℝ` (each with variance proxy `σ²` under `μ`, NOT
necessarily independent).

**Tail bound** (`tail_max_le`): for `t ≥ 0`,
`μ {ω | t < ⨆ j, X j ω} ≤ ENNReal.ofReal (d · exp(−t²/(2σ²)))`.

**Expectation bound** (`expectation_max_le`): under `IsProbabilityMeasure μ`,
`E[⨆ j, X j] ≤ √σ² · √(2 log d)`.

The tail bound is fully proved via a union bound: the event `{max_j X_j > t}` is the
union of `{X_j > t}`, each of which is bounded by `exp(−t²/(2σ²))` via
`IsSubGaussian.measure_sub_integral_lt_le` (centeredness kills the `−∫ X_j` shift).

The expectation bound `expectation_max_le` is a named `sorry`; the full proof requires:
Jensen on `exp(λ ·)` (convex, probability measure), sum-bound `exp(λ max) ≤ ∑ exp(λ X_j)`
for `λ > 0`, sub-Gaussian MGF bound for each `j`, then algebra to optimise
`λ = √(2 log d / σ²)` giving the stated constant `√σ² · √(2 log d)`.

Deviation from the book: Lu states both bounds for `t > 0` (tail) and uses strict
sub-Gaussianity; we allow `t ≥ 0` throughout, which is strictly stronger.
-/

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Tail bound -/

/-- **Finite Maximal Inequality — tail bound** (Lu-BDA §4.2, `thm:finite-maximal`).

Given `d ≥ 1` random variables, each sub-Gaussian with variance proxy `σ²` and
centered (`E[X_j] = 0`), and `t ≥ 0`:
```
μ {ω | t < ⨆ j : Fin d, X j ω} ≤ ENNReal.ofReal (d · exp(−t²/(2σ²)))
```

The finite max is expressed as `⨆ j : Fin d, X j ω` (the `iSup` equals the pointwise
maximum for `d ≥ 1`).

Proof: union bound (`measure_iUnion_fintype_le`) + per-`j` sub-Gaussian Chernoff tail
(`IsSubGaussian.measure_sub_integral_lt_le`; centeredness kills the `−∫ X_j` shift). -/
theorem tail_max_le
    {d : ℕ} [NeZero d] {μ : Measure Ω} {σ2 : ℝ≥0}
    {X : Fin d → Ω → ℝ}
    -- USER-INPUT: E[X_j] = 0; Lu-BDA §4.2 (thm:finite-maximal)
    (hcenter : ∀ j, ∫ x, X j x ∂μ = 0)
    -- USER-INPUT: X_j is sub-Gaussian with variance proxy σ²; Lu-BDA §4.2 (thm:finite-maximal)
    (hX : ∀ j, IsSubGaussian (X j) σ2 μ)
    -- USER-INPUT: 0 ≤ t (book: t > 0); Lu-BDA §4.2 (thm:finite-maximal)
    {t : ℝ} (ht : 0 ≤ t) :
    μ {ω | t < ⨆ j, X j ω}
      ≤ ENNReal.ofReal ((d : ℝ) * Real.exp (-t ^ 2 / (2 * ↑σ2))) := by
  -- `Fin d` is nonempty since d ≥ 1.
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp (Nat.pos_of_neZero d)
  -- The range of `j ↦ X j ω` is finite hence bounded above, for every fixed `ω`.
  have hbdd : ∀ ω, BddAbove (Set.range (fun j => X j ω)) := fun ω =>
    Finite.bddAbove_range _
  -- Step 1: Rewrite `{ω | t < ⨆ j, X j ω}` as the union `⋃ j, {ω | t < X j ω}`.
  have heq : {ω | t < ⨆ j, X j ω} = ⋃ j, {ω | t < X j ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    exact ⟨fun h => (lt_ciSup_iff (hbdd ω)).mp h,
           fun ⟨j, hj⟩ => lt_of_lt_of_le hj (le_ciSup (hbdd ω) j)⟩
  rw [heq]
  -- Step 2: Union bound + per-j Chernoff tail.
  calc μ (⋃ j, {ω | t < X j ω})
      ≤ ∑ j : Fin d, μ {ω | t < X j ω} :=
          measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin d, ENNReal.ofReal (Real.exp (-t ^ 2 / (2 * ↑σ2))) := by
          apply Finset.sum_le_sum
          intro j _
          -- Centeredness: X j ω - ∫ X j ∂μ = X j ω - 0 = X j ω.
          have hj := (hX j).measure_sub_integral_lt_le ht
          simp only [hcenter j, sub_zero] at hj
          exact hj
    _ = ENNReal.ofReal ((d : ℝ) * Real.exp (-t ^ 2 / (2 * ↑σ2))) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          -- d • ENNReal.ofReal e = ENNReal.ofReal (d * e)
          rw [← ENNReal.ofReal_nsmul, nsmul_eq_mul]

/-! ### Expectation bound -/

/-- **Finite Maximal Inequality — expectation bound** (Lu-BDA §4.2, `thm:finite-maximal`).

Given `d ≥ 1` centered sub-Gaussian random variables with variance proxy `σ²` under a
probability measure `μ`:
```
E[⨆ j : Fin d, X j] ≤ √σ² · √(2 log d)
```

Proof sketch (Lu §4.2): for any `λ > 0`, by Jensen (exp is convex, μ is probability),
`exp(λ · E[max]) ≤ E[exp(λ · max)] ≤ E[∑_j exp(λ X_j)] = ∑_j mgf(X_j, λ)`;
sub-Gaussian MGF gives `∑_j mgf(X_j, λ) ≤ d · exp(σ² λ²/2)`. Taking log and dividing by
`λ` yields `E[max] ≤ log d / λ + σ² λ / 2`; optimising at `λ* = √(2 log d / σ²)` gives
`σ √(2 log d)`.

TODO: the algebra of the λ-optimisation step is deferred. -/
theorem expectation_max_le
    {d : ℕ} [NeZero d] {μ : Measure Ω} [IsProbabilityMeasure μ] {σ2 : ℝ≥0}
    {X : Fin d → Ω → ℝ}
    -- USER-INPUT: E[X_j] = 0; Lu-BDA §4.2 (thm:finite-maximal)
    (hcenter : ∀ j, ∫ x, X j x ∂μ = 0)
    -- USER-INPUT: X_j is sub-Gaussian with variance proxy σ²; Lu-BDA §4.2 (thm:finite-maximal)
    (hX : ∀ j, IsSubGaussian (X j) σ2 μ) :
    ∫ ω, ⨆ j, X j ω ∂μ ≤ Real.sqrt (σ2 : ℝ) * Real.sqrt (2 * Real.log d) := by
  sorry

end StatLean.ConcentrationInequalities
