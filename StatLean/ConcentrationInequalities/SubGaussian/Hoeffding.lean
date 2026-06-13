import StatLean.ConcentrationInequalities.SubGaussian.Defs

/-!
# Hoeffding's inequality for sums of independent sub-Gaussian variables

Lu, *Big Data Analysis* §2.2 (Theorem "Hoeffding Inequality", label
`thm:hoefdding`): if `X 0, …, X (n−1)` are **independent** and each is
sub-Gaussian with variance proxy `σ²` (in the sense of our
`IsSubGaussian` predicate from `…/SubGaussian/Defs.lean`), then for every
`t > 0`,

  `P( (1/n) ∑_{i<n} (X i − E[X i])  >  t )  ≤  exp(− n t² / (2 σ²))`.

Equivalently the centered sum `∑_{i<n} (X i − E[X i])` exceeds `n t` with the
same bound; this is the form we state and prove directly, since it matches
Mathlib's sum-tail lemma
`ProbabilityTheory.HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun`
applied at the threshold `ε := n t` to the centered variables
`X i − E[X i]` — precisely the engine wrapped by `IsSubGaussian`.

We additionally record the **scalar-multiple** rule used downstream in
OLS / Lasso noise bounds: `c · X` is sub-Gaussian with proxy `c² σ²`
(Lu-BDA §2.2), delegated to `ProbabilityTheory.HasSubgaussianMGF.const_mul`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Scalar multiple of a sub-Gaussian variable, Lu-BDA §2.2.**
If `X` is sub-Gaussian with variance proxy `σ²`, then `c · X` (as
`fun ω => c * X ω`) is sub-Gaussian with proxy `c² σ²`. Centering passes
through the scalar via `MeasureTheory.integral_const_mul`, so this is a
direct corollary of Mathlib's
`ProbabilityTheory.HasSubgaussianMGF.const_mul`. The proxy `c² σ²` is the
`ℝ≥0` element `⟨c², sq_nonneg c⟩ * σ²`, matching Mathlib's encoding of
`const_mul`. Used downstream by OLS / Lasso to scale per-coordinate noise
bounds. -/
theorem isSubGaussian_const_mul {X : Ω → ℝ} {σ2 : ℝ≥0} {μ : Measure Ω}
    (h : IsSubGaussian X σ2 μ) (c : ℝ) :
    IsSubGaussian (fun ω => c * X ω) (⟨c ^ 2, sq_nonneg c⟩ * σ2) μ := by
  -- Mathlib `const_mul` applied to the centered engine of `IsSubGaussian`.
  have h' : HasSubgaussianMGF (fun ω => c * (X ω - ∫ x, X x ∂μ))
              (⟨c ^ 2, sq_nonneg c⟩ * σ2) μ :=
    (h : HasSubgaussianMGF (fun ω => X ω - ∫ x, X x ∂μ) σ2 μ).const_mul c
  -- The centered engine of `c · X` is the same function (pull `c` through `∫`).
  show HasSubgaussianMGF (fun ω => c * X ω - ∫ x, c * X x ∂μ)
        (⟨c ^ 2, sq_nonneg c⟩ * σ2) μ
  have heq : (fun ω => c * X ω - ∫ x, c * X x ∂μ) =
              (fun ω => c * (X ω - ∫ x, X x ∂μ)) := by
    funext ω
    rw [integral_const_mul]
    ring
  rw [heq]
  exact h'

/-- **Hoeffding's inequality (centered-sum form), Lu-BDA §2.2 `thm:hoefdding`.**
If `X 0, …, X (n−1)` are jointly independent and each is sub-Gaussian with
variance proxy `σ²` under the probability measure `μ`, then for every `t > 0`,

  `P( ∑_{i<n} (X i − E[X i])  ≥  n t )  ≤  exp(− n t² / (2 σ²))`.

Equivalently, dividing the threshold and the bound by `n` (for `n ≥ 1`):

  `P( (1/n) ∑_{i<n} (X i − E[X i]) ≥ t ) ≤ exp(− n t² / (2 σ²))`,

which is the sample-mean form stated by Lu (the strict inequality `>` is
implied since `{ω | t < S ω} ⊆ {ω | t ≤ S ω}`). Proved by feeding the
centered variables `X i − E[X i]` — the engine of `IsSubGaussian` — into
Mathlib's sum-tail bound
`HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun` at threshold
`ε := n t`. -/
theorem hoeffding {n : ℕ} {X : ℕ → Ω → ℝ} {σ2 : ℝ≥0} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    -- LEAN-ONLY: measurability of each `X i`; needed by `iIndepFun.comp` to
    --            lift independence of `X` to independence of the centered family
    --            `X i − E[X i]`.
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: X 0, …, X (n-1) are jointly independent; Lu-BDA §2.2 thm:hoefdding.
    (hX_indep : iIndepFun X μ)
    -- USER-INPUT: each X i is sub-Gaussian with variance proxy σ²; Lu-BDA §2.2 thm:hoefdding.
    (hX_subG : ∀ i, i < n → IsSubGaussian (X i) σ2 μ)
    -- USER-INPUT: at least one variable in the family `X 0, …, X (n-1)`;
    --             Lu-BDA §2.2 thm:hoefdding (implicit in "X 0, …, X (n−1)").
    (hn : 1 ≤ n)
    -- USER-INPUT: t > 0; Lu-BDA §2.2 thm:hoefdding.
    {t : ℝ} (ht : 0 < t) :
    μ.real {ω | (n : ℝ) * t ≤ ∑ i ∈ Finset.range n, (X i ω - ∫ x, X i x ∂μ)}
      ≤ Real.exp (-(n : ℝ) * t ^ 2 / (2 * (σ2 : ℝ))) := by
  -- Step 1: lift independence of `X` to the centered family `X i − E[X i]`.
  have hg : ∀ i, Measurable (fun y : ℝ => y - ∫ x, X i x ∂μ) :=
    fun i => measurable_id.sub_const _
  have hY_indep :
      iIndepFun (fun i ω => X i ω - ∫ x, X i x ∂μ) μ :=
    hX_indep.comp _ hg
  -- Step 2: each centered variable carries the sub-Gaussian MGF bound.
  have hY_subG : ∀ i, i < n →
      HasSubgaussianMGF (fun ω => X i ω - ∫ x, X i x ∂μ) σ2 μ :=
    fun i hi => hX_subG i hi
  -- Step 3: apply Mathlib's sub-Gaussian sum-tail at threshold ε := n t.
  have hε : (0 : ℝ) ≤ (n : ℝ) * t := by positivity
  have h := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun
              hY_indep hY_subG hε
  refine h.trans ?_
  -- Step 4: identify the Mathlib RHS `exp(-(nt)² / (2 n σ²))` with our
  --          `exp(-n t² / (2 σ²))`; equal as reals for n ≥ 1, including the
  --          σ² = 0 corner (where both reduce to `exp 0 = 1` via `x / 0 = 0`).
  apply Real.exp_le_exp.mpr
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnR' : (n : ℝ) ≠ 0 := ne_of_gt hnR
  rcases eq_or_ne (σ2 : ℝ) 0 with hs | hs
  · -- σ² = 0: both sides collapse to `0` via `x / 0 = 0`.
    rw [hs]
    simp
  · -- σ² > 0: clear denominators (field_simp closes the resulting goal; see
    -- CLAUDE.md §7.10 — a trailing `ring` would raise "no goals").
    have heq : -((n : ℝ) * t) ^ 2 / (2 * (n : ℝ) * (σ2 : ℝ))
                = -(n : ℝ) * t ^ 2 / (2 * (σ2 : ℝ)) := by
      field_simp
    exact le_of_eq heq

end StatLean.ConcentrationInequalities
