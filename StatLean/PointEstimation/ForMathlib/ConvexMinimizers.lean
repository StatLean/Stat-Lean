import Mathlib.Analysis.Convex.Function
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Minimizers of convex integral criteria on the line

The optimization facts behind conditional-risk minimization on the real line:

* `lintegral_convex_even_min_at_zero` — for a convex even `ρ` and a symmetric measure, the
  shifted criterion `c ↦ ∫⁻ ρ (x - c)` is minimized at `c = 0`;
* `exists_min_of_convexOn_of_coercive` — a convex coercive real function on `ℝ` attains its
  minimum;
* `argmin_unique_of_strictConvexOn` — a strictly convex function has at most one minimizer;
* `integral_sq_sub_eq_variance_add_sq` — the bias–variance identity
  `E (X − c)² = E (X − E X)² + (E X − c)²`;
* `integral_sq_sub_mean_le` — its immediate corollary: the mean minimizes squared error.

**Reference.** Classical convexity and least-squares theory; original sources in the
bibliographic comments below.

**Proof formalization notes.**
* **`lintegral_convex_even_min_at_zero` is stated for an ARBITRARY measure.** The argument is
  purely `∫⁻`-level: convexity gives the pointwise bound
  `ρ x ≤ ½ ρ (x - c) + ½ ρ (x + c)`, monotonicity and additivity of the lower Lebesgue
  integral turn it into `∫⁻ ρ ≤ ½ ∫⁻ ρ (· - c) + ½ ∫⁻ ρ (· + c)`, and symmetry of the measure
  identifies the two right-hand integrals. Nothing in this chain needs finiteness of `μ` or
  of any of the integrals — `ℝ≥0∞` absorbs the `⊤` cases — so no finiteness hypothesis is
  imposed. Only measurability of `ρ` is required, for additivity of `∫⁻`.
* **Convexity coefficients.** The `∫⁻` statement uses `ConvexOn ℝ≥0`, the only convexity
  predicate that typechecks for `ℝ≥0∞`-valued functions at this pin (`ℝ≥0∞` is a module over
  `ℝ≥0`, not over `ℝ`). The real-valued statements use the ordinary `ConvexOn ℝ`.
* **No continuity hypothesis on `exists_min_of_convexOn_of_coercive`.** A convex function
  `ℝ → ℝ` defined on all of `ℝ` is automatically continuous, so assuming continuity would be
  assuming something forced by the other hypotheses. Coercivity is `Tendsto g (cocompact ℝ)
  atTop`, which for an `ℝ`-valued objective is the intended "blows up at infinity"; the
  `ℝ≥0∞`-valued counterpart lives in `ForMathlib/MeasurableArgmin.lean`, where the target
  filter must be `𝓝 ⊤` instead (in `ℝ≥0∞`, `atTop = pure ⊤`).
* **`integral_sq_sub_mean_le` hypothesizes only the second moment.** Integrability of `X`
  itself is *derived* from `MemLp X 2 μ` on a probability measure, so listing it as a
  hypothesis would be laundering a forced condition. The same applies to integrability of
  `(X - c)²`, which follows from `MemLp.integrable_sq` after adding the constant.
* The bias–variance identity is stated as an equation on Bochner integrals rather than in
  terms of `ProbabilityTheory.variance`, so that it applies to conditional laws presented as
  arbitrary probability measures without a variance-API detour.

**Bibliographic comments.** The convexity inequality underlying the first three statements is
J. L. W. V. Jensen's ("Sur les fonctions convexes et les inégalités entre les valeurs
moyennes," *Acta Math.* **30** (1906), 175–193). That the mean minimizes mean squared error,
and the accompanying decomposition of the error, go back to C. F. Gauss's least-squares
memoir (*Theoria combinationis observationum erroribus minimis obnoxiae*, Göttingen, 1821).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace StatLean.PointEstimation

/-- For a convex even penalty and a symmetric measure, no shift beats the zero shift. -/
theorem lintegral_convex_even_min_at_zero
    -- USER-INPUT: the (arbitrary) measure; no finiteness needed, see the header
    {μ : Measure ℝ}
    -- USER-INPUT: the penalty function
    {ρ : ℝ → ℝ≥0∞}
    -- USER-INPUT: measurability of the penalty; needed for additivity of `∫⁻`
    (hρ_meas : Measurable ρ)
    -- USER-INPUT: convexity of the penalty; the substantive hypothesis
    (hρ_conv : ConvexOn ℝ≥0 Set.univ ρ)
    -- USER-INPUT: evenness of the penalty
    (hρ_even : ∀ v : ℝ, ρ (-v) = ρ v)
    -- USER-INPUT: symmetry of the measure about the origin
    (hμ_symm : μ.map (fun x => -x) = μ)
    -- USER-INPUT: the competing shift
    (c : ℝ) :
    ∫⁻ x, ρ x ∂μ ≤ ∫⁻ x, ρ (x - c) ∂μ := by
  sorry

/-- A convex coercive function on the line attains its minimum. -/
theorem exists_min_of_convexOn_of_coercive
    -- USER-INPUT: the objective
    {g : ℝ → ℝ}
    -- USER-INPUT: convexity on the whole line; also supplies continuity, see the header
    (hg : ConvexOn ℝ Set.univ g)
    -- USER-INPUT: coercivity; compactness of a nontrivial sublevel set
    (hcoer : Tendsto g (cocompact ℝ) atTop) :
    ∃ v : ℝ, ∀ w : ℝ, g v ≤ g w := by
  sorry

/-- A strictly convex function on the line has at most one minimizer. -/
theorem argmin_unique_of_strictConvexOn
    -- USER-INPUT: the objective
    {g : ℝ → ℝ}
    -- USER-INPUT: strict convexity; the substantive hypothesis
    (hg : StrictConvexOn ℝ Set.univ g)
    -- USER-INPUT: two points, each minimizing `g`
    {v w : ℝ} (hv : ∀ u : ℝ, g v ≤ g u) (hw : ∀ u : ℝ, g w ≤ g u) :
    v = w := by
  sorry

/-- **Bias–variance identity.** `E (X − c)² = E (X − E X)² + (E X − c)²`. -/
theorem integral_sq_sub_eq_variance_add_sq {Ω : Type*} [MeasurableSpace Ω]
    -- USER-INPUT: the law of the random variable; free choice
    {μ : Measure Ω}
    -- USER-INPUT: the law is a probability measure; the identity is false for total mass ≠ 1
    [IsProbabilityMeasure μ]
    -- USER-INPUT: the random variable
    {X : Ω → ℝ}
    -- USER-INPUT: a finite second moment; makes both sides finite
    (hX : MemLp X 2 μ)
    -- USER-INPUT: the competing constant
    (c : ℝ) :
    ∫ ω, (X ω - c) ^ 2 ∂μ
      = (∫ ω, (X ω - ∫ ω', X ω' ∂μ) ^ 2 ∂μ) + ((∫ ω', X ω' ∂μ) - c) ^ 2 := by
  sorry

/-- **The mean minimizes mean squared error.** -/
theorem integral_sq_sub_mean_le {Ω : Type*} [MeasurableSpace Ω]
    -- USER-INPUT: the law of the random variable; free choice
    {μ : Measure Ω}
    -- USER-INPUT: the law is a probability measure
    [IsProbabilityMeasure μ]
    -- USER-INPUT: the random variable
    {X : Ω → ℝ}
    -- USER-INPUT: a finite second moment; integrability of `X` is derived, not assumed
    (hX : MemLp X 2 μ)
    -- USER-INPUT: the competing constant
    (c : ℝ) :
    ∫ ω, (X ω - ∫ ω', X ω' ∂μ) ^ 2 ∂μ ≤ ∫ ω, (X ω - c) ^ 2 ∂μ := by
  sorry

end StatLean.PointEstimation
