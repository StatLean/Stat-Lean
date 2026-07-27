import StatLean.AsymptoticStatistics.ForMathlib.GaussianMGF
import StatLean.AsymptoticStatistics.ForMathlib.MultivariateGaussianWeakLimit
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Lebesgue density bricks for the multivariate Gaussian

Mathlib's `ProbabilityTheory.multivariateGaussian μ S` is defined as a pushforward of
`stdGaussian` and carries no explicit Lebesgue density. This file provides the density
facts needed by the Bernstein–von Mises development (vdV Chapter 10), all for a
**positive definite** covariance `S`:

* `multivariateGaussian_map_const_add` — translation pushforward `N(0,S).map (m + ·) = N(m,S)`;
* `multivariateGaussian_map_matrix_inv` — whitening-type pushforward
  `N(0,J).map (J⁻¹·) = N(0,J⁻¹)`;
* `multivariateGaussian_eq_smul_withDensity` — the **constant-free density**: `N(0,S)` is a
  positive finite multiple of `volume.withDensity (exp (−⟪x, S⁻¹x⟫/2))`. All Chapter-10 uses
  are ratios or normalized restrictions, so the normalizing constant `(2π)^{-d/2} det(S)^{-1/2}`
  is deliberately left abstract;
* `multivariateGaussian_eq_withDensity_tilt` — the mean-shift exponential tilt
  `N(m,S) = N(0,S).withDensity (exp (⟪S⁻¹m, y⟫ − ⟪m,S⁻¹m⟫/2))` (Cameron–Martin form);
* `exists_forall_multivariateGaussian_le_smul_volume` — mean-uniform density **upper** bound;
* `exists_pos_smul_volume_le_multivariateGaussian` — density **lower** bound on bounded sets,
  uniform over bounded means;
* `multivariateGaussian_compl_closedBall_uniform_small` — mean-uniform tail smallness;
* `gaussian_loss_convolution_lt_top` / `gaussian_loss_convolution_continuous` — finiteness and
  continuity of `u ↦ ∫⁻ ℓ(u − z) dN(0,S)(z)` for polynomially growing `ℓ` (used for the limit
  criterion function of vdV Theorem 10.8).

**Proof formalization notes.** The density route: `stdGaussian = (Measure.pi gaussianReal(0,1))`
pushed through an orthonormal-basis equiv (`map_pi_eq_stdGaussian`), whose product density is
`pi_gaussianReal_eq_withDensity`; then push through the invertible `toEuclideanCLM (CFC.sqrt S)`
using `Measure.map_linearMap_addHaar_eq_smul_addHaar` (the `|det|` factor is absorbed into the
abstract constant) and the self-adjointness moves for `CFC.sqrt` already used in
`GaussianMGF.lean` (`multivariateGaussian_withDensity_exp_shift`). The tilt is the existing
`multivariateGaussian_withDensity_exp_shift` at `h := S⁻¹ m`, using
`toEuclideanCLM S (S⁻¹ m) = m` for invertible `S`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Matrix
open scoped RealInnerProductSpace ENNReal

namespace AsymptoticStatistics

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Translation pushforward of a centered Gaussian.** `N(0,S).map (m + ·) = N(m,S)`.
Holds for arbitrary `S` (both sides are pushforwards of `stdGaussian`; the degenerate
`¬PosSemidef` case is Dirac on both sides). -/
theorem multivariateGaussian_map_const_add
    (S : Matrix ι ι ℝ) (m : EuclideanSpace ℝ ι) :
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).map (fun x => m + x)
      = multivariateGaussian m S := by
  sorry

/-- **Whitening pushforward**: for positive definite `J`,
`N(0,J).map (J⁻¹·) = N(0, J⁻¹)`. Immediate from
`multivariateGaussian_map_toEuclideanCLM` and `J⁻¹ * J * (J⁻¹)ᴴ = J⁻¹` (Hermitian inverse). -/
theorem multivariateGaussian_map_matrix_inv
    {J : Matrix ι ι ℝ}
    -- LEAN-ONLY: positive definiteness makes `J` invertible; degenerate case meaningless
    (hJ : J.PosDef) :
    (multivariateGaussian (0 : EuclideanSpace ℝ ι) J).map
        (Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹)
      = multivariateGaussian (0 : EuclideanSpace ℝ ι) J⁻¹ := by
  sorry

/-- **Constant-free Lebesgue density of the centered Gaussian.** For positive definite `S`
there is a positive finite constant `c` (the normalizer `(2π)^{-d/2} det S^{-1/2}`, left
abstract) with
`N(0,S) = c • volume.withDensity (fun x => exp (−⟪x, S⁻¹x⟫/2))`. -/
theorem multivariateGaussian_eq_smul_withDensity
    {S : Matrix ι ι ℝ}
    -- LEAN-ONLY: positive definiteness; the density statement is false for singular `S`
    (hS : S.PosDef) :
    ∃ c : ℝ≥0∞, 0 < c ∧ c ≠ ∞ ∧
      multivariateGaussian (0 : EuclideanSpace ℝ ι) S
        = c • volume.withDensity
            (fun x => ENNReal.ofReal
              (Real.exp (-⟪x, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) x⟫ / 2))) := by
  sorry

/-- **Mean-shift exponential tilt** (Cameron–Martin, invertible-covariance form):
`N(m,S) = N(0,S).withDensity (fun y => exp (⟪S⁻¹m, y⟫ − ⟪m, S⁻¹m⟫/2))`.
This is `multivariateGaussian_withDensity_exp_shift` at `h := S⁻¹ m`. -/
theorem multivariateGaussian_eq_withDensity_tilt
    {S : Matrix ι ι ℝ}
    -- LEAN-ONLY: positive definiteness gives `toEuclideanCLM S (S⁻¹ m) = m`
    (hS : S.PosDef) (m : EuclideanSpace ℝ ι) :
    multivariateGaussian m S
      = (multivariateGaussian (0 : EuclideanSpace ℝ ι) S).withDensity
          (fun y => ENNReal.ofReal
            (Real.exp (⟪(Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) m, y⟫
              - ⟪m, (Matrix.toEuclideanCLM (𝕜 := ℝ) S⁻¹) m⟫ / 2))) := by
  sorry

/-- **Mean-uniform density upper bound.** The Gaussian density is bounded by a constant
independent of the mean: there is `D < ∞` with `N(m,S) A ≤ D · volume A` for every mean `m`
and every set `A` (outer-measure monotonicity handles non-measurable `A`). -/
theorem exists_forall_multivariateGaussian_le_smul_volume
    {S : Matrix ι ι ℝ}
    -- LEAN-ONLY: positive definiteness; a singular Gaussian is not volume-dominated
    (hS : S.PosDef) :
    ∃ D : ℝ≥0∞, D ≠ ∞ ∧
      ∀ (m : EuclideanSpace ℝ ι) (A : Set (EuclideanSpace ℝ ι)),
        multivariateGaussian m S A ≤ D * volume A := by
  sorry

/-- **Density lower bound on bounded sets, uniform over bounded means.** For every
radius pair `R, r` there is `c > 0` with `c · volume A ≤ N(m,S) A` for all `‖m‖ ≤ R` and all
measurable `A ⊆ closedBall 0 r`. -/
theorem exists_pos_smul_volume_le_multivariateGaussian
    {S : Matrix ι ι ℝ}
    -- LEAN-ONLY: positive definiteness; a singular Gaussian has volume-null support
    (hS : S.PosDef) (R r : ℝ) :
    ∃ c : ℝ≥0∞, 0 < c ∧
      ∀ m : EuclideanSpace ℝ ι, ‖m‖ ≤ R →
        ∀ A : Set (EuclideanSpace ℝ ι), A ⊆ Metric.closedBall 0 r → MeasurableSet A →
          c * volume A ≤ multivariateGaussian m S A := by
  sorry

/-- **Mean-uniform tail smallness.** For means in a fixed ball, the Gaussian mass outside
`closedBall 0 M` is eventually (in `M`) below any `ε > 0`, uniformly over the mean. No
definiteness assumption is needed (the degenerate case is a Dirac, whose tail vanishes). -/
theorem multivariateGaussian_compl_closedBall_uniform_small
    (S : Matrix ι ι ℝ) (R : ℝ) {ε : ℝ≥0∞}
    -- LEAN-ONLY: nontrivial tolerance
    (hε : 0 < ε) :
    ∃ M₀ : ℝ, ∀ M : ℝ, M₀ ≤ M → ∀ m : EuclideanSpace ℝ ι, ‖m‖ ≤ R →
      multivariateGaussian m S (Metric.closedBall (0 : EuclideanSpace ℝ ι) M)ᶜ ≤ ε := by
  sorry

/-- **Finiteness of Gaussian loss averages** for polynomially growing losses:
`∫⁻ ℓ(u − z) dN(0,S)(z) < ∞`. -/
theorem gaussian_loss_convolution_lt_top
    (S : Matrix ι ι ℝ) {ℓ : EuclideanSpace ℝ ι → ℝ≥0∞} {p : ℝ}
    -- LEAN-ONLY: polynomial growth of the loss (vdV §10.3 standing assumption)
    (hpoly : ∀ h, ℓ h ≤ ENNReal.ofReal (1 + ‖h‖ ^ p))
    -- LEAN-ONLY: nonnegative exponent (vdV §10.3: `p ≥ 0`)
    (hp : 0 ≤ p) (u : EuclideanSpace ℝ ι) :
    ∫⁻ z, ℓ (u - z) ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) S) < ∞ := by
  sorry

/-- **Continuity of the Gaussian loss average** `u ↦ ∫⁻ ℓ(u − z) dN(0,S)(z)` for a measurable,
polynomially growing loss and positive definite `S`. This derives the continuity of the limit
criterion in vdV Theorem 10.8 (there taken for granted from smoothness of the normal density);
the proof is convolution-with-a-continuous-density plus dominated convergence, via
`multivariateGaussian_eq_smul_withDensity`. -/
theorem gaussian_loss_convolution_continuous
    {S : Matrix ι ι ℝ}
    -- LEAN-ONLY: positive definiteness (continuity can fail for a Dirac limit measure)
    (hS : S.PosDef) {ℓ : EuclideanSpace ℝ ι → ℝ≥0∞} {p : ℝ}
    -- LEAN-ONLY: the loss is measurable (regularity)
    (hmeas : Measurable ℓ)
    -- LEAN-ONLY: polynomial growth of the loss (vdV §10.3 standing assumption)
    (hpoly : ∀ h, ℓ h ≤ ENNReal.ofReal (1 + ‖h‖ ^ p))
    -- LEAN-ONLY: nonnegative exponent (vdV §10.3: `p ≥ 0`)
    (hp : 0 ≤ p) :
    Continuous fun u : EuclideanSpace ℝ ι =>
      ∫⁻ z, ℓ (u - z) ∂(multivariateGaussian (0 : EuclideanSpace ℝ ι) S) := by
  sorry

end AsymptoticStatistics
