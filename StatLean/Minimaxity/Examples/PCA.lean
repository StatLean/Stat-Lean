import StatLean.Minimaxity.Fano.FanoLowerBound
import StatLean.Minimaxity.ForMathlib.GaussianMaxEntropy
import StatLean.Minimaxity.ForMathlib.Packing.SpherePacking
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Example: lower bounds for principal component analysis (Wainwright Example 15.19)

In the spiked covariance model `Z ∼ 𝒩(0, Iᵈ + ν θ*θ*ᵀ)` with leading eigenvector `θ*` on the unit
sphere, the minimax risk for estimating `θ*` in squared Euclidean norm, from `n` i.i.d. samples, is
lower bounded as
```
M(PCA; 𝕊ᵈ⁻¹, ‖·‖₂²) ≳ min{ (1 + ν)/ν² · d/n, 1 }            (Example 15.19),
```
proved by Fano's method with the Gaussian maximum-entropy mutual-information bound (Lemma 15.17) over
a `1/2`-packing of the sphere (Example 5.8).

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.4, Example 15.19.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal

namespace StatLean.Minimaxity

/-- **Crux: Fano configuration for the spiked-covariance PCA lower bound.** A `1/2`-packing of the
unit sphere (Wainwright Example 5.8, `exists_sphere_packing`) of cardinality `2^Ω(d)` gives a
`2δ`-separated family with `δ² ≍ min{(1+ν)/ν²·d/n, 1}`; the Gaussian maximum-entropy bound on the
mutual information (Lemma 15.17) keeps `I(Z;J) ≤ ½ log M`, so Fano's `(1 − ·)` factor is `≥ ½`. -/
private lemma pca_fano_config {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d) (ν : ℝ) (hν : 0 < ν)
    (P : Kernel (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) (Fin n → EuclideanSpace ℝ (Fin d)))
    [IsMarkovKernel P]
    (hP : ∀ θ, P θ = Measure.pi fun _ : Fin n =>
      multivariateGaussian 0 (1 + ν • vecMulVec (θ : Fin d → ℝ) (θ : Fin d → ℝ))) :
    ∃ (M : ℕ) (_ : NeZero M) (θfam : Fin M → Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1)
      (hθ : Measurable θfam) (δ : ℝ≥0∞),
      2 ≤ M ∧ IsSeparatedFamily (Subtype.val) θfam δ ∧
      ENNReal.ofReal (128⁻¹ * min ((1 + ν) / ν ^ 2 * (d / n)) 1)
        ≤ (fun x : ℝ≥0∞ => x ^ 2) δ
            * (1 - (mutualInformation (P.comap θfam hθ) + ENNReal.ofReal (Real.log 2))
                    / ENNReal.ofReal (Real.log (M : ℝ))) := by
  sorry -- TODO(mmx): sphere packing (exists_sphere_packing) + Gaussian max-entropy MI bound (15.17)

/-- **Minimax risk for PCA in the spiked model** (Wainwright Example 15.19): for `n` i.i.d. samples
from `𝒩(0, Iᵈ + ν θ*θ*ᵀ)` with `θ*` on the unit sphere, the minimax risk for estimating `θ*` in
squared Euclidean norm is at least `c·min{(1+ν)/ν²·d/n, 1}`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.3.4, Example 15.19. -/
theorem pca_minimax_rate {n d : ℕ} (hn : 1 ≤ n) (hd : 1 ≤ d) (ν : ℝ) (hν : 0 < ν)
    (P : Kernel (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) (Fin n → EuclideanSpace ℝ (Fin d)))
    [IsMarkovKernel P]
    -- USER-INPUT: `Z ∼ 𝒩(0, Iᵈ + ν θθᵀ)^{⊗n}` (spiked covariance model); Wainwright §15.3.4, Ex 15.19.
    (hP : ∀ θ, P θ = Measure.pi fun _ : Fin n =>
      multivariateGaussian 0 (1 + ν • vecMulVec (θ : Fin d → ℝ) (θ : Fin d → ℝ))) :
    ENNReal.ofReal (128⁻¹ * min ((1 + ν) / ν ^ 2 * (d / n)) 1)
      ≤ minimaxRiskDist (· ^ 2) (Subtype.val) P := by
  obtain ⟨M, hMne, θfam, hθ, δ, hM, hsep, hbound⟩ := pca_fano_config hn hd ν hν P hP
  haveI := hMne
  have hΦ : Monotone (fun x : ℝ≥0∞ => x ^ 2) := fun a b hab => pow_le_pow_left' hab 2
  have key := minimax_fano_lower_bound (fun x : ℝ≥0∞ => x ^ 2) (Subtype.val) P θfam hθ δ hM hΦ hsep
  exact le_trans hbound key

end StatLean.Minimaxity
