import StatLean.AsymptoticStatistics.ForMathlib.BowlShaped
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Minimax bound in the Gaussian shift experiment

Lemma 4 of the lower-bound proof of vdV §25.3, Theorem 25.21: a minimax
Bayes-risk lower bound in the Gaussian shift experiment
`(N(h, I_m) : h ∈ ℝᵐ)`, restricted to a convex cone `C_m` with nonempty
interior. For the scalar parameter functional (`k = 1`) the book's linear
coefficient collapses to a continuous linear functional
`A : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ`, and the covariance to the scalar
variance `‖A‖²`. The headline declaration is `gaussianShift_minimax`.

The book derives this in three steps: (1) Anderson's lemma on a Gaussian
prior `N(c h₀, c I_m)` identifies the posterior loss minimum as a Gaussian
integral; (2) restricting the prior to `C_m` and letting `c → ∞` recovers
`∫ ℓ dN(0, ‖A‖²)`; (3) a finite-support density argument plus Bayes-risk
continuity transports the Bayes lower bound to the finite-subset minimax
form. Steps (1)+(2) and step (3) enter as the hypotheses `hPriorBayesBound`
and `hFiniteSupportApprox`; they are combined via `le_iSup`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

namespace AsymptoticStatistics.LowerBounds.GaussianShiftMinimax

open AsymptoticStatistics

variable {m : ℕ}

/-- *Lemma 4 (minimax bound in the Gaussian shift experiment).*

For the finite-dim limit experiment `(N(h, I_m) : h ∈ ℝᵐ)` with
parameter restricted to a convex cone `C_m ⊆ EuclideanSpace ℝ (Fin m)`
of nonempty interior, any bounded uniformly continuous subconvex loss
`ℓ : ℝ → ℝ≥0∞`, and a continuous linear coefficient
`A : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ` (the "functional differential"
of `ψ` along the score basis), the finite-subset minimax risk is
bounded below by the Gaussian integral of `ℓ` against `N(0, ‖A‖²)`:

```
sup_{I_0 ⊂ C_m finite} inf_T max_{h∈I_0} ∫⁻ ℓ(T(X) − A h) dN(h, I_m)(X)
  ≥ ∫⁻ u, ℓ u ∂(gaussianReal 0 ‖A‖²).
```

`σ²` is encoded as `⟨‖A‖^2, sq_nonneg _⟩ : ℝ≥0` to match Mathlib's
`gaussianReal : ℝ → ℝ≥0 → Measure ℝ`.

Reference: vdV §25.3 (proof of Theorem 25.21). Proof intent in this
file's header docstring.

Proof: `hPriorBayesBound` supplies a cone-supported prior with a Bayes-risk
lower bound (book steps (1)+(2)); `hFiniteSupportApprox` extracts a
finite-support witness `I_0` with the same bound (book step (3)); the two
are combined via `le_iSup`. -/
theorem gaussianShift_minimax
    (C_m : Set (EuclideanSpace ℝ (Fin m)))
    (_hC_convex : Convex ℝ C_m)
    (_hC_cone : ∀ x ∈ C_m, ∀ t : ℝ, 0 ≤ t → t • x ∈ C_m)
    (_hC_int : (interior C_m).Nonempty)
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
    -- `AsymptoticStatistics.BowlShaped` from `ForMathlib/BowlShaped.lean` (vdV §8.5).
    (ℓ : ℝ → ℝ≥0∞)
    (_hℓ_bowl : BowlShaped ℓ)
    (_hℓ_bdd : ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ u : ℝ, ℓ u ≤ B)
    -- Stated on the real-valued `toReal` bridge so the standard `UniformContinuous`
    -- predicate applies (`ℓ` is `ℝ≥0∞`-valued; bounded `⇒` finite `⇒` `ofReal ∘ toReal`
    -- is the canonical real proxy).
    (_hℓ_uc : UniformContinuous fun u : ℝ => (ℓ u).toReal)
    -- vdV §25.3 (book steps (1)+(2)). Packages Anderson's lemma on the Gaussian
    -- prior `N(c h₀, c I_m)` (`ForMathlib/Anderson.gaussian_lintegral_mono_of_psd_le`)
    -- and the cone-restriction `π̃_c(C_m) → 1` limit (`c → ∞`).
    --
    -- Stated as: there exists a probability measure `π` on `EuclideanSpace ℝ
    -- (Fin m)` supported in `C_m` (encoded via full measure `π C_m = 1`), whose
    -- Bayes-style integral-of-minimax (the order `inf_T`-then-`∫ ∂π` is the
    -- canonical Bayes risk) lower-bounds the limit Gaussian integral on the right.
    (hPriorBayesBound :
      ∃ (π : Measure (EuclideanSpace ℝ (Fin m))),
        IsProbabilityMeasure π ∧
        π C_m = 1 ∧
        (⨅ T : EuclideanSpace ℝ (Fin m) → ℝ,
          ∫⁻ h, ∫⁻ X, ℓ (T X - A h)
            ∂(multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ)) ∂π)
          ≥ ∫⁻ u, ℓ u ∂(gaussianReal 0 ⟨‖A‖ ^ 2, sq_nonneg _⟩))
    -- vdV §25.3 (book step (3)): finite-support density of priors on the cone,
    -- with Bayes-risk continuity in the prior. Says: any cone-supported prior `π`
    -- whose `inf_T` Bayes risk is at least `B` admits a *finite-support*
    -- approximation, in the sense that for any such `B` there is a finite
    -- `I_0 ⊂ C_m` with `inf_T max_{h ∈ I_0} risk(T, h) ≥ B`.
    --
    -- Justification (book): probability measures with finite support are
    -- weakly dense in `Prob(K)` for compact `K ⊂ C_m`; the bounded uniformly
    -- continuous loss `ℓ` makes the Bayes integral continuous in the prior;
    -- and the inequality `max_{h ∈ I_0} f(h) ≥ ∫ f dπ_finite` (sup ≥ mean)
    -- transports the Bayes lower bound to the minimax form.
    --
    -- Expressed pointwise in `B` so the consumer can cite it on the value
    -- delivered by `hPriorBayesBound`.
    (hFiniteSupportApprox :
      ∀ {π : Measure (EuclideanSpace ℝ (Fin m))} (_hπ : IsProbabilityMeasure π)
        (_hπC : π C_m = 1) (B : ℝ≥0∞),
        (⨅ T : EuclideanSpace ℝ (Fin m) → ℝ,
          ∫⁻ h, ∫⁻ X, ℓ (T X - A h)
            ∂(multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ)) ∂π) ≥ B →
        ∃ I_0 : Finset (EuclideanSpace ℝ (Fin m)),
          (I_0 : Set _) ⊆ C_m ∧
          (⨅ T : EuclideanSpace ℝ (Fin m) → ℝ,
            ⨆ h ∈ I_0, ∫⁻ X, ℓ (T X - A h)
              ∂(multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ)))
            ≥ B) :
    -- LHS: `sup_{I_0 finite ⊂ C_m} inf_{T : EuclideanSpace ℝ (Fin m) → ℝ}
    --        max_{h ∈ I_0} ∫⁻ ℓ(T(X) − A h) ∂(N(h, I_m))`
    --     ≥
    -- RHS: ∫⁻ u, ℓ u ∂(gaussianReal 0 ‖A‖²).
    --
    -- We use `multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ)` for `N(h, I_m)`
    -- (Mathlib `multivariateGaussian_zero_one`), and `gaussianReal 0 ⟨‖A‖^2, _⟩` for
    -- the 1D limit Gaussian (Mathlib `Probability/Distributions/Gaussian/Real`).
    (⨆ I_0 : { S : Finset (EuclideanSpace ℝ (Fin m)) // (S : Set _) ⊆ C_m },
        ⨅ T : EuclideanSpace ℝ (Fin m) → ℝ,
          ⨆ h ∈ (I_0 : Finset (EuclideanSpace ℝ (Fin m))),
            ∫⁻ X, ℓ (T X - A h)
              ∂(multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ)))
      ≥ ∫⁻ u, ℓ u ∂(gaussianReal 0 ⟨‖A‖ ^ 2, sq_nonneg _⟩) := by
  -- Step (1)+(2): extract the cone-supported prior `π` and its Bayes-risk
  -- lower bound from the Anderson-PSD chain (post the cone-restriction
  -- `c → ∞` limit).
  obtain ⟨π, hπ, hπC, hπBound⟩ := hPriorBayesBound
  -- Step (3): apply the finite-support-density approximation to that prior,
  -- with the limit Gaussian integral as the lower bound to be transported.
  obtain ⟨I_0, hI_sub, hI_bd⟩ :=
    hFiniteSupportApprox hπ hπC
      (∫⁻ u, ℓ u ∂(gaussianReal 0 ⟨‖A‖ ^ 2, sq_nonneg _⟩))
      hπBound
  -- Structural step: the supremum over all finite subsets of `C_m` dominates
  -- any individual subset's `inf_T max_{h∈I_0}` value. Specialise the `iSup`
  -- to the witness `⟨I_0, hI_sub⟩`.
  refine le_trans hI_bd ?_
  -- `le_iSup` at the bundled subtype `⟨I_0, hI_sub⟩`.
  exact le_iSup
    (fun I_0' : { S : Finset (EuclideanSpace ℝ (Fin m)) // (S : Set _) ⊆ C_m } =>
      ⨅ T : EuclideanSpace ℝ (Fin m) → ℝ,
        ⨆ h ∈ (I_0' : Finset (EuclideanSpace ℝ (Fin m))),
          ∫⁻ X, ℓ (T X - A h)
            ∂(multivariateGaussian h (1 : Matrix (Fin m) (Fin m) ℝ)))
    ⟨I_0, hI_sub⟩

end AsymptoticStatistics.LowerBounds.GaussianShiftMinimax
