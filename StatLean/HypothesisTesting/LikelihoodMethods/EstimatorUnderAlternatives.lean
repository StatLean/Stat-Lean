import StatLean.AsymptoticStatistics.LocalAsymptoticNormality.AsymptoticRepresentation
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# Efficient estimators under local alternatives

Let `X₁, …, Xₙ` be i.i.d. from a model that is differentiable in quadratic mean at `θ₀` with
nonsingular Fisher information `I(θ₀)`, and let `θ̂ₙ` be an **asymptotically linear**
(efficient) estimator sequence, i.e. one satisfying, under `P^n_{θ₀}`,
$$ \sqrt{n}\,(\hat\theta_n - \theta_0) \;=\; I^{-1}(\theta_0)\, Z_n + o_{P}(1), \qquad
   Z_n = \frac{1}{\sqrt n}\sum_{i\le n} \tilde\eta_{\theta_0}(X_i) $$
(`Z_n` the normalized score). The expansion is assumed **only at `θ₀`**; the point of this
file is that it nevertheless determines the limiting behaviour of `θ̂ₙ` along every local
alternative sequence `θₙ = θ₀ + hₙ/√n` (`hₙ → h`), because the local experiments are
mutually contiguous:

* `weak_limit_estimator_under_local_alternatives` — `√n(θ̂ₙ − θₙ) ⇝ N(0, I⁻¹(θ₀))` under
  `P^n_{θₙ}`;
* `weak_limit_estimator_centered_under_local_alternatives` — equivalently
  `√n(θ̂ₙ − θ₀) ⇝ N(h, I⁻¹(θ₀))` under `P^n_{θₙ}`;
* `weak_limit_g_estimator_under_local_alternatives` — the delta-method consequence
  `√n(g(θ̂ₙ) − g(θₙ)) ⇝ N(0, ġ(θ₀)I⁻¹(θ₀)ġ(θ₀)ᵀ)` for a differentiable real `g` with
  nonvanishing gradient.

This "weak robustness" of the limiting law under perturbations of size `n^{-1/2}` is what
makes such estimator sequences usable as the backbone of asymptotic testing theory.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 14 (Quadratic Mean
Differentiable Families), §14.4 (Likelihood Methods in Parametric Models), Theorem 14.4.1
(§14.4.1, Efficient Likelihood Estimation): the limit law of an asymptotically linear
estimator under `θ₀ + h/√n`. (`TSH4 §14.4 Thm 14.4.1`.)

**Proof formalization notes.**
* Statements are built on the area conventions of the asymptotic-statistics development:
  the model is a `ParametricFamily` with a dominating measure and `IsPDFOf`, the i.i.d.
  law of the sample is `productMeasure M μ θ n` on `Fin n → 𝓧`, the score sum is
  `scoreSum ℓ n`, weak convergence is `WeakConverges`, and quadratic-mean
  differentiability is `DifferentiableQuadraticMean`. The parameter set is the whole of
  `EuclideanSpace ℝ (Fin k)`, which is open, so the source's "Ω an open subset of `ℝᵏ`"
  needs no separate hypothesis.
* `o_P(1)` along a triangular array cannot be `TendstoInMeasure` (each `n` lives on its own
  sample space), so it is spelled out as the measure of the exceptional event tending to
  zero — the same shape as the area's LAN-residual statement.
* The Fisher information enters as a matrix `J` tied to the bilinear form
  `fisherInformation` by `hJ`, matching the area's convention; `mulVecE` is that
  convention's `(WithLp.equiv 2 _).symm ∘ mulVec ∘ (WithLp.equiv 2 _)` sandwich, given a
  name so that the statements below stay readable (it unfolds definitionally, so the
  area's lemmas apply after `simp only [mulVecE]`).
* Nonsingularity of the information matrix is `IsUnit J.det`, matching the source's
  "nonsingular"; the stronger `Matrix.PosDef J` is used only where the source says
  "positive definite".
* The proof route is: contiguity of `P^n_{θₙ}` to `P^n_{θ₀}` (from quadratic-mean
  differentiability) plus Le Cam's third lemma, applied to the pair
  `(⟪I⁻¹(θ₀)Z_n, t⟫, log L_{n,h})`, followed by the Cramér–Wold device.

**Bibliographic comments.** Contiguity, local asymptotic normality and the third lemma are
due to L. Le Cam ("Locally asymptotically normal families of distributions," *Univ.
California Publ. Statist.* **3** (1960), 37–98), with quadratic-mean differentiability
introduced in L. Le Cam ("On the assumptions used to prove asymptotic normality of maximum
likelihood estimates," *Ann. Math. Statist.* **41** (1970), 802–828). The systematic use of
contiguity to transfer limit laws to local alternatives, and the notion of a regular
estimator sequence, are due to J. Hájek ("Asymptotically most powerful rank-order tests,"
*Ann. Math. Statist.* **33** (1962), 1124–1147).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open AsymptoticStatistics AsymptoticStatistics.AsymptoticRepresentation
open scoped RealInnerProductSpace ENNReal

namespace StatLean.HypothesisTesting

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {k : ℕ}

/-- The action of a `k × k` matrix on `EuclideanSpace ℝ (Fin k)`, transported through the
`WithLp` equivalence: `mulVecE J v = J·v`. This is the sandwich in which the Fisher
information matrix is tied to the Fisher information bilinear form throughout the
asymptotic development; it is given a name only for readability and unfolds
definitionally. -/
noncomputable def mulVecE (J : Matrix (Fin k) (Fin k) ℝ) (v : EuclideanSpace ℝ (Fin k)) :
    EuclideanSpace ℝ (Fin k) :=
  (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))

/-- The **local alternative sequence** `θₙ = θ₀ + hₙ/√n`. At `n = 0` the scaling factor
`(√0)⁻¹ = 0`, so `localAlt θ₀ h_n 0 = θ₀`. -/
noncomputable def localAlt (θ₀ : EuclideanSpace ℝ (Fin k))
    (h_n : ℕ → EuclideanSpace ℝ (Fin k)) (n : ℕ) : EuclideanSpace ℝ (Fin k) :=
  θ₀ + (Real.sqrt n)⁻¹ • h_n n

/-- **Asymptotic linearity (efficiency) of an estimator sequence at `θ₀`.**

`√n(θ̂ₙ − θ₀) = I⁻¹(θ₀)·Zₙ + o_P(1)` under the i.i.d. law `P^n_{θ₀}`, where `Zₙ` is the
normalized score sum. The `o_P(1)` is spelled as: for every `ε > 0` the `P^n_{θ₀}`-measure
of the event that the remainder has norm at least `ε` tends to `0`.

Estimator sequences with this property are exactly those the asymptotic testing theory calls
efficient; maximum likelihood estimators and one-step estimators satisfy it under classical
smoothness conditions, but the property — not any particular construction — is what the
theorems consume.

Edge behaviour: `J⁻¹` is the `Matrix` inverse, which is the junk value `0` when `J` is
singular; the theorems consuming this predicate all assume `J` nonsingular, and with a
singular `J` the condition degenerates to `√n(θ̂ₙ − θ₀) →_P 0`. -/
def IsAsymptoticallyLinear (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (μ : Measure 𝓧) (θ₀ : EuclideanSpace ℝ (Fin k)) (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    (J : Matrix (Fin k) (Fin k) ℝ)
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k)) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
      {ω : Fin n → 𝓧 |
        ε ≤ ‖Real.sqrt n • (est n ω - θ₀) - mulVecE J⁻¹ (scoreSum ℓ n ω)‖})
      atTop (𝓝 0)

/-- **Limit law of an efficient estimator under local alternatives.**

Under `P^n_{θₙ}` with `θₙ = θ₀ + hₙ/√n` and `hₙ → h`, the recentred estimator
`√n(θ̂ₙ − θₙ)` converges weakly to `N(0, I⁻¹(θ₀))` — the same law as under `θ₀`. -/
theorem weak_limit_estimator_under_local_alternatives
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    -- LEAN-ONLY: instance plumbing for the i.i.d. laws; forced by `hPDF` through
    -- `productMeasure_isProbabilityMeasure`
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n,
      IsProbabilityMeasure (productMeasure M μ θ n)]
    -- USER-INPUT: the densities normalize and are integrable; the model is a density family
    (hPDF : IsPDFOf M μ)
    -- USER-INPUT: the parameter at which the expansion is assumed
    (θ₀ : EuclideanSpace ℝ (Fin k))
    -- USER-INPUT: the score function of the model at `θ₀`
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the score; standard regularity
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the model is differentiable in quadratic mean at `θ₀` with score `ℓ`
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- USER-INPUT: the Fisher information matrix at `θ₀`
    (J : Matrix (Fin k) (Fin k) ℝ)
    -- LEAN-ONLY: matrix form of the Fisher information bilinear form; the area convention
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    -- USER-INPUT: the Fisher information matrix is nonsingular
    (hJ_inv : IsUnit J.det)
    -- USER-INPUT: the estimator sequence
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the estimators; needed to push measures forward
    (hest : ∀ n, Measurable (est n))
    -- USER-INPUT: the estimator sequence is asymptotically linear at `θ₀`
    (hlin : IsAsymptoticallyLinear M μ θ₀ ℓ J est)
    -- USER-INPUT: the local direction and the converging sequence of directions
    (h : EuclideanSpace ℝ (Fin k)) (h_n : ℕ → EuclideanSpace ℝ (Fin k))
    (hconv : Tendsto h_n atTop (𝓝 h)) :
    WeakConverges
      (fun n => (productMeasure M μ (localAlt θ₀ h_n n) n).map
        (fun ω => Real.sqrt n • (est n ω - localAlt θ₀ h_n n)))
      (multivariateGaussian 0 J⁻¹) := by
  sorry

/-- **Limit law of an efficient estimator under local alternatives, centred at `θ₀`.**

The equivalent form of the previous theorem: under `P^n_{θₙ}`, `√n(θ̂ₙ − θ₀)` converges
weakly to `N(h, I⁻¹(θ₀))`; the local shift `h` appears as the mean. -/
theorem weak_limit_estimator_centered_under_local_alternatives
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    -- LEAN-ONLY: instance plumbing for the i.i.d. laws; forced by `hPDF`
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n,
      IsProbabilityMeasure (productMeasure M μ θ n)]
    -- USER-INPUT: the densities normalize and are integrable
    (hPDF : IsPDFOf M μ)
    -- USER-INPUT: the parameter at which the expansion is assumed
    (θ₀ : EuclideanSpace ℝ (Fin k))
    -- USER-INPUT: the score function of the model at `θ₀`
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the score; standard regularity
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the model is differentiable in quadratic mean at `θ₀` with score `ℓ`
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- USER-INPUT: the Fisher information matrix at `θ₀`
    (J : Matrix (Fin k) (Fin k) ℝ)
    -- LEAN-ONLY: matrix form of the Fisher information bilinear form; the area convention
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    -- USER-INPUT: the Fisher information matrix is nonsingular
    (hJ_inv : IsUnit J.det)
    -- USER-INPUT: the estimator sequence
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the estimators
    (hest : ∀ n, Measurable (est n))
    -- USER-INPUT: the estimator sequence is asymptotically linear at `θ₀`
    (hlin : IsAsymptoticallyLinear M μ θ₀ ℓ J est)
    -- USER-INPUT: the local direction and the converging sequence of directions
    (h : EuclideanSpace ℝ (Fin k)) (h_n : ℕ → EuclideanSpace ℝ (Fin k))
    (hconv : Tendsto h_n atTop (𝓝 h)) :
    WeakConverges
      (fun n => (productMeasure M μ (localAlt θ₀ h_n n) n).map
        (fun ω => Real.sqrt n • (est n ω - θ₀)))
      (multivariateGaussian h J⁻¹) := by
  sorry

/-- **Delta-method form under local alternatives.**

For a differentiable real-valued `g` with nonvanishing gradient `ġ`, the plug-in estimator
satisfies, under `P^n_{θₙ}`,
`√n(g(θ̂ₙ) − g(θₙ)) ⇝ N(0, σ²)` with `σ² = ġ(θ₀)·I⁻¹(θ₀)·ġ(θ₀)ᵀ`. -/
theorem weak_limit_g_estimator_under_local_alternatives
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    -- LEAN-ONLY: instance plumbing for the i.i.d. laws; forced by `hPDF`
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n,
      IsProbabilityMeasure (productMeasure M μ θ n)]
    -- USER-INPUT: the densities normalize and are integrable
    (hPDF : IsPDFOf M μ)
    -- USER-INPUT: the parameter at which the expansion is assumed
    (θ₀ : EuclideanSpace ℝ (Fin k))
    -- USER-INPUT: the score function of the model at `θ₀`
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the score; standard regularity
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the model is differentiable in quadratic mean at `θ₀` with score `ℓ`
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- USER-INPUT: the Fisher information matrix at `θ₀`
    (J : Matrix (Fin k) (Fin k) ℝ)
    -- LEAN-ONLY: matrix form of the Fisher information bilinear form; the area convention
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    -- USER-INPUT: the Fisher information matrix is nonsingular
    (hJ_inv : IsUnit J.det)
    -- USER-INPUT: the estimator sequence, measurable and asymptotically linear at `θ₀`
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k))
    (hest : ∀ n, Measurable (est n))
    (hlin : IsAsymptoticallyLinear M μ θ₀ ℓ J est)
    -- USER-INPUT: the local direction and the converging sequence of directions
    (h : EuclideanSpace ℝ (Fin k)) (h_n : ℕ → EuclideanSpace ℝ (Fin k))
    (hconv : Tendsto h_n atTop (𝓝 h))
    -- USER-INPUT: a differentiable real-valued parameter functional with gradient `gr`
    (g : EuclideanSpace ℝ (Fin k) → ℝ)
    (gr : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k))
    (hg : ∀ θ, HasGradientAt g (gr θ) θ)
    -- USER-INPUT: the gradient does not vanish at `θ₀`
    (hgr_ne : gr θ₀ ≠ 0)
    -- USER-INPUT: the asymptotic variance `σ² = ġ(θ₀)I⁻¹(θ₀)ġ(θ₀)ᵀ`
    (σ : NNReal) (hσ : (σ : ℝ) = ⟪gr θ₀, mulVecE J⁻¹ (gr θ₀)⟫) :
    WeakConverges
      (fun n => (productMeasure M μ (localAlt θ₀ h_n n) n).map
        (fun ω => Real.sqrt n * (g (est n ω) - g (localAlt θ₀ h_n n))))
      (gaussianReal 0 σ) := by
  sorry

end StatLean.HypothesisTesting
