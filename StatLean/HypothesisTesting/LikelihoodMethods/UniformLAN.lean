import StatLean.HypothesisTesting.LikelihoodMethods.EstimatorUnderAlternatives

/-!
# The local asymptotic normality expansion, uniformly over bounded directions

The quadratic expansion of the log-likelihood ratio
$$ \log L_{n,h} \;=\; \langle h, Z_n\rangle - \tfrac12\langle h, I(\theta_0)h\rangle + o_P(1)
   \qquad (L_{n,h} = L_n(\theta_0 + h/\sqrt n)/L_n(\theta_0)) $$
holds under quadratic-mean differentiability for each **fixed** direction `h`. Arguments that
substitute a *random* direction — most importantly `ĥₙ = √n(θ̂ₙ − θ₀)` in the analysis of the
likelihood ratio statistic — need the remainder to be small **uniformly over `‖h‖ ≤ c`**:
$$ \epsilon_{n,c} \;=\; \sup_{\|h\|\le c}
   \Bigl|\log L_{n,h} - \bigl[\langle h, Z_n\rangle
     - \tfrac12 \langle h, I(\theta_0) h\rangle\bigr]\Bigr| \;\xrightarrow{P}\; 0 . $$
This file states that uniform version, under quadratic-mean differentiability together with
the second-order envelope condition
$$ \bigl|\log p_\theta(x) - \log p_{\theta_0}(x)
   - \langle \theta - \theta_0, \tilde\eta_{\theta_0}(x)\rangle\bigr|
   \;\le\; M(x)\,\|\theta-\theta_0\|^2, \qquad E_{\theta_0}[M(X)] < \infty, $$
for `θ` in a neighbourhood of `θ₀` — the hypothesis under which the trinity of likelihood
tests is analysed.

**Reference.** E.L. Lehmann and J.P. Romano, *Testing Statistical Hypotheses*, 4th ed.,
Springer Nature Switzerland AG, 2022 (ISBN 978-3-030-70577-0), Chapter 14 (Quadratic Mean
Differentiable Families), §14.2 (Quadratic Mean Differentiability (q.m.d.)), the quadratic
mean differentiability expansion, in the locally asymptotically normal form used uniformly
over bounded directions. (`TSH4 §14.2`.)

**Proof formalization notes.**
* The supremum over the uncountable ball is avoided at statement level: instead of asserting
  that a (possibly non-measurable) supremum converges in probability, the statement says
  that for every `ε > 0` the measure of the event `∃ h, ‖h‖ ≤ c ∧ ε ≤ |remainder|` tends to
  zero. Quantified over all `ε > 0` this is equivalent to `ε_{n,c} →_P 0`, and it needs no
  measurable-selection or separability argument to be well posed. Measures of non-measurable
  sets are the outer measure, so the statement is meaningful as written.
* The envelope condition is transcribed pointwise in `x` (as in the source) rather than
  almost everywhere; the almost-everywhere form is a weaker hypothesis and would give a
  formally stronger theorem, but the pointwise form is what the source assumes and what
  applications verify.
* Both the remainder and the envelope are expressed through the area's `logLikelihood`
  (the log-likelihood ratio of the shifted family on a sample) and `scoreSum` (the
  normalized score sum), so the fixed-`h` case of the statement is exactly the area's
  `lanResidual_tendsto_productMeasure`; the content added here is uniformity in `h`.
* `E_{θ₀}[M(X)] < ∞` is integrability of `M` against `μ.withDensity p_{θ₀}`, the model's
  single-observation law at `θ₀`.

**Bibliographic comments.** The quadratic expansion of the log-likelihood ratio and the local
asymptotic normality framework are due to L. Le Cam ("Locally asymptotically normal families
of distributions," *Univ. California Publ. Statist.* **3** (1960), 37–98), with the
quadratic-mean differentiability hypothesis introduced in L. Le Cam ("On the assumptions used
to prove asymptotic normality of maximum likelihood estimates," *Ann. Math. Statist.* **41**
(1970), 802–828). Uniform-in-direction control of the remainder is the technical device by
which the classical likelihood ratio theory of S. S. Wilks ("The large-sample distribution of
the likelihood ratio for testing composite hypotheses," *Ann. Math. Statist.* **9** (1938),
60–62) is recovered without third-derivative conditions.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open AsymptoticStatistics AsymptoticStatistics.AsymptoticRepresentation
open scoped RealInnerProductSpace ENNReal

namespace StatLean.HypothesisTesting

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {k : ℕ}

/-- The **LAN remainder** in direction `h` on a sample of size `n`:
`log L_{n,h} − (⟪h, Zₙ⟫ − ½⟪h, J h⟫)`, where `L_{n,h}` is the likelihood ratio of the
shifted parameter `θ₀ + h/√n` against `θ₀` and `Zₙ` is the normalized score sum.

Edge behaviour: at `n = 0` the empty sample makes both the log-likelihood ratio and the
score sum vanish, so the remainder is `½⟪h, J h⟫`. -/
noncomputable def lanRemainder (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (θ₀ : EuclideanSpace ℝ (Fin k)) (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    (J : Matrix (Fin k) (Fin k) ℝ) (h : EuclideanSpace ℝ (Fin k)) (n : ℕ)
    (ω : Fin n → 𝓧) : ℝ :=
  logLikelihood M θ₀ h n ω - (⟪h, scoreSum ℓ n ω⟫ - (1 / 2 : ℝ) * ⟪h, mulVecE J h⟫)

/-- **Uniform LAN remainder.**

Under quadratic-mean differentiability at `θ₀` and the second-order envelope condition, the
LAN remainder is uniformly small over every bounded set of directions: for every radius
`c > 0` and every `ε > 0`, the `P^n_{θ₀}`-probability that some direction `h` with `‖h‖ ≤ c`
has remainder at least `ε` tends to zero.

This is the statement consumed by the likelihood ratio analysis, where the direction is the
random `ĥₙ = √n(θ̂ₙ − θ₀)`, bounded in probability but not fixed. -/
theorem sup_LAN_remainder_tendsto
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    -- LEAN-ONLY: instance plumbing for the i.i.d. laws; forced by `hPDF` through
    -- `productMeasure_isProbabilityMeasure`
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n,
      IsProbabilityMeasure (productMeasure M μ θ n)]
    -- USER-INPUT: the densities normalize and are integrable; the model is a density family
    (hPDF : IsPDFOf M μ)
    -- USER-INPUT: the parameter at which the expansion is taken
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
    -- USER-INPUT: the envelope function of the second-order expansion
    (Menv : 𝓧 → ℝ)
    -- LEAN-ONLY: measurability of the envelope; standard regularity
    (hMenv_meas : Measurable Menv)
    -- USER-INPUT: the envelope has finite mean under the model at `θ₀`
    (hMenv_int :
      Integrable Menv (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
    -- USER-INPUT: radius of the neighbourhood on which the envelope condition holds
    (δ : ℝ) (hδ : 0 < δ)
    -- USER-INPUT: second-order envelope condition on the log-density increment
    (henv : ∀ θ : EuclideanSpace ℝ (Fin k), ‖θ - θ₀‖ ≤ δ → ∀ x : 𝓧,
      |Real.log (M.density θ x) - Real.log (M.density θ₀ x) - ⟪θ - θ₀, ℓ x⟫|
        ≤ Menv x * ‖θ - θ₀‖ ^ 2)
    -- USER-INPUT: the radius of the ball of directions over which uniformity is claimed
    (c : ℝ) (hc : 0 < c) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 | ∃ h : EuclideanSpace ℝ (Fin k),
          ‖h‖ ≤ c ∧ ε ≤ |lanRemainder M θ₀ ℓ J h n ω|})
        atTop (𝓝 0) := by
  sorry

end StatLean.HypothesisTesting
