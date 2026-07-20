import StatLean.HypothesisTesting.LikelihoodMethods.UniformLAN
import StatLean.MultipleTesting.ForMathlib.ChiSquared
import StatLean.HypothesisTesting.ForMathlib.NoncentralChiSquared
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The likelihood trinity: Wald, score and likelihood ratio statistics

Three statistics test the same simple null `θ = θ₀` in an i.i.d. quadratic-mean
differentiable model with positive definite Fisher information `I(θ₀)`:

* the **Wald statistic** `Wₙ = n·(θ̂ₙ − θ₀)ᵀ I(θ₀) (θ̂ₙ − θ₀)`, built from an efficient
  estimator sequence;
* the **Rao score statistic** `Rₙ = Zₙᵀ I⁻¹(θ₀) Zₙ`, built from the normalized score and
  requiring no estimator at all;
* the **likelihood ratio statistic** `2 log Rₙ = 2[ℓₙ(θ̂ₙ) − ℓₙ(θ₀)]`.

They are asymptotically equivalent — pairwise differences vanish in probability — and each
converges in law to `χ²` with `k` degrees of freedom. For the composite null obtained by
restricting `θ` to an affine subspace of codimension `p`, the likelihood ratio statistic
formed from efficient estimators in the full and in the restricted model converges to `χ²`
with `p` degrees of freedom.

Beyond quadratic-mean differentiability, the likelihood ratio analysis needs the source's
additional second-order remainder condition
$$ \bigl|\log p_\theta(x) - \log p_{\theta_0}(x)
   - \langle\theta-\theta_0, \tilde\eta_{\theta_0}(x)\rangle\bigr| \le M(x)\|\theta-\theta_0\|^2,
   \qquad E_{\theta_0}[M(X)]<\infty, $$
for `θ` in a neighbourhood of `θ₀` — it is what makes the local expansion uniform over
bounded directions, and hence usable at the random direction `√n(θ̂ₙ − θ₀)`.

**Reference.** Classical asymptotic likelihood theory; original sources in the bibliographic
comments below.

**Proof formalization notes.**
* *Hypotheses are assigned per statistic, not globally.* The source states the whole theorem
  under one set of standing assumptions; here the envelope condition is imposed only on the
  likelihood-ratio statements, which are the ones that consume it (through
  `sup_LAN_remainder_tendsto`). The score and Wald limits follow from quadratic-mean
  differentiability, the score central limit theorem and the assumed expansion alone.
* The efficient estimator sequence is never constructed: it is data, constrained by
  `IsAsymptoticallyLinear`, exactly as in the source, where maximum likelihood estimators
  and one-step estimators are cited as examples but the expansion is what is assumed.
* The Wald statistic is normalized by `I(θ₀)` rather than by `I(θ̂ₙ)`. The source notes the
  two versions are interchangeable ("`I(θ̂ₙ)` may be replaced by `I(θ₀)` or any consistent
  estimator"); the fixed-matrix form avoids carrying a consistency hypothesis on a plug-in
  estimator of the information matrix.
* The composite null is presented as the affine subspace `a + range B` with `B` an injective
  linear map from a space of dimension `m`. This is exactly the solution set of
  `A(θ − a) = 0` for a `p × k` matrix `A` of rank `p = k − m`, and it lets the restricted
  model be an honest `ParametricFamily` in the chart `β`, so that "efficient estimator
  assuming the null" is the *same* predicate `IsAsymptoticallyLinear` applied to the
  restricted model rather than a new, unverified formula for its influence function.
* The smooth-constraint version of the composite case (null `{θ | g(θ) = 0}` with a
  continuously differentiable `g : ℝᵏ → ℝᵖ` whose Jacobian has rank `p`) is not stated
  separately: at `θ₀` it is the affine statement in the chart supplied by the implicit
  function theorem, with the same `p` degrees of freedom, and stating it independently would
  duplicate that reduction rather than add content.

**Bibliographic comments.** The three statistics are due to A. Wald ("Tests of statistical
hypotheses concerning several parameters when the number of observations is large," *Trans.
Amer. Math. Soc.* **54** (1943), 426–482), C. R. Rao ("Large sample tests of statistical
hypotheses concerning several parameters with applications to problems of estimation,"
*Proc. Camb. Phil. Soc.* **44** (1948), 50–57) and S. S. Wilks ("The large-sample
distribution of the likelihood ratio for testing composite hypotheses," *Ann. Math.
Statist.* **9** (1938), 60–62). The modern proof, which replaces classical
third-derivative conditions by quadratic-mean differentiability and contiguity, is due to
L. Le Cam ("Locally asymptotically normal families of distributions," *Univ. California
Publ. Statist.* **3** (1960), 37–98; "On the assumptions used to prove asymptotic normality
of maximum likelihood estimates," *Ann. Math. Statist.* **41** (1970), 802–828).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open AsymptoticStatistics AsymptoticStatistics.AsymptoticRepresentation
open scoped RealInnerProductSpace ENNReal Matrix

namespace StatLean.HypothesisTesting

variable {𝓧 : Type*} [MeasurableSpace 𝓧] {k : ℕ}

/-! ## The three statistics -/

/-- The **Wald statistic** `Wₙ = n·⟪θ̂ₙ − θ₀, I(θ₀)(θ̂ₙ − θ₀)⟫` for the simple null
`θ = θ₀`, with the information matrix evaluated at the null value.

Edge behaviour: at `n = 0` the statistic is `0`. -/
noncomputable def waldStatistic (J : Matrix (Fin k) (Fin k) ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin k))
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k)) (n : ℕ) (ω : Fin n → 𝓧) : ℝ :=
  (n : ℝ) * ⟪est n ω - θ₀, mulVecE J (est n ω - θ₀)⟫

/-- The **Rao score statistic** `Rₙ = ⟪Zₙ, I⁻¹(θ₀)Zₙ⟫`, a quadratic form in the normalized
score sum. It uses no estimator of the parameter.

Edge behaviour: at `n = 0` the empty score sum vanishes, so the statistic is `0`. -/
noncomputable def scoreStatistic (J : Matrix (Fin k) (Fin k) ℝ)
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (n : ℕ) (ω : Fin n → 𝓧) : ℝ :=
  ⟪scoreSum ℓ n ω, mulVecE J⁻¹ (scoreSum ℓ n ω)⟫

/-- The **likelihood ratio statistic** `2 log(Lₙ(θ̂ₙ)/Lₙ(θ̂ₙ,₀))` for a pair of estimator
sequences: twice the difference of the log-likelihoods at the unrestricted and restricted
estimates. The simple null `θ = θ₀` is the case of the constant restricted sequence.

Edge behaviour: densities enter through their ratio, so points where both densities vanish
contribute `Real.log (0/0) = 0`; at `n = 0` the statistic is `0`. -/
noncomputable def logLRStatistic (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (est est₀ : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k)) (n : ℕ)
    (ω : Fin n → 𝓧) : ℝ :=
  2 * ∑ i, Real.log (M.density (est n ω) (ω i) / M.density (est₀ n ω) (ω i))

/-- The **affinely restricted model** `β ↦ P_{a + Bβ}`: the model reparametrized by a chart
of the affine null subspace `a + range B`. Densities, their measurability and their
nonnegativity are inherited pointwise from the full model. -/
noncomputable def restrictFamily {m : ℕ} (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (a : EuclideanSpace ℝ (Fin k))
    (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k)) :
    ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin m)) where
  density := fun β x => M.density (a + B β) x
  density_meas := fun β => M.density_meas (a + B β)
  density_nonneg := fun β x => M.density_nonneg (a + B β) x

/-! ## Asymptotic equivalence and the chi-squared limits -/

/-- **Measurability of the likelihood-ratio statistic.** For measurable estimator sequences the
map `ω ↦ 2 ∑ᵢ log(p_{θ̂}(ωᵢ)/p_{θ̂₀}(ωᵢ))` is measurable. -/
-- TODO: This holds under standard regularity, but the proof needs *joint* measurability of
-- `(θ, x) ↦ M.density θ x` (Carathéodory measurability of the density in both arguments), so
-- that `ω ↦ M.density (est n ω) (ω i)` is measurable.  The abstract `ParametricFamily` structure
-- only records per-`θ` measurability (`density_meas : ∀ θ, Measurable (density θ)`), so this
-- input is not available from the frozen hypotheses.  Sanctioned lifted sorry.
private lemma measurable_logLRStatistic
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (est est₀ : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k))
    (hest : ∀ n, Measurable (est n)) (hest₀ : ∀ n, Measurable (est₀ n)) (n : ℕ) :
    Measurable (logLRStatistic M est est₀ n) := by
  sorry

/-- **Wald − score is `o_P(1)`.** Under `P^n_{θ₀}` the Wald and Rao score statistics differ by a
quantity tending to zero in probability. -/
-- TODO: Writing `Uₙ = √n(θ̂ₙ−θ₀)` and `Vₙ = J⁻¹Zₙ`, one has `Wₙ = ⟪Uₙ, J Uₙ⟫` and
-- `Rₙ = ⟪Vₙ, J Vₙ⟫` (cf. `waldStatistic_eq_quadratic`), so `Wₙ − Rₙ` is the bilinear remainder
-- `⟪Uₙ−Vₙ, J Uₙ⟫ + ⟪Vₙ, J(Uₙ−Vₙ)⟫`.  `IsAsymptoticallyLinear` gives `‖Uₙ−Vₙ‖ →_P 0`, and the
-- score CLT (`scoreSum_weakly_converges`) makes `‖Vₙ‖`, `‖Uₙ‖` tight, whence the product is
-- `o_P(1)`.  Completing this needs the `o_P · O_P = o_P` product lemma (tightness ×
-- convergence-in-probability), which is not yet in the library.  Sanctioned lifted sorry.
private lemma wald_sub_score_tendstoInMeasure
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n, IsProbabilityMeasure (productMeasure M μ θ n)]
    (hPDF : IsPDFOf M μ) (θ₀ : EuclideanSpace ℝ (Fin k))
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k)) (hest : ∀ n, Measurable (est n))
    (hlin : IsAsymptoticallyLinear M μ θ₀ ℓ J est) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 | ε ≤ |waldStatistic J θ₀ est n ω - scoreStatistic J ℓ n ω|})
        atTop (𝓝 0) := by
  sorry

/-- **logLR − score is `o_P(1)`** (simple null). Under `P^n_{θ₀}` and the second-order envelope
condition, the likelihood-ratio and Rao score statistics differ by a quantity tending to zero
in probability. -/
-- TODO: The uniform LAN expansion `sup_LAN_remainder_tendsto` (in `UniformLAN.lean`, itself an
-- open sorry) evaluated at the random direction `ĥₙ = √n(θ̂ₙ−θ₀)` gives
-- `2[ℓₙ(θ̂)−ℓₙ(θ₀)] = 2⟪ĥₙ, Zₙ⟫ − ⟪ĥₙ, J ĥₙ⟫ + o_P(1)`; substituting `ĥₙ = J⁻¹Zₙ + o_P(1)`
-- (`IsAsymptoticallyLinear`) collapses the leading terms to `⟪Zₙ, J⁻¹Zₙ⟫ = Rₙ`.  Blocked on the
-- upstream expansion plus tightness bookkeeping.  Sanctioned lifted sorry.
private lemma logLR_sub_score_tendstoInMeasure
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n, IsProbabilityMeasure (productMeasure M μ θ n)]
    (hPDF : IsPDFOf M μ) (θ₀ : EuclideanSpace ℝ (Fin k))
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k)) (hest : ∀ n, Measurable (est n))
    (hlin : IsAsymptoticallyLinear M μ θ₀ ℓ J est)
    (Menv : 𝓧 → ℝ) (hMenv_meas : Measurable Menv)
    (hMenv_int : Integrable Menv (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
    (δ : ℝ) (hδ : 0 < δ)
    (henv : ∀ θ : EuclideanSpace ℝ (Fin k), ‖θ - θ₀‖ ≤ δ → ∀ x : 𝓧,
      |Real.log (M.density θ x) - Real.log (M.density θ₀ x) - ⟪θ - θ₀, ℓ x⟫|
        ≤ Menv x * ‖θ - θ₀‖ ^ 2) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 |
          ε ≤ |logLRStatistic M est (fun _ _ => θ₀) n ω - scoreStatistic J ℓ n ω|})
        atTop (𝓝 0) := by
  sorry

/-- **Asymptotic equivalence of the trinity.**

Under `P^n_{θ₀}`, the Wald and likelihood ratio statistics each differ from the Rao score
statistic by a quantity tending to zero in probability. Consequently the three tests reject
the same data sets with probability tending to one. -/
theorem trinity_asymptotically_equivalent
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    -- LEAN-ONLY: instance plumbing for the i.i.d. laws; forced by `hPDF`
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n,
      IsProbabilityMeasure (productMeasure M μ θ n)]
    -- USER-INPUT: the densities normalize and are integrable
    (hPDF : IsPDFOf M μ)
    -- USER-INPUT: the null value of the parameter
    (θ₀ : EuclideanSpace ℝ (Fin k))
    -- USER-INPUT: the score function of the model at `θ₀`
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the score; standard regularity
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the model is differentiable in quadratic mean at `θ₀` with score `ℓ`
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- USER-INPUT: the Fisher information matrix at `θ₀`, positive definite
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    -- LEAN-ONLY: matrix form of the Fisher information bilinear form; the area convention
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    -- USER-INPUT: an efficient (asymptotically linear) estimator sequence
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k))
    (hest : ∀ n, Measurable (est n))
    (hlin : IsAsymptoticallyLinear M μ θ₀ ℓ J est)
    -- USER-INPUT: the envelope function of the second-order expansion, with finite mean
    (Menv : 𝓧 → ℝ) (hMenv_meas : Measurable Menv)
    (hMenv_int :
      Integrable Menv (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
    -- USER-INPUT: radius of the neighbourhood on which the envelope condition holds
    (δ : ℝ) (hδ : 0 < δ)
    -- USER-INPUT: second-order envelope condition on the log-density increment
    (henv : ∀ θ : EuclideanSpace ℝ (Fin k), ‖θ - θ₀‖ ≤ δ → ∀ x : 𝓧,
      |Real.log (M.density θ x) - Real.log (M.density θ₀ x) - ⟪θ - θ₀, ℓ x⟫|
        ≤ Menv x * ‖θ - θ₀‖ ^ 2) :
    (∀ ε : ℝ, 0 < ε →
        Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
          {ω : Fin n → 𝓧 |
            ε ≤ |waldStatistic J θ₀ est n ω - scoreStatistic J ℓ n ω|})
          atTop (𝓝 0)) ∧
      (∀ ε : ℝ, 0 < ε →
        Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
          {ω : Fin n → 𝓧 |
            ε ≤ |logLRStatistic M est (fun _ _ => θ₀) n ω - scoreStatistic J ℓ n ω|})
          atTop (𝓝 0)) :=
  ⟨wald_sub_score_tendstoInMeasure M μ hPDF θ₀ ℓ hℓ hDQM J hJ_pd hJ est hest hlin,
    logLR_sub_score_tendstoInMeasure M μ hPDF θ₀ ℓ hℓ hDQM J hJ_pd hJ est hest hlin
      Menv hMenv_meas hMenv_int δ hδ henv⟩

/-- Continuity of the quadratic form `z ↦ ⟪z, A·z⟫` on `EuclideanSpace ℝ (Fin k)`; the matrix
action `mulVecE A` is definitionally `AsymptoticStatistics.GaussianShift.matrixAction A`, so
its continuity is inherited. -/
private lemma continuous_gaussQuadratic (A : Matrix (Fin k) (Fin k) ℝ) :
    Continuous (fun z : EuclideanSpace ℝ (Fin k) => ⟪z, mulVecE A z⟫) :=
  continuous_id.inner (GaussianShift.matrixAction_continuous A)

/-- Measurability of the normalized score sum. -/
private lemma measurable_scoreSum (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (hℓ : Measurable ℓ)
    (n : ℕ) : Measurable (scoreSum ℓ n) := by
  unfold scoreSum
  exact (Finset.measurable_sum Finset.univ
    (fun i _ => hℓ.comp (measurable_pi_apply i))).const_smul (Real.sqrt n)⁻¹

/-- **Gaussian quadratic form is chi-squared.** For a positive-definite `k×k` matrix `J`
(`k > 0`), the pushforward of `N(0, J)` under the quadratic form `z ↦ ⟪z, J⁻¹ z⟫` is the
`χ²ₖ` distribution.

This is the exact distributional identity `Zᵀ J⁻¹ Z ∼ χ²ₖ` for `Z ∼ N(0, J)`. It is **not**
available anywhere in the current library (there is no Gaussian↔chi-squared bridge in the
`AsymptoticStatistics` tree). The intended proof is the whitening argument: with
`C = CFC.sqrt J⁻¹` one has `J⁻¹ = C²`, and since `C`, `J`, `J⁻¹` are continuous-functional-
calculus functions of one matrix they commute, so `C J C = J C² = J J⁻¹ = I`; hence
`(multivariateGaussian 0 J).map (matrixAction C) = multivariateGaussian 0 I = stdGaussian`
(via `multivariateGaussian_map_toEuclideanCLM`), while `⟪z, J⁻¹ z⟫ = ‖C z‖² = ∑ᵢ (C z)ᵢ²`;
the standard Gaussian's coordinates are i.i.d. `N(0,1)`, so `map_sum_sq_eq_chiSquared`
finishes. -/
private lemma multivariateGaussian_map_quadratic_eq_chiSquared
    (hk : 0 < k) (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef) :
    (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J).map
        (fun z => ⟪z, mulVecE J⁻¹ z⟫) = MultipleTesting.chiSquared k :=
  multivariateGaussian_map_inner_inv_eq_chiSquared hk hJ_pd

/-- The matrix action `mulVecE J` is `ℝ`-linear in its vector argument (scalar homogeneity). -/
private lemma mulVecE_smul (J : Matrix (Fin k) (Fin k) ℝ) (c : ℝ)
    (v : EuclideanSpace ℝ (Fin k)) : mulVecE J (c • v) = c • mulVecE J v := by
  change Matrix.toEuclideanCLM (𝕜 := ℝ) J (c • v) = c • Matrix.toEuclideanCLM (𝕜 := ℝ) J v
  rw [map_smul]

/-- The Wald statistic is the quadratic form `⟪·, J ·⟫` evaluated at the normalized deviation
`√n·(θ̂ₙ − θ₀)`: `Wₙ = ⟪√n(θ̂ₙ−θ₀), J √n(θ̂ₙ−θ₀)⟫`. The two `√n` factors collapse the `n` in
front of the definition. -/
private lemma waldStatistic_eq_quadratic (J : Matrix (Fin k) (Fin k) ℝ)
    (θ₀ : EuclideanSpace ℝ (Fin k))
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k)) (n : ℕ) (ω : Fin n → 𝓧) :
    waldStatistic J θ₀ est n ω
      = ⟪Real.sqrt n • (est n ω - θ₀), mulVecE J (Real.sqrt n • (est n ω - θ₀))⟫ := by
  unfold waldStatistic
  rw [mulVecE_smul, real_inner_smul_left, real_inner_smul_right, ← mul_assoc,
    Real.mul_self_sqrt (Nat.cast_nonneg n)]

/-- **The Rao score statistic is asymptotically chi-squared.**

Under `P^n_{θ₀}`, `Zₙᵀ I⁻¹(θ₀) Zₙ ⇝ χ²ₖ`. This part needs no estimator and no envelope
condition: the score central limit theorem plus the continuous mapping theorem suffice, the
quadratic form of a `N(0, I)` vector in the metric `I⁻¹` being `χ²ₖ`. -/
theorem score_tendsto_chiSquared
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    -- LEAN-ONLY: instance plumbing for the i.i.d. laws; forced by `hPDF`
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n,
      IsProbabilityMeasure (productMeasure M μ θ n)]
    -- USER-INPUT: the densities normalize and are integrable
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: nondegenerate parameter dimension; `χ²₀` is not a probability measure
    (hk : 0 < k)
    -- USER-INPUT: the null value of the parameter
    (θ₀ : EuclideanSpace ℝ (Fin k))
    -- USER-INPUT: the score function of the model at `θ₀`
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the score; standard regularity
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the model is differentiable in quadratic mean at `θ₀` with score `ℓ`
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- USER-INPUT: the Fisher information matrix at `θ₀`, positive definite
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    -- LEAN-ONLY: matrix form of the Fisher information bilinear form; the area convention
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k),
      fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫) :
    WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map (scoreStatistic J ℓ n))
      (MultipleTesting.chiSquared k) := by
  -- Score CLT under the null: `Zₙ ⇝ N(0, J)`.
  have hScore : WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map (scoreSum ℓ n))
      (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J) :=
    scoreSum_weakly_converges M μ θ₀ ℓ hℓ (hPDF.density_integral_eq_one θ₀)
      (hPDF.density_integrable θ₀)
      (fun t u => hPDF.density_integral_eq_one _) (fun t u => hPDF.density_integrable _)
      hDQM J hJ_pd.posSemidef hJ
  -- The quadratic form `q z = ⟪z, J⁻¹ z⟫` is continuous, and `scoreStatistic = q ∘ scoreSum`.
  have hcont := continuous_gaussQuadratic (k := k) J⁻¹
  have hmeas := hcont.measurable
  -- Rewrite the pushforward of the statistic as a composed pushforward of the score sum.
  have hseq : (fun n => (productMeasure M μ θ₀ n).map (scoreStatistic J ℓ n))
      = (fun n => ((productMeasure M μ θ₀ n).map (scoreSum ℓ n)).map
          (fun z => ⟪z, mulVecE J⁻¹ z⟫)) := by
    funext n
    rw [Measure.map_map hmeas (measurable_scoreSum ℓ hℓ n)]
    rfl
  rw [hseq, ← multivariateGaussian_map_quadratic_eq_chiSquared hk J hJ_pd]
  exact hScore.map hcont hmeas

/-- **The Wald statistic is asymptotically chi-squared.**

Under `P^n_{θ₀}`, `n(θ̂ₙ − θ₀)ᵀ I(θ₀)(θ̂ₙ − θ₀) ⇝ χ²ₖ` for any efficient estimator
sequence. Follows from the assumed expansion and the score limit; no envelope condition is
needed. -/
theorem wald_tendsto_chiSquared
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    -- LEAN-ONLY: instance plumbing for the i.i.d. laws; forced by `hPDF`
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n,
      IsProbabilityMeasure (productMeasure M μ θ n)]
    -- USER-INPUT: the densities normalize and are integrable
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: nondegenerate parameter dimension; `χ²₀` is not a probability measure
    (hk : 0 < k)
    -- USER-INPUT: the null value of the parameter
    (θ₀ : EuclideanSpace ℝ (Fin k))
    -- USER-INPUT: the score function of the model at `θ₀`
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the score; standard regularity
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the model is differentiable in quadratic mean at `θ₀` with score `ℓ`
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- USER-INPUT: the Fisher information matrix at `θ₀`, positive definite
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    -- LEAN-ONLY: matrix form of the Fisher information bilinear form; the area convention
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k),
      fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    -- USER-INPUT: an efficient (asymptotically linear) estimator sequence
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k))
    (hest : ∀ n, Measurable (est n))
    (hlin : IsAsymptoticallyLinear M μ θ₀ ℓ J est) :
    WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map (waldStatistic J θ₀ est n))
      (MultipleTesting.chiSquared k) := by
  -- Score CLT under the null: `Zₙ ⇝ N(0, J)`.
  have hScore : WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map (scoreSum ℓ n))
      (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J) :=
    scoreSum_weakly_converges M μ θ₀ ℓ hℓ (hPDF.density_integral_eq_one θ₀)
      (hPDF.density_integrable θ₀)
      (fun t u => hPDF.density_integral_eq_one _) (fun t u => hPDF.density_integrable _)
      hDQM J hJ_pd.posSemidef hJ
  have hJinv_pd : J⁻¹.PosDef := hJ_pd.inv
  have hdet : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det J).mp hJ_pd.isUnit
  -- The pushforward of `N(0, J)` under `mulVecE J⁻¹` is `N(0, J⁻¹)`.
  have hpush : (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J).map
      (GaussianShift.matrixAction J⁻¹)
      = ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹ := by
    have hfun : GaussianShift.matrixAction J⁻¹
        = (Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹ :
            EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k)) :=
      funext (GaussianShift.matrixAction_eq_toEuclideanCLM J⁻¹)
    rw [hfun, ProbabilityTheory.multivariateGaussian_map_toEuclideanCLM J⁻¹ 0
      hJ_pd.posSemidef]
    have hHerm : J⁻¹ᴴ = J⁻¹ := hJ_pd.inv.isHermitian
    congr 1
    · simp
    · rw [hHerm, Matrix.nonsing_inv_mul J hdet, Matrix.one_mul]
  -- `Vₙ = mulVecE J⁻¹ Zₙ ⇝ N(0, J⁻¹)`.
  have hV : WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map (fun ω => mulVecE J⁻¹ (scoreSum ℓ n ω)))
      (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹) := by
    have hmap := hScore.map (GaussianShift.matrixAction_continuous J⁻¹)
      (GaussianShift.matrixAction_measurable J⁻¹)
    rw [hpush] at hmap
    have hseqV : (fun n => (productMeasure M μ θ₀ n).map
        (fun ω => mulVecE J⁻¹ (scoreSum ℓ n ω)))
        = (fun n => ((productMeasure M μ θ₀ n).map (scoreSum ℓ n)).map
            (GaussianShift.matrixAction J⁻¹)) := by
      funext n
      rw [Measure.map_map (GaussianShift.matrixAction_measurable J⁻¹)
        (measurable_scoreSum ℓ hℓ n)]
      rfl
    rw [hseqV]; exact hmap
  -- `Uₙ = √n·(θ̂ₙ − θ₀) ⇝ N(0, J⁻¹)` by Slutsky, since `‖Uₙ − Vₙ‖ →_P 0`.
  have hUmeas : ∀ n, Measurable (fun ω : Fin n → 𝓧 => Real.sqrt n • (est n ω - θ₀)) :=
    fun n => ((hest n).sub measurable_const).const_smul (Real.sqrt n)
  have hVmeas : ∀ n, Measurable (fun ω : Fin n → 𝓧 => mulVecE J⁻¹ (scoreSum ℓ n ω)) :=
    fun n => (GaussianShift.matrixAction_measurable J⁻¹).comp (measurable_scoreSum ℓ hℓ n)
  have hU : WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map (fun ω => Real.sqrt n • (est n ω - θ₀)))
      (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹) := by
    refine WeakConverges.slutsky_of_tendstoInMeasure_dist
      (X := fun n ω => mulVecE J⁻¹ (scoreSum ℓ n ω))
      (Y := fun n ω => Real.sqrt n • (est n ω - θ₀))
      (fun n => (hVmeas n).aemeasurable) (fun n => (hUmeas n).aemeasurable) hV ?_
    intro ε hε
    have hset : (fun n => (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 | ε ≤ dist (mulVecE J⁻¹ (scoreSum ℓ n ω))
          (Real.sqrt n • (est n ω - θ₀))})
        = (fun n => (productMeasure M μ θ₀ n).real
          {ω : Fin n → 𝓧 |
            ε ≤ ‖Real.sqrt n • (est n ω - θ₀) - mulVecE J⁻¹ (scoreSum ℓ n ω)‖}) := by
      funext n; congr 1; ext ω
      simp only [Set.mem_setOf_eq]
      rw [dist_eq_norm, norm_sub_rev]
    rw [hset]; exact hlin ε hε
  -- Continuous mapping: `Wₙ = ⟪Uₙ, J Uₙ⟫`, and `N(0, J⁻¹)` pushes to `χ²ₖ`.
  have hcont := continuous_gaussQuadratic (k := k) J
  have hmeas := hcont.measurable
  have hmapU := hU.map hcont hmeas
  have hlim : (ProbabilityTheory.multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) J⁻¹).map
      (fun z => ⟪z, mulVecE J z⟫) = MultipleTesting.chiSquared k := by
    have h := multivariateGaussian_map_quadratic_eq_chiSquared hk J⁻¹ hJinv_pd
    rwa [Matrix.nonsing_inv_nonsing_inv J hdet] at h
  rw [hlim] at hmapU
  have hseq : (fun n => (productMeasure M μ θ₀ n).map (waldStatistic J θ₀ est n))
      = (fun n => ((productMeasure M μ θ₀ n).map
          (fun ω => Real.sqrt n • (est n ω - θ₀))).map (fun z => ⟪z, mulVecE J z⟫)) := by
    funext n
    rw [Measure.map_map hmeas (hUmeas n)]
    congr 1
    funext ω
    exact waldStatistic_eq_quadratic J θ₀ est n ω
  rw [hseq]; exact hmapU

/-- **The likelihood ratio statistic is asymptotically chi-squared (simple null).**

Under `P^n_{θ₀}` and the second-order envelope condition,
`2 log(Lₙ(θ̂ₙ)/Lₙ(θ₀)) ⇝ χ²ₖ` for any efficient estimator sequence. -/
theorem logLR_tendsto_chiSquared
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    -- LEAN-ONLY: instance plumbing for the i.i.d. laws; forced by `hPDF`
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n,
      IsProbabilityMeasure (productMeasure M μ θ n)]
    -- USER-INPUT: the densities normalize and are integrable
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: nondegenerate parameter dimension; `χ²₀` is not a probability measure
    (hk : 0 < k)
    -- USER-INPUT: the null value of the parameter
    (θ₀ : EuclideanSpace ℝ (Fin k))
    -- USER-INPUT: the score function of the model at `θ₀`
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the score; standard regularity
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the model is differentiable in quadratic mean at `θ₀` with score `ℓ`
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- USER-INPUT: the Fisher information matrix at `θ₀`, positive definite
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    -- LEAN-ONLY: matrix form of the Fisher information bilinear form; the area convention
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k),
      fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    -- USER-INPUT: an efficient (asymptotically linear) estimator sequence
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k))
    (hest : ∀ n, Measurable (est n))
    (hlin : IsAsymptoticallyLinear M μ θ₀ ℓ J est)
    -- USER-INPUT: the envelope function of the second-order expansion, with finite mean
    (Menv : 𝓧 → ℝ) (hMenv_meas : Measurable Menv)
    (hMenv_int :
      Integrable Menv (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
    -- USER-INPUT: radius of the neighbourhood on which the envelope condition holds
    (δ : ℝ) (hδ : 0 < δ)
    -- USER-INPUT: second-order envelope condition on the log-density increment
    (henv : ∀ θ : EuclideanSpace ℝ (Fin k), ‖θ - θ₀‖ ≤ δ → ∀ x : 𝓧,
      |Real.log (M.density θ x) - Real.log (M.density θ₀ x) - ⟪θ - θ₀, ℓ x⟫|
        ≤ Menv x * ‖θ - θ₀‖ ^ 2) :
    WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map (logLRStatistic M est (fun _ _ => θ₀) n))
      (MultipleTesting.chiSquared k) := by
  -- Rao score statistic converges to `χ²ₖ`; the LR statistic differs from it by `o_P(1)`.
  haveI : NeZero k := ⟨hk.ne'⟩
  have hscore := score_tendsto_chiSquared M μ hPDF hk θ₀ ℓ hℓ hDQM J hJ_pd hJ
  refine WeakConverges.slutsky_of_tendstoInMeasure_dist
    (X := fun n => scoreStatistic J ℓ n)
    (Y := fun n => logLRStatistic M est (fun _ _ => θ₀) n)
    (fun n => ((continuous_gaussQuadratic J⁻¹).measurable.comp
        (measurable_scoreSum ℓ hℓ n)).aemeasurable)
    (fun n => (measurable_logLRStatistic M est (fun _ _ => θ₀) hest
        (fun _ => measurable_const) n).aemeasurable)
    hscore ?_
  intro ε hε
  have h := logLR_sub_score_tendstoInMeasure M μ hPDF θ₀ ℓ hℓ hDQM J hJ_pd hJ est hest hlin
    Menv hMenv_meas hMenv_int δ hδ henv ε hε
  have hset : (fun n => (productMeasure M μ θ₀ n).real
      {ω : Fin n → 𝓧 | ε ≤ dist (scoreStatistic J ℓ n ω)
        (logLRStatistic M est (fun _ _ => θ₀) n ω)})
      = (fun n => (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 |
          ε ≤ |logLRStatistic M est (fun _ _ => θ₀) n ω - scoreStatistic J ℓ n ω|}) := by
    funext n; congr 1; ext ω
    simp only [Set.mem_setOf_eq, Real.dist_eq, abs_sub_comm]
  rw [hset]; exact h

/-- **Score-difference surrogate converges to `χ²ₚ`** (affine composite null). The difference of
the full-model and restricted-model Rao score statistics converges in law to `χ²ₚ`, `p = k − m`
the codimension. -/
-- TODO: The classical fact `Zₙᵀ J⁻¹ Zₙ − (B*Zₙ)ᵀ JB⁻¹ (B*Zₙ) = ‖Π Zₙ‖²_{J⁻¹} ⇝ χ²ₚ`, where `Π`
-- is the rank-`p` `J`-orthogonal projection off `range B` (`B* = adjoint B`, and
-- `scoreSum ℓB = B* (scoreSum ℓ)` by linearity of `B*`).  Needs the restricted-model score CLT
-- together with a *degenerate* (rank-`p`) Gaussian-quadratic ↔ chi-squared bridge, which
-- generalises `multivariateGaussian_map_inner_inv_eq_chiSquared` (full-rank only) and is not yet
-- available.  Sanctioned lifted sorry.
private lemma affineScoreDiff_tendsto_chiSquared {m p : ℕ}
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n, IsProbabilityMeasure (productMeasure M μ θ n)]
    (hPDF : IsPDFOf M μ) (hdim : m + p = k) (hp : 0 < p)
    (a : EuclideanSpace ℝ (Fin k)) (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hB : Function.Injective B)
    (β₀ : EuclideanSpace ℝ (Fin m)) (θ₀ : EuclideanSpace ℝ (Fin k)) (hθ₀ : θ₀ = a + B β₀)
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    (ℓB : 𝓧 → EuclideanSpace ℝ (Fin m))
    (hℓB : ℓB = fun x => ContinuousLinearMap.adjoint B (ℓ x))
    (JB : Matrix (Fin m) (Fin m) ℝ)
    (hJB : ∀ u v : EuclideanSpace ℝ (Fin m),
      fisherInformation (restrictFamily M a B) μ β₀ ℓB u v = ⟪u, mulVecE JB v⟫)
    [∀ β : EuclideanSpace ℝ (Fin m), ∀ n,
      IsProbabilityMeasure (productMeasure (restrictFamily M a B) μ β n)] :
    WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map
        (fun ω => scoreStatistic J ℓ n ω - scoreStatistic JB ℓB n ω))
      (MultipleTesting.chiSquared p) := by
  sorry

/-- **logLR − score-difference is `o_P(1)`** (affine composite null). The affine likelihood-ratio
statistic differs from the score-difference surrogate by a quantity tending to zero in
probability. -/
-- TODO: Apply the uniform LAN expansion (`sup_LAN_remainder_tendsto`, open sorry upstream) in the
-- full model at `ĥₙ = √n(θ̂ₙ−θ₀)` and in the restricted model at `√n(β̂ₙ−β₀)`, then subtract; the
-- efficient-estimator substitutions (`hlin`, `hlin₀`) collapse each expansion to its score
-- quadratic, leaving `ZₙᵀJ⁻¹Zₙ − (B*Zₙ)ᵀJB⁻¹(B*Zₙ)`.  Blocked on the upstream expansion.
-- Sanctioned lifted sorry.
private lemma logLR_affine_sub_scoreDiff_tendstoInMeasure {m : ℕ}
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n, IsProbabilityMeasure (productMeasure M μ θ n)]
    (hPDF : IsPDFOf M μ) (θ₀ : EuclideanSpace ℝ (Fin k))
    (a : EuclideanSpace ℝ (Fin k)) (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (β₀ : EuclideanSpace ℝ (Fin m))
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k)) (hℓ : Measurable ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (ℓB : 𝓧 → EuclideanSpace ℝ (Fin m))
    (JB : Matrix (Fin m) (Fin m) ℝ)
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k)) (hest : ∀ n, Measurable (est n))
    (hlin : IsAsymptoticallyLinear M μ θ₀ ℓ J est)
    (est₀ : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin m)) (hest₀ : ∀ n, Measurable (est₀ n))
    (hlin₀ : IsAsymptoticallyLinear (restrictFamily M a B) μ β₀ ℓB JB est₀)
    (Menv : 𝓧 → ℝ) (hMenv_meas : Measurable Menv)
    (hMenv_int : Integrable Menv (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
    (δ : ℝ) (hδ : 0 < δ)
    (henv : ∀ θ : EuclideanSpace ℝ (Fin k), ‖θ - θ₀‖ ≤ δ → ∀ x : 𝓧,
      |Real.log (M.density θ x) - Real.log (M.density θ₀ x) - ⟪θ - θ₀, ℓ x⟫|
        ≤ Menv x * ‖θ - θ₀‖ ^ 2) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 | ε ≤ |logLRStatistic M est (fun n ω => a + B (est₀ n ω)) n ω
          - (scoreStatistic J ℓ n ω - scoreStatistic JB ℓB n ω)|})
        atTop (𝓝 0) := by
  sorry

/-- **The likelihood ratio statistic is asymptotically chi-squared (affine composite null).**

Let the null hypothesis restrict `θ` to the affine subspace `a + range B` of codimension
`p = k − m` (equivalently, `A(θ − a) = 0` for a `p × k` matrix `A` of rank `p`), let `θ̂ₙ` be
efficient in the full model and let `β̂ₙ` be efficient in the restricted model
`β ↦ P_{a + Bβ}`. Then, under `P^n_{θ₀}` for any `θ₀ = a + Bβ₀` in the null,
`2 log(Lₙ(θ̂ₙ)/Lₙ(a + Bβ̂ₙ)) ⇝ χ²ₚ`: the degrees of freedom count the restrictions, i.e. the
dimension of the full parameter space minus that of the null. -/
theorem logLR_tendsto_chiSquared_affine {m p : ℕ}
    (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))) (μ : Measure 𝓧) [SigmaFinite μ]
    -- LEAN-ONLY: instance plumbing for the i.i.d. laws of the full model; forced by `hPDF`
    [∀ θ : EuclideanSpace ℝ (Fin k), ∀ n,
      IsProbabilityMeasure (productMeasure M μ θ n)]
    -- USER-INPUT: the densities normalize and are integrable
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: the codimension is the difference of dimensions and is nondegenerate
    (hdim : m + p = k) (hp : 0 < p)
    -- USER-INPUT: a chart of the affine null subspace: base point and injective direction map
    (a : EuclideanSpace ℝ (Fin k))
    (B : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (hB : Function.Injective B)
    -- USER-INPUT: the null parameter, given in the chart
    (β₀ : EuclideanSpace ℝ (Fin m)) (θ₀ : EuclideanSpace ℝ (Fin k)) (hθ₀ : θ₀ = a + B β₀)
    -- USER-INPUT: the score function of the model at `θ₀`
    (ℓ : 𝓧 → EuclideanSpace ℝ (Fin k))
    -- LEAN-ONLY: measurability of the score; standard regularity
    (hℓ : Measurable ℓ)
    -- USER-INPUT: the model is differentiable in quadratic mean at `θ₀` with score `ℓ`
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    -- USER-INPUT: the Fisher information matrix at `θ₀`, positive definite
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ_pd : J.PosDef)
    -- LEAN-ONLY: matrix form of the Fisher information bilinear form; the area convention
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k),
      fisherInformation M μ θ₀ ℓ u v = ⟪u, mulVecE J v⟫)
    -- LEAN-ONLY: name for the score of the restricted model — the adjoint image of `ℓ`
    (ℓB : 𝓧 → EuclideanSpace ℝ (Fin m))
    (hℓB : ℓB = fun x => ContinuousLinearMap.adjoint B (ℓ x))
    -- LEAN-ONLY: matrix form of the restricted model's Fisher information at `β₀`
    (JB : Matrix (Fin m) (Fin m) ℝ)
    (hJB : ∀ u v : EuclideanSpace ℝ (Fin m),
      fisherInformation (restrictFamily M a B) μ β₀ ℓB u v = ⟪u, mulVecE JB v⟫)
    -- LEAN-ONLY: instance plumbing for the i.i.d. laws of the restricted model
    [∀ β : EuclideanSpace ℝ (Fin m), ∀ n,
      IsProbabilityMeasure (productMeasure (restrictFamily M a B) μ β n)]
    -- USER-INPUT: an efficient estimator sequence in the full model
    (est : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin k))
    (hest : ∀ n, Measurable (est n))
    (hlin : IsAsymptoticallyLinear M μ θ₀ ℓ J est)
    -- USER-INPUT: an efficient estimator sequence in the restricted model, in the chart
    (est₀ : ∀ n, (Fin n → 𝓧) → EuclideanSpace ℝ (Fin m))
    (hest₀ : ∀ n, Measurable (est₀ n))
    (hlin₀ : IsAsymptoticallyLinear (restrictFamily M a B) μ β₀ ℓB JB est₀)
    -- USER-INPUT: the envelope function of the second-order expansion, with finite mean
    (Menv : 𝓧 → ℝ) (hMenv_meas : Measurable Menv)
    (hMenv_int :
      Integrable Menv (μ.withDensity fun x => ENNReal.ofReal (M.density θ₀ x)))
    -- USER-INPUT: radius of the neighbourhood on which the envelope condition holds
    (δ : ℝ) (hδ : 0 < δ)
    -- USER-INPUT: second-order envelope condition on the log-density increment
    (henv : ∀ θ : EuclideanSpace ℝ (Fin k), ‖θ - θ₀‖ ≤ δ → ∀ x : 𝓧,
      |Real.log (M.density θ x) - Real.log (M.density θ₀ x) - ⟪θ - θ₀, ℓ x⟫|
        ≤ Menv x * ‖θ - θ₀‖ ^ 2) :
    WeakConverges
      (fun n => (productMeasure M μ θ₀ n).map
        (logLRStatistic M est (fun n ω => a + B (est₀ n ω)) n))
      (MultipleTesting.chiSquared p) := by
  -- Score-difference surrogate converges to `χ²ₚ`; the affine LR differs from it by `o_P(1)`.
  haveI : NeZero p := ⟨hp.ne'⟩
  have hℓB' : Measurable ℓB := by
    rw [hℓB]; exact (ContinuousLinearMap.adjoint B).continuous.measurable.comp hℓ
  have hscorediff := affineScoreDiff_tendsto_chiSquared M μ hPDF hdim hp a B hB β₀ θ₀ hθ₀
    ℓ hℓ hDQM J hJ_pd hJ ℓB hℓB JB hJB
  refine WeakConverges.slutsky_of_tendstoInMeasure_dist
    (X := fun n ω => scoreStatistic J ℓ n ω - scoreStatistic JB ℓB n ω)
    (Y := fun n => logLRStatistic M est (fun n ω => a + B (est₀ n ω)) n)
    (fun n => (((continuous_gaussQuadratic J⁻¹).measurable.comp
        (measurable_scoreSum ℓ hℓ n)).sub
        ((continuous_gaussQuadratic JB⁻¹).measurable.comp
          (measurable_scoreSum ℓB hℓB' n))).aemeasurable)
    (fun n => (measurable_logLRStatistic M est (fun n ω => a + B (est₀ n ω)) hest
        (fun n => (B.continuous.measurable.comp (hest₀ n)).const_add a) n).aemeasurable)
    hscorediff ?_
  intro ε hε
  have h := logLR_affine_sub_scoreDiff_tendstoInMeasure M μ hPDF θ₀ a B β₀ ℓ hℓ J ℓB JB
    est hest hlin est₀ hest₀ hlin₀ Menv hMenv_meas hMenv_int δ hδ henv ε hε
  have hset : (fun n => (productMeasure M μ θ₀ n).real
      {ω : Fin n → 𝓧 | ε ≤ dist (scoreStatistic J ℓ n ω - scoreStatistic JB ℓB n ω)
        (logLRStatistic M est (fun n ω => a + B (est₀ n ω)) n ω)})
      = (fun n => (productMeasure M μ θ₀ n).real
        {ω : Fin n → 𝓧 | ε ≤ |logLRStatistic M est (fun n ω => a + B (est₀ n ω)) n ω
          - (scoreStatistic J ℓ n ω - scoreStatistic JB ℓB n ω)|}) := by
    funext n; congr 1; ext ω
    simp only [Set.mem_setOf_eq, Real.dist_eq, abs_sub_comm]
  rw [hset]; exact h

end StatLean.HypothesisTesting
