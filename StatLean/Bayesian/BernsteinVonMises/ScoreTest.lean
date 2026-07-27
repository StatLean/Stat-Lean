import StatLean.Bayesian.BernsteinVonMises.Defs
import StatLean.ConcentrationInequalities.SubGaussian.Hoeffding
import StatLean.ConcentrationInequalities.SubGaussian.Bounded

/-!
# The truncated-score test (moderate range of Lemma 10.3)

The first half of vdV Lemma 10.3: a test based on the empirical mean of the coordinatewise
**truncated score** `sc^L` detects alternatives in the moderate range
`Mₙ/√n ≤ ‖θ − θ₀‖ ≤ ε` with exponential type-II error.

* `bvmOneObs` — the single-observation law `P_θ = p_θ · μ`;
* `bvmTruncScore` — the coordinatewise clamp of the score to `[−L, L]`;
* `truncScore_mean_expansion` — the DQM differentiation of `θ ↦ P_θ sc^L`:
  `P_θ sc^L − P_{θ₀} sc^L = ∫ ⟪θ−θ₀, sc⟫ sc^L dP_{θ₀} + o(‖θ−θ₀‖)` (via the `L²`
  expansion of `√p_θ` and Cauchy–Schwarz);
* `truncScore_separation` — for a suitable truncation level the mean displacement is bounded
  below: `c‖θ−θ₀‖ ≤ ‖P_θ sc^L − P_{θ₀} sc^L‖` on a neighborhood (the matrix
  `P_{θ₀} sc^L (sc^L)ᵀ` tends to the nonsingular `J` as `L → ∞`);
* `truncScore_empirical_dev_tail` — the Hoeffding tail for the empirical mean of the bounded
  vector `sc^L` under `P^n_θ` (coordinatewise Hoeffding + union bound over `2k` events);
* `exists_moderate_tests` — the headline: measurable `[0,1]`-tests with vanishing size at
  `θ₀` and type-II error `≤ exp(−c n ‖θ−θ₀‖²)` on `Mₙ/√n ≤ ‖θ−θ₀‖ ≤ ε`.

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10, §10.2, proof of
Lemma 10.3, pp. 143–144 (first test sequence `ω_n`; Hoeffding's inequality via Pollard 1984,
Appendix B).

**Proof formalization notes.** The Type-I bound uses Chebyshev (vdV invokes the CLT; the
variance bound suffices since the threshold is `√(Mₙ/n)` with `Mₙ → ∞`). The Type-II bound
uses `StatLean.ConcentrationInequalities.hoeffding` on each coordinate of the centered
truncated score under `P^n_θ` (`ProbabilityTheory.iIndepFun_pi` supplies coordinate
independence on the product), with two one-sided tails per coordinate.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal RealInnerProductSpace
open AsymptoticStatistics (ParametricFamily IsPDFOf DifferentiableQuadraticMean
  fisherInformation)
open AsymptoticStatistics.AsymptoticRepresentation (productMeasure)

namespace StatLean.Bayesian

variable {k : ℕ} {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]
variable {M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))} {μ : Measure 𝓧} [SigmaFinite μ]
variable {θ₀ : EuclideanSpace ℝ (Fin k)} {sc : 𝓧 → EuclideanSpace ℝ (Fin k)}
variable {J : Matrix (Fin k) (Fin k) ℝ}

/-- The single-observation law `P_θ = p_θ · μ` of the dominated model. -/
noncomputable def bvmOneObs (M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k)))
    (μ : Measure 𝓧) (θ : EuclideanSpace ℝ (Fin k)) : Measure 𝓧 :=
  μ.withDensity fun x => ENNReal.ofReal (M.density θ x)

/-- The **coordinatewise truncated score** `sc^L`: each coordinate of `sc` clamped to
`[−L, L]` (vdV p. 143: "the score function truncated to the interval `[−L, L]`"). -/
noncomputable def bvmTruncScore (sc : 𝓧 → EuclideanSpace ℝ (Fin k)) (L : ℝ) :
    𝓧 → EuclideanSpace ℝ (Fin k) :=
  fun x => (WithLp.equiv 2 (Fin k → ℝ)).symm
    (fun i => max (-L) (min L ((WithLp.equiv 2 (Fin k → ℝ)) (sc x) i)))

lemma measurable_bvmTruncScore
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc) (L : ℝ) :
    Measurable (bvmTruncScore sc L) := by
  sorry

lemma norm_bvmTruncScore_le (sc : 𝓧 → EuclideanSpace ℝ (Fin k)) {L : ℝ}
    -- LEAN-ONLY: nonnegative truncation level
    (hL : 0 ≤ L) (x : 𝓧) :
    ‖bvmTruncScore sc L x‖ ≤ Real.sqrt k * L := by
  sorry

/-- **DQM differentiation of the truncated-score mean** (vdV p. 143, "It follows that
`P_θ ℓ̇^L_{θ₀} − P_{θ₀} ℓ̇^L_{θ₀} = (P_{θ₀} ℓ̇^L_{θ₀} ℓ̇^T_{θ₀} + o(1))(θ − θ₀)`"): the map
`θ ↦ P_θ sc^L` is differentiable at `θ₀` with derivative acting as
`u ↦ ∫ ⟪u, sc x⟫ • sc^L x dP_{θ₀}(x)`, in little-o form. -/
theorem truncScore_mean_expansion
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc)
    -- USER-INPUT: differentiability in quadratic mean at θ₀; vdV Thm 10.1
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc) {L : ℝ}
    -- LEAN-ONLY: positive truncation level
    (hL : 0 < L) :
    (fun θ => ∫ x, bvmTruncScore sc L x ∂(bvmOneObs M μ θ)
        - ∫ x, bvmTruncScore sc L x ∂(bvmOneObs M μ θ₀)
        - ∫ x, ⟪θ - θ₀, sc x⟫ • bvmTruncScore sc L x ∂(bvmOneObs M μ θ₀))
      =o[𝓝 θ₀] fun θ => ‖θ - θ₀‖ := by
  sorry

/-- **Mean-displacement separation** (vdV p. 144, top): for a suitable truncation level `L`
the displacement of the truncated-score mean is bounded below by `c‖θ − θ₀‖` on a
neighborhood of `θ₀` (choose `L` with `P_{θ₀} sc^L (sc^L)ᵀ` close enough to the nonsingular
`J`, by dominated convergence). -/
theorem truncScore_separation
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc)
    -- USER-INPUT: differentiability in quadratic mean at θ₀; vdV Thm 10.1
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc)
    -- USER-INPUT: nonsingular Fisher information; vdV Thm 10.1
    (hJ_pd : J.PosDef)
    -- LEAN-ONLY: the abstract Fisher form is the matrix `J` (bridging identity)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ sc u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫) :
    ∃ L ε c : ℝ, 0 < L ∧ 0 < ε ∧ 0 < c ∧
      ∀ θ, ‖θ - θ₀‖ < ε →
        c * ‖θ - θ₀‖ ≤ ‖∫ x, bvmTruncScore sc L x ∂(bvmOneObs M μ θ)
          - ∫ x, bvmTruncScore sc L x ∂(bvmOneObs M μ θ₀)‖ := by
  sorry

/-- **Hoeffding tail for the empirical truncated-score mean** under any `P^n_θ`: for bounded
coordinates (`|sc^L_j| ≤ L`), the deviation of the empirical mean from its `P_θ`-mean
exceeds `s` with probability at most `2k · exp(−n s² / (2 k L²))` (coordinatewise Hoeffding
+ union bound over the `2k` one-sided events). -/
theorem truncScore_empirical_dev_tail
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc) {L : ℝ}
    -- LEAN-ONLY: positive truncation level
    (hL : 0 < L) (θ : EuclideanSpace ℝ (Fin k)) {n : ℕ}
    -- LEAN-ONLY: at least one observation
    (hn : 1 ≤ n) {s : ℝ}
    -- LEAN-ONLY: positive threshold
    (hs : 0 < s) :
    (productMeasure M μ θ n).real
        {ω | s ≤ ‖(n : ℝ)⁻¹ • ∑ i, bvmTruncScore sc L (ω i)
          - ∫ x, bvmTruncScore sc L x ∂(bvmOneObs M μ θ)‖}
      ≤ 2 * k * Real.exp (-(n : ℝ) * s ^ 2 / (2 * k * L ^ 2)) := by
  sorry

/-- **The moderate-range tests** (vdV Lemma 10.3, first test sequence): measurable
`[0,1]`-valued tests `φₙ` with `P^n_{θ₀} φₙ → 0` and, for all large `n`,
`P^n_θ(1 − φₙ) ≤ exp(−c n ‖θ−θ₀‖²)` whenever `Mₙ/√n ≤ ‖θ − θ₀‖ ≤ ε`. -/
theorem exists_moderate_tests
    -- USER-INPUT: dominated iid model with normalized densities; vdV §10.2, p. 140
    (hPDF : IsPDFOf M μ)
    -- LEAN-ONLY: measurable score (regularity)
    (hsc : Measurable sc)
    -- USER-INPUT: differentiability in quadratic mean at θ₀; vdV Thm 10.1
    (hDQM : DifferentiableQuadraticMean M μ θ₀ sc)
    -- USER-INPUT: nonsingular Fisher information; vdV Thm 10.1
    (hJ_pd : J.PosDef)
    -- LEAN-ONLY: the abstract Fisher form is the matrix `J` (bridging identity)
    (hJ : ∀ u v : EuclideanSpace ℝ (Fin k), fisherInformation M μ θ₀ sc u v =
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    {Mseq : ℕ → ℝ}
    -- USER-INPUT: the localization radii diverge; vdV Lemma 10.3 (`Mₙ → ∞`)
    (hM : Tendsto Mseq atTop atTop) :
    ∃ (φ : ∀ n : ℕ, (Fin n → 𝓧) → ℝ) (ε c : ℝ), 0 < ε ∧ 0 < c ∧
      (∀ n, Measurable (φ n)) ∧ (∀ n ω, φ n ω ∈ Set.Icc (0 : ℝ) 1) ∧
      Tendsto (fun n => ∫ ω, φ n ω ∂(productMeasure M μ θ₀ n)) atTop (𝓝 0) ∧
      ∃ N₀ : ℕ, ∀ n, N₀ ≤ n → ∀ θ, Mseq n / Real.sqrt n ≤ ‖θ - θ₀‖ → ‖θ - θ₀‖ ≤ ε →
        ∫ ω, (1 - φ n ω) ∂(productMeasure M μ θ n)
          ≤ Real.exp (-c * n * ‖θ - θ₀‖ ^ 2) := by
  sorry

end StatLean.Bayesian
