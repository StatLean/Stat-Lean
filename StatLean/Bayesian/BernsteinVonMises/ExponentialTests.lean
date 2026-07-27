import StatLean.Bayesian.BernsteinVonMises.ScoreTest
import StatLean.Bayesian.BernsteinVonMises.TestBoost

/-!
# Lemma 10.3: exponentially powerful tests

Assembly of vdV Lemma 10.3: under the conditions of Theorem 10.1 (DQM at `θ₀`, nonsingular
Fisher information, tests condition (10.2)), for every `Mₙ → ∞` there are tests `φₙ` and a
constant `c > 0` with
`P^n_{θ₀} φₙ → 0` and `P^n_θ(1 − φₙ) ≤ exp(−c n (‖θ−θ₀‖² ∧ 1))` for every
`‖θ − θ₀‖ ≥ Mₙ/√n` and every sufficiently large `n`.

The test is the pointwise maximum of the moderate-range truncated-score test
(`ScoreTest.exists_moderate_tests`, covering `Mₙ/√n ≤ ‖θ−θ₀‖ ≤ ε`) and the boosted
far-range test (`TestBoost.exists_boosted_tests`, covering `‖θ−θ₀‖ ≥ ε`).

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10, §10.2,
Lemma 10.3, p. 143 (statement) and pp. 143–144 (proof).

**Proof formalization notes.** The two ranges are glued with a single rate constant
`c := min(c_moderate, c_far)`; on the far range `‖θ−θ₀‖ ≥ ε` one has
`min(‖θ−θ₀‖², 1) ≤ 1`, so `exp(−c_far n)` dominates `exp(−c n (‖θ−θ₀‖² ∧ 1))` after
shrinking `c` by the factor `min(ε², 1)`. The size at `θ₀` of the maximum test is bounded by
the sum of the two sizes.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal RealInnerProductSpace
open AsymptoticStatistics (ParametricFamily IsPDFOf DifferentiableQuadraticMean
  fisherInformation)

namespace StatLean.Bayesian

variable {k : ℕ} {𝓧 : Type*} [m𝓧 : MeasurableSpace 𝓧]
variable {M : ParametricFamily 𝓧 (EuclideanSpace ℝ (Fin k))} {μ : Measure 𝓧} [SigmaFinite μ]
variable {θ₀ : EuclideanSpace ℝ (Fin k)} {sc : 𝓧 → EuclideanSpace ℝ (Fin k)}
variable {J : Matrix (Fin k) (Fin k) ℝ}

/-- **vdV Lemma 10.3** (exponentially powerful tests). Under the conditions of Theorem 10.1,
for every `Mₙ → ∞` there exist tests `φₙ` and `c > 0` with vanishing size at `θ₀` and
type-II error `≤ exp(−c n (‖θ−θ₀‖² ∧ 1))` uniformly over `‖θ − θ₀‖ ≥ Mₙ/√n`, for `n`
large. -/
theorem exponential_tests
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
    -- USER-INPUT: the tests condition (10.2); vdV Thm 10.1
    (hTests : UniformlyConsistentTests M μ θ₀)
    {Mseq : ℕ → ℝ}
    -- USER-INPUT: the localization radii diverge; vdV Lemma 10.3 (`Mₙ → ∞`)
    (hM : Tendsto Mseq atTop atTop) :
    ∃ (φ : ∀ n : ℕ, (Fin n → 𝓧) → ℝ) (c : ℝ), 0 < c ∧
      IsExpConsistentTestSeq M μ θ₀ Mseq c φ := by
  sorry

end StatLean.Bayesian
