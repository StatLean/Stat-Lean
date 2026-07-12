import StatLean.Bayesian.DirichletLaplace.DensityBounds
import StatLean.Bayesian.ForMathlib.PiLintegralFintype
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Dirichlet–Laplace joint prior density and its two-sided bounds (Lemma 3.2)

This file lifts the univariate marginal density bounds of `DirichletLaplace.DensityBounds`
(P3/P4/P5) to the **joint** `ι`-fold product density of the Dirichlet–Laplace prior, and packages
them as measure-vs-Lebesgue comparisons. These are the density inputs to Lemma 6.1 (`C14`).

Contents:
* `dlPrior_eq_withDensity` — the DL prior is Lebesgue with the product density
  `θ ↦ ∏ⱼ dlDensity a (θⱼ)` (BPPD eq. (10) joint form; via `pi_withDensity'` + the volume-preserving
  `WithLp.toLp`).
* `prod_dlDensity_le` — **Lemma 3.2 (13)**: on the coordinates of a support set `S` the product
  density is `≤ (17·a·δ^{a−1})^{|S|}`.
* `sum_sqrt_abs_le` — the two-step Cauchy–Schwarz bound `∑ⱼ √|θⱼ| ≤ (card ι)^{3/4}‖θ‖^{1/2}` that
  converts the coordinate-wise `√|·|` exponent of the lower bound into a norm.
* `prod_dlDensity_ge` — **Lemma 3.2 (14)**: the uniform log-form lower bound
  `∏ⱼ dlDensity a (θⱼ) ≥ (a/64)^{card ι}·exp(−3·card ι − (7/2)∑ⱼ√|θⱼ|)`.
* `dlPrior_le_of_subset`, `dlPrior_ball_ge_volume` — set-vs-volume comparisons in both directions,
  obtained from the `withDensity` representation.

**Reference.** A. Bhattacharya, D. Pati, N. S. Pillai, D. B. Dunson, *Dirichlet–Laplace priors for
optimal shrinkage*, J. Amer. Statist. Assoc. 110 (2015), 1479–1490 (arXiv:1401.5398). Prior (10),
Lemma 3.2, eqs. (13)–(14).

**Proof formalization notes.** `dlPrior_eq_withDensity` unfolds `dlPrior` (a `Measure.pi`-of-marginals
pushed through `WithLp.toLp 2`), rewrites each marginal by `dlMarginal_eq_withDensity` (C2), applies
`pi_withDensity'` (F4, the `Fintype ι` upgrade of `pi_withDensity`), and transports across the
volume-preserving `WithLp.toLp 2` (`PiLp.volume_preserving_toLp`). The product bounds are `Finset`
products of the univariate C3 bounds; `prod_dlDensity_ge` combines the per-coordinate uniform
log-form P4 with `Real.exp_sum`. The Lebesgue comparisons are `withDensity_apply` +
`setLIntegral_mono`/`setLIntegral_le`.
*Deviations (see the milestone plan).* D5: the mixture-restriction lower bound has exponent
`−(7/2)√|x|` (not the paper's sketched `−2√|x|`), which is why `prod_dlDensity_ge` carries the
`7/2` factor. D8: the density **upper** bound (and hence `prod_dlDensity_le`) genuinely needs
`a ≤ 1/2` (the `Γ(1−a)` blow-up), whereas the lower bound needs only `a ≤ 1`.

**Bibliographic comments.** The product structure of the DL prior density is what reduces the
`n`-dimensional prior-mass estimates to `n` independent univariate calculations; the `√|·|`
tails are the signature of the Laplace-scale mixture and are the mechanism behind the prior's
near-minimax concentration (Bhattacharya–Pati–Pillai–Dunson 2015; cf. the Gaussian-scale-mixture
program of Polson–Scott, "Shrink globally, act locally," *Bayesian Statistics 9*, 2011).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace Classical

namespace StatLean.Bayesian

variable {ι : Type*} [Fintype ι]

/-- **Product-density representation of the DL prior** (BPPD eq. (10), joint form): for `0 < a`,
`dlPrior a ι` is Lebesgue measure on `EuclideanSpace ℝ ι` weighted by the product density
`θ ↦ ∏ⱼ dlDensity a (θⱼ)`. -/
theorem dlPrior_eq_withDensity {a : ℝ}
    -- USER-INPUT: prior scale positive so the marginal is the Laplace–Gamma mixture; BPPD (10)
    (ha : 0 < a) :
    dlPrior a ι
      = (volume : Measure (EuclideanSpace ℝ ι)).withDensity (fun θ => ∏ j, dlDensity a (θ j)) := by
  sorry

/-- **Lemma 3.2 (13)** (BPPD): on a support set `S` all of whose coordinates exceed the resolution
`δ`, the product of the coordinate DL densities is at most `(17·a·δ^{a−1})^{|S|}`. Needs `a ≤ 1/2`
(deviation D8) and `δ ∈ (0,1]`. -/
theorem prod_dlDensity_le {a δ : ℝ}
    -- USER-INPUT: prior scale in the admissible range for the density upper bound; BPPD Lem 3.2, D8
    (ha : 0 < a) (ha' : a ≤ 1 / 2)
    -- USER-INPUT: resolution in the Lemma 3.3 window (0,1]; BPPD Lem 3.2/3.3
    (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {S : Finset ι} {θ : EuclideanSpace ℝ ι}
    -- USER-INPUT: `S` indexes coordinates above the resolution; BPPD Lem 3.2
    (hθ : ∀ j ∈ S, δ < |θ j|) :
    ∏ j ∈ S, dlDensity a (θ j) ≤ ENNReal.ofReal ((17 * a * δ ^ (a - 1)) ^ S.card) := by
  sorry

/-- Two-step Cauchy–Schwarz bound converting the coordinate-wise `√|·|` sum of the lower bound into
a norm: `∑ⱼ √|θⱼ| ≤ (card ι)^{3/4}·‖θ‖^{1/2}`. -/
theorem sum_sqrt_abs_le (θ : EuclideanSpace ℝ ι) :
    ∑ j, Real.sqrt |θ j| ≤ (Fintype.card ι : ℝ) ^ (3 / 4 : ℝ) * ‖θ‖ ^ (1 / 2 : ℝ) := by
  sorry

/-- **Lemma 3.2 (14)** (BPPD), uniform log-form (deviation D5): the joint DL density is bounded
below by `(a/64)^{card ι}·exp(−3·card ι − (7/2)∑ⱼ√|θⱼ|)`. Needs only `a ≤ 1`. -/
theorem prod_dlDensity_ge {a : ℝ}
    -- USER-INPUT: prior scale in the admissible range for the density lower bound; BPPD Lem 3.2
    (ha : 0 < a) (ha' : a ≤ 1) (θ : EuclideanSpace ℝ ι) :
    ENNReal.ofReal ((a / 64) ^ Fintype.card ι *
        Real.exp (-3 * (Fintype.card ι : ℝ) - (7 / 2) * (∑ j, Real.sqrt |θ j|)))
      ≤ ∏ j, dlDensity a (θ j) := by
  sorry

/-- Upper set-vs-volume comparison: on a measurable region `C` where the joint density is uniformly
`≤ c`, the DL prior charges `C` with at most `c ·` its Lebesgue volume. -/
theorem dlPrior_le_of_subset {a : ℝ}
    -- USER-INPUT: prior scale positive; BPPD (10)
    (ha : 0 < a) {C : Set (EuclideanSpace ℝ ι)}
    -- LEAN-ONLY: target region measurable (regularity)
    (hC : MeasurableSet C) {c : ℝ≥0∞}
    -- USER-INPUT: uniform density upper bound on `C`; instantiated from Lemma 3.2 (13)
    (hc : ∀ θ ∈ C, ∏ j, dlDensity a (θ j) ≤ c) :
    dlPrior a ι C ≤ c * volume C := by
  sorry

/-- Lower set-vs-volume comparison on a ball: where the joint density is uniformly `≥ c` over a
closed ball, the DL prior charges the ball with at least `c ·` its Lebesgue volume. -/
theorem dlPrior_ball_ge_volume {a : ℝ}
    -- USER-INPUT: prior scale positive; BPPD (10)
    (ha : 0 < a) (θ₀ : EuclideanSpace ℝ ι) (r : ℝ) {c : ℝ≥0∞}
    -- USER-INPUT: uniform density lower bound on the ball; instantiated from Lemma 3.2 (14)
    (hc : ∀ θ ∈ Metric.closedBall θ₀ r, c ≤ ∏ j, dlDensity a (θ j)) :
    c * volume (Metric.closedBall θ₀ r) ≤ dlPrior a ι (Metric.closedBall θ₀ r) := by
  sorry

end StatLean.Bayesian
