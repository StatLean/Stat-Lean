import StatLean.Bayesian.DirichletLaplace.DensityBounds
import StatLean.Bayesian.ForMathlib.PiLintegralFintype
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Dirichlet–Laplace prior: support-count MGF, Chernoff tail, and small-ball lower bound

The two prior-side probabilistic engines of the compressibility argument, both consequences of the
**product** structure of `dlPrior` (independent, identically distributed coordinates):

* `dlPrior_count_mgf` — the moment generating function of the δ-support size `dlSuppCount δ` under
  the prior factorizes: `∫ c^{|supp_δ(θ)|} dΠ = ((1−ζ) + ζ·c)^{card ι}`, where
  `ζ = ζ(δ) = Π(|θ₁| > δ)` is the per-coordinate exceedance probability.
* `dlPrior_count_ge_le` — the **Chernoff bound** it yields:
  `Π(|supp_δ(θ)| ≥ k) ≤ exp(card ι·z·(c−1) − k·log c)` for any tilt `c > 1` and any upper bound `z`
  on `ζ` (supplied downstream by Lemma 3.3, C3).
* `dlPrior_box_ge`, `dlPrior_ball_zero_ge` — the **small-ball lower bound**: a coordinatewise box
  is contained in the Euclidean ball, so `Π(B(0,r)) ≥ (1 − ζ(s))^{card ι} ≥ exp(−2·card ι·w)` with
  the per-coordinate threshold `s = min(r/√(card ι), 1/2)` (deviation D7) and `w` an upper bound on
  the tail `ζ(s)`.

**Reference.** A. Bhattacharya, D. Pati, N. S. Pillai, D. B. Dunson, *Dirichlet–Laplace priors for
optimal shrinkage*, J. Amer. Statist. Assoc. 110 (2015), 1479–1490 (arXiv:1401.5398). §6 (the
denominator/support-count analysis); the tensorization identity of eq. (26) is the special case
`c = 1` boundary of the MGF here.

**Proof formalization notes.** `dlPrior_count_mgf` pushes `c^{dlSuppCount}` through the
`WithLp.toLp 2` pushforward (support count is invariant) and factorizes with `lintegral_pi_prod'`
(F4), each factor being `E[c^{1[|θⱼ|>δ]}] = (1−ζ) + ζ·c`. `dlPrior_count_ge_le` is Markov applied to
the tilted variable `c^{dlSuppCount}` followed by `1 + t ≤ eᵗ` and `ζ ≤ z`. `dlPrior_box_ge` is the
box-probability factorization; `dlPrior_ball_zero_ge` uses the inclusion
`{θ | ∀ j, |θⱼ| ≤ s} ⊆ B(0,r)` for `s ≤ r/√(card ι)` and `(1−x)^m ≥ e^{−2xm}` for `x ≤ 1/2`.
*Deviation D7:* the per-coordinate threshold is clamped to `1/2` because `r/√(card ι)` may exceed
`1` when `qₙ log n > n`.

**Bibliographic comments.** Bounding the number of "large" coordinates by a binomial Chernoff tail
is the Bayesian analogue of the frequentist support-recovery counting arguments (Donoho–Johnstone,
*Biometrika* 81 (1994), 425–455); the small-ball / prior-mass condition on Kullback–Leibler
neighborhoods is the Ghosal–Ghosh–van der Vaart (*Ann. Statist.* 28 (2000), 500–531) prior-mass
requirement, here verified for the Dirichlet–Laplace prior.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace Classical

namespace StatLean.Bayesian

variable {ι : Type*} [Fintype ι]

/-- **Support-count MGF under the product prior.** For any tilt `c`, the moment generating function
of the δ-support size factorizes over coordinates:
`∫ c^{|supp_δ(θ)|} dΠ = ((1−ζ) + ζ·c)^{card ι}`, `ζ = Π(|θ₁| > δ)`. -/
theorem dlPrior_count_mgf {a δ : ℝ} (c : ℝ≥0∞) :
    ∫⁻ θ, c ^ dlSuppCount δ θ ∂(dlPrior a ι)
      = ((1 - dlMarginal a {x : ℝ | δ < |x|}) + dlMarginal a {x : ℝ | δ < |x|} * c)
          ^ Fintype.card ι := by
  sorry

/-- **Chernoff tail for the δ-support size** (BPPD §6): tilting by `c > 1` and using `1 + t ≤ eᵗ`,
`Π(|supp_δ(θ)| ≥ k) ≤ exp(card ι · z · (c−1) − k · log c)` for any upper bound `z` on the
per-coordinate exceedance probability `ζ(δ)`. -/
theorem dlPrior_count_ge_le {a δ z c : ℝ}
    -- USER-INPUT: admissible tilt `c > 1`; Markov/Chernoff, BPPD §6
    (hc : 1 < c) (k : ℕ)
    -- USER-INPUT: `z` bounds the per-coordinate exceedance prob ζ(δ) (supplied by Lemma 3.3, C3)
    (hz : (dlMarginal a {x : ℝ | δ < |x|}).toReal ≤ z) :
    dlPrior a ι {θ | k ≤ dlSuppCount δ θ}
      ≤ ENNReal.ofReal (Real.exp ((Fintype.card ι : ℝ) * z * (c - 1) - (k : ℝ) * Real.log c)) := by
  sorry

/-- Box-probability factorization: the prior mass of the coordinatewise box `{θ | ∀ j, |θⱼ| ≤ s}`
is at least the product `Π(|θ₁| ≤ s)^{card ι}` of one-dimensional masses. -/
theorem dlPrior_box_ge {a s : ℝ} :
    (dlMarginal a {x : ℝ | |x| ≤ s}) ^ Fintype.card ι
      ≤ dlPrior a ι {θ | ∀ j, |θ j| ≤ s} := by
  sorry

/-- **Small-ball lower bound at the origin** (BPPD §6, deviation D7): with per-coordinate threshold
`s = min(r/√(card ι), 1/2)` and any upper bound `w` on the tail `ζ(s) = Π(|θ₁| > s)`, the prior
charges the ball `B(0,r)` with at least `exp(−2·card ι·w)`. -/
theorem dlPrior_ball_zero_ge {a r w : ℝ}
    -- USER-INPUT: positive radius; BPPD §6
    (hr : 0 < r)
    -- USER-INPUT: `w` bounds the tail at the clamped threshold s = min(r/√m, 1/2); D7
    (hw : (dlMarginal a
        {x : ℝ | min (r / Real.sqrt (Fintype.card ι : ℝ)) (1 / 2) < |x|}).toReal ≤ w) :
    ENNReal.ofReal (Real.exp (-2 * (Fintype.card ι : ℝ) * w))
      ≤ dlPrior a ι (Metric.closedBall 0 r) := by
  sorry

end StatLean.Bayesian
