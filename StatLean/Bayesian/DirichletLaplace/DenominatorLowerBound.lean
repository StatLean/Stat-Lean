import StatLean.Bayesian.DirichletLaplace.Defs
import StatLean.Bayesian.ForMathlib.GaussianShift
import Mathlib.MeasureTheory.Integral.Average

/-!
# Denominator lower bound for the Dirichlet–Laplace posterior (C7)

The posterior ratio `dlNumer / dlDenom` is only useful once the denominator `dlDenom θ* π y`
(the marginal likelihood `m(y) = ∫ dN(θ,I)/dN(θ*,I)(y) dΠ(θ)`) is bounded *below* on a set of `y`
of high probability under the truth `θ*`. This is the Castillo–van der Vaart evidence lower bound
(a "prior-mass / Kullback–Leibler neighbourhood" argument).

The two-step estimate:

* **Jensen** (`dlDenom_ge_jensen`). Restricting the integral to the ball `B = B(θ*, r)` and applying
  Jensen's inequality to the convex exponential gives
  `dlDenom θ* π y ≥ Π(B)·exp(⟪aveShift, y − θ*⟫ − r²/2)`,
  where `aveShift = ⨍_{B} (θ − θ*) dΠ` is the average displacement of the prior over the ball
  (`‖aveShift‖ ≤ r`).
* **Gaussian tail** (`measure_dlDenom_lt_le`, the Castillo–van der Vaart Lemma 5.2 analogue). Under
  `y ∼ N(θ*, I)`, the event `{dlDenom < e^{−r²}·Π(B)}` is contained (via the Jensen bound) in
  `{⟪aveShift, y − θ*⟫ < −r²/2}`, whose probability is `≤ exp(−(r²/2)²/(2‖aveShift‖²)) ≤ exp(−r²/8)`
  because `‖aveShift‖ ≤ r`.

**Reference.** A. Bhattacharya, D. Pati, N. S. Pillai, D. B. Dunson, *Dirichlet–Laplace priors for
optimal shrinkage*, Journal of the American Statistical Association 110 (2015), 1479–1490
(arXiv:1401.5398). §6 (denominator / evidence lower bound). The evidence-lower-bound event is the
analogue of I. Castillo and A. W. van der Vaart, "Needles and straw in a haystack: posterior
concentration for possibly sparse sequences," *Ann. Statist.* 40 (2012), 2069–2101, Lemma 5.2.

**Proof formalization notes.** `aveShift` is a genuine `EuclideanSpace ℝ ι`-valued Bochner set
average `⨍`; its norm bound is `norm_setAverage_le`-style (each `θ − θ*` has norm `≤ r` on the ball).
The Jensen step uses `ConvexOn.map_average_le` with `Real.convexOn_exp` on the normalized restricted
prior `(Π B)⁻¹ • Π.restrict B` (the integrand `⟪θ − θ*, y − θ*⟫ − ‖θ − θ*‖²/2` is bounded on the
ball, so it is integrable). The tail step reduces to the 1-dimensional Gaussian
`stdGaussianShift_inner_ge_le` (from `ForMathlib.GaussianShift`) applied to the direction
`c = aveShift` with variance `‖aveShift‖² ≤ r²`. Edge cases: `Π(B) = 0` collapses the target event
to `∅`; `aveShift = 0` makes the standardized deviation `+∞` and the tail `0`. `[IsProbabilityMeasure
π]` is carried because the intended `π` is the DL prior and finiteness of `Π(B)` is needed for the
Jensen normalization.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace Classical

namespace StatLean.Bayesian

variable {ι : Type*} [Fintype ι]

/-- **Average displacement of the prior over a ball** (BPPD §6, evidence lower bound helper).

`aveShift π θ* r = ⨍_{B(θ*, r)} (θ − θ*) dΠ` is the Bochner set average of the displacement
`θ ↦ θ − θ*` over the closed ball of radius `r`. It is the location around which the log-likelihood
ratio is linearized in the Jensen step.

Edge behaviour: when `Π(B(θ*, r)) = 0` or `= ∞` the set average `⨍` returns `0` (Mathlib's
convention `(μ s).toReal⁻¹ • ∫ = 0`), consistent with the trivial lower bound in that case. -/
noncomputable def aveShift (π : Measure (EuclideanSpace ℝ ι)) (θstar : EuclideanSpace ℝ ι)
    (r : ℝ) : EuclideanSpace ℝ ι :=
  ⨍ θ in Metric.closedBall θstar r, (θ - θstar) ∂π

/-- The average displacement stays inside the ball: `‖aveShift π θ* r‖ ≤ r`. Every point `θ` of the
ball has `‖θ − θ*‖ ≤ r`, and the set average of a norm-bounded function is norm-bounded by the same
constant (degenerate `Π(B) ∈ {0, ∞}` gives `aveShift = 0 ≤ r`). -/
lemma norm_aveShift_le (π : Measure (EuclideanSpace ℝ ι)) (θstar : EuclideanSpace ℝ ι) {r : ℝ}
    -- LEAN-ONLY: radius nonneg, else `closedBall = ∅`, `aveShift = 0` and `0 ≤ r` fails
    (hr : 0 ≤ r) :
    ‖aveShift π θstar r‖ ≤ r := by
  sorry

/-- **Jensen evidence lower bound** (BPPD §6).

Restricting `dlDenom` to the ball `B(θ*, r)` and applying Jensen to the exponential yields

  `Π(B(θ*, r))·exp(⟪aveShift π θ* r, y − θ*⟫ − r²/2) ≤ dlDenom θ* π y`.

The linear term `⟪aveShift, y − θ*⟫` is the average of `⟪θ − θ*, y − θ*⟫` over the ball; the
quadratic penalty `r²/2` bounds the average of `‖θ − θ*‖²/2 ≤ r²/2`. -/
lemma dlDenom_ge_jensen (π : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure π]
    (θstar y : EuclideanSpace ℝ ι) {r : ℝ}
    -- USER-INPUT: 0 < r (ball radius positive; CvdV Lem 5.2 setup); BPPD §6
    (hr : 0 < r) :
    π (Metric.closedBall θstar r)
        * ENNReal.ofReal (Real.exp (⟪aveShift π θstar r, y - θstar⟫ - r ^ 2 / 2))
      ≤ dlDenom θstar π y := by
  sorry

/-- **Castillo–van der Vaart Lemma 5.2 analogue: the denominator is not too small** (BPPD §6).

Under the true model `y ∼ N(θ*, I)` (the measure `gaussShiftKernel ι θ*`), the probability that the
marginal likelihood `dlDenom θ* π y` falls below `e^{−r²}·Π(B(θ*, r))` is at most `e^{−r²/8}`.

Combining the Jensen bound `dlDenom ≥ Π(B)·exp(⟪aveShift, y − θ*⟫ − r²/2)` with the target event
gives the inclusion `{dlDenom < e^{−r²}Π(B)} ⊆ {⟪aveShift, y − θ*⟫ < −r²/2}` (when `Π(B) > 0`; the
event is empty otherwise), and the 1-dimensional Gaussian tail with variance `‖aveShift‖² ≤ r²`
gives `exp(−(r²/2)²/(2r²)) = exp(−r²/8)`. -/
lemma measure_dlDenom_lt_le (π : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure π]
    (θstar : EuclideanSpace ℝ ι) {r : ℝ}
    -- USER-INPUT: 0 < r (ball radius positive; CvdV Lem 5.2 setup); BPPD §6
    (hr : 0 < r) :
    (gaussShiftKernel ι θstar)
        {y | dlDenom θstar π y
          < ENNReal.ofReal (Real.exp (-(r ^ 2))) * π (Metric.closedBall θstar r)}
      ≤ ENNReal.ofReal (Real.exp (-(r ^ 2 / 8))) := by
  sorry

end StatLean.Bayesian
