import StatLean.Bayesian.BernsteinVonMises.Defs

/-!
# Prior small-ball bounds and the exponential tail split

Quantitative consequences of the prior condition of vdV Theorem 10.1 (`HasLocalDensity`):

* `prior_ball_inv_sqrt_lower` — the small-ball lower bound
  `π(B(θ₀, u/√n)) ≳ n^{-k/2}` (continuity and positivity of the density at `θ₀`);
* `prior_smallBall_upper` / `prior_smallBall_lower` — two-sided volume comparison of `π`
  with Lebesgue measure on a small ball around `θ₀`;
* `prior_tail_split` — the Step-A tail estimate (vdV p. 142, last display):
  `√nᵏ · ∫_{‖θ−θ₀‖ ≥ Mₙ/√n} exp(−c n (‖θ−θ₀‖² ∧ 1)) dπ(θ) → 0` for every `Mₙ → ∞`,
  by splitting at a fixed radius `D` where the density is bounded (moderate zone: Gaussian
  integral; far zone: `√nᵏ e^{−cn} → 0`).

**Reference.** A. W. van der Vaart, *Asymptotic Statistics*, Cambridge Series in Statistical
and Probabilistic Mathematics, Cambridge University Press, 1998, Chapter 10, §10.2, proof of
Theorem 10.1, p. 142 (the displays following "Combining the preceding displays").

**Proof formalization notes.** All statements are about the prior alone — no sampling model
appears. The `n^{-k/2}` normalizations are kept explicit (no rescaled-prior object is
introduced); `volume` is Lebesgue measure on `EuclideanSpace ℝ (Fin k)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace StatLean.Bayesian

variable {k : ℕ}
variable {π : Measure (EuclideanSpace ℝ (Fin k))} [IsProbabilityMeasure π]
variable {θ₀ : EuclideanSpace ℝ (Fin k)} {r₀ : ℝ} {f : EuclideanSpace ℝ (Fin k) → ℝ}

/-- **Prior small-ball lower bound** (vdV p. 142: `Π_n(U) ≳ (1/√n)ᵏ`): under the prior
condition, for every fixed `u > 0` there is `c > 0` with
`c · (√n)⁻ᵏ ≤ π(B(θ₀, u/√n))` for all large `n`. -/
theorem prior_ball_inv_sqrt_lower
    -- USER-INPUT: the prior condition of Theorem 10.1; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f) {u : ℝ}
    -- LEAN-ONLY: nontrivial ball radius
    (hu : 0 < u) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * ENNReal.ofReal ((Real.sqrt n)⁻¹ ^ k) ≤ π (Metric.ball θ₀ (u / Real.sqrt n)) := by
  sorry

/-- **Local volume upper comparison**: near `θ₀` the prior is dominated by a multiple of
Lebesgue measure (density bounded by continuity at `θ₀`). Returns a radius `D ≤ r₀` on which
the comparison holds. -/
theorem prior_smallBall_upper
    -- USER-INPUT: the prior condition of Theorem 10.1; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f) :
    ∃ D : ℝ, 0 < D ∧ D ≤ r₀ ∧ ∃ Cb : ℝ≥0∞, Cb ≠ ∞ ∧
      ∀ s : Set (EuclideanSpace ℝ (Fin k)), s ⊆ Metric.ball θ₀ D → MeasurableSet s →
        π s ≤ Cb * volume s := by
  sorry

/-- **Local volume lower comparison**: near `θ₀` the prior dominates a positive multiple of
Lebesgue measure (density positive by continuity at `θ₀`). -/
theorem prior_smallBall_lower
    -- USER-INPUT: the prior condition of Theorem 10.1; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f) :
    ∃ D : ℝ, 0 < D ∧ D ≤ r₀ ∧ ∃ cb : ℝ≥0∞, 0 < cb ∧
      ∀ s : Set (EuclideanSpace ℝ (Fin k)), s ⊆ Metric.ball θ₀ D → MeasurableSet s →
        cb * volume s ≤ π s := by
  sorry

/-- **The Step-A tail split** (vdV p. 142, final display of the concentration step): for every
exponent `c > 0` and every `Mₙ → ∞`,
`(√n)ᵏ · ∫_{‖θ−θ₀‖ ≥ Mₙ/√n} exp(−c n (‖θ−θ₀‖² ∧ 1)) dπ(θ) → 0`.
Split at a radius `D` from `prior_smallBall_upper`: on the moderate zone substitute the
density bound and compare with the Gaussian integral `∫_{‖h‖ ≥ Mₙ} e^{−c‖h‖²} dh → 0`; on
the far zone bound by `(√n)ᵏ e^{−c n D²} · π(univ) → 0`. -/
theorem prior_tail_split
    -- USER-INPUT: the prior condition of Theorem 10.1; vdV §10.2, p. 141
    (hπ : HasLocalDensity π θ₀ r₀ f) {c : ℝ}
    -- LEAN-ONLY: positive exponential rate (supplied by Lemma 10.3)
    (hc : 0 < c) {Mseq : ℕ → ℝ}
    -- USER-INPUT: the localization radii diverge; vdV §10.2, p. 141 (`Mₙ → ∞`)
    (hM : Tendsto Mseq atTop atTop) :
    Tendsto (fun n : ℕ =>
        ENNReal.ofReal (Real.sqrt n ^ k) *
          ∫⁻ θ in {θ | Mseq n / Real.sqrt n ≤ ‖θ - θ₀‖},
            ENNReal.ofReal (Real.exp (-c * n * min (‖θ - θ₀‖ ^ 2) 1)) ∂π)
      atTop (𝓝 0) := by
  sorry

end StatLean.Bayesian
