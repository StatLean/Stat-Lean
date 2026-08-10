import StatLean.RobustStatistics.MEstimation.MLocationFunctional

/-!
# Asymptotic breakdown of monotone location M-functionals

The asymptotic contamination breakdown point of a monotone location M-estimator with
bounded score is (`MMY §3.2.1`, eq. (3.21); proof §3.8.3)

$$\varepsilon^* = \frac{\min(k_1, k_2)}{k_1 + k_2}, \qquad
  k_1 = -\psi(-\infty),\ k_2 = \psi(\infty),$$

attaining `1/2` for odd ψ. Following the statement-first design, the content is split
into the two directions that *are* eq. (3.21), without introducing an `ε*` supremum:

* `mLocationRoot_bounded_of_contamination` — **stability**: for
  `ε < min(k₁,k₂)/(k₁+k₂)`, all roots of every `ε`-contaminated M-equation lie in one
  fixed bounded interval (uniformly over the contaminating `Q`).
* `mLocationRoot_contamination_unbounded` — **sharpness**: for
  `ε > k₁/(k₁+k₂)`, point-mass contaminations `δ_{x₀}` with `x₀ → ∞` produce contaminated
  roots beyond any bound.
* `mLocationRoot_bounded_of_odd`, `huberLocationRoot_bounded` — the odd/Huber case:
  breakdown `1/2` (`MMY §3.2.1`: "if ψ is odd … the bound ε* = 0.5 is attained").

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) §3.2.1 (eq.
(3.21)–(3.22)), §3.8.3.1 (eq. (3.61)–(3.63)).
-/

open MeasureTheory Filter Topology

namespace StatLean.RobustStatistics

/-- **Stability below the breakdown level** (`MMY` eq. (3.21), "≥" direction; §3.8.3.1):
for a monotone score with limits `-k₁ < 0 < k₂` and contamination level
`ε < min(k₁,k₂)/(k₁+k₂)`, the roots of all `ε`-contaminated M-equations are uniformly
bounded — no contaminating distribution can drive the M-functional to infinity. -/
theorem mLocationRoot_bounded_of_contamination {P : Measure ℝ} [IsProbabilityMeasure P]
    {ψ : ℝ → ℝ} {k₁ k₂ ε : ℝ}
    -- USER-INPUT: monotone score with finite limits; MMY §3.2.1 (k₁ = -ψ(-∞), k₂ = ψ(∞))
    (hψm : Monotone ψ) (hbot : Tendsto ψ atBot (𝓝 (-k₁))) (htop : Tendsto ψ atTop (𝓝 k₂))
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    -- USER-INPUT: contamination level below the breakdown point; MMY eq. (3.21)
    (hε0 : 0 ≤ ε) (hε : ε < min k₁ k₂ / (k₁ + k₂)) :
    ∃ B : ℝ, ∀ (Q : Measure ℝ), IsProbabilityMeasure Q → ∀ θ : ℝ,
      IsMLocationRoot ψ (contaminate P Q ε) θ → |θ| ≤ B := by
  sorry

/-- **Sharpness above the breakdown level** (`MMY` eq. (3.21), "≤" direction; §3.8.3.1,
eq. (3.62)–(3.63)): for `ε > k₁/(k₁+k₂)`, placing the contaminating point mass far enough
to the right produces contaminated roots beyond any bound — the M-functional explodes
to `+∞`. -/
theorem mLocationRoot_contamination_unbounded {P : Measure ℝ} [IsProbabilityMeasure P]
    {ψ : ℝ → ℝ} {k₁ k₂ ε : ℝ}
    -- USER-INPUT: continuous monotone score with finite limits; MMY §3.2.1 + Thm 10.1
    (hψc : Continuous ψ) (hψm : Monotone ψ)
    (hbot : Tendsto ψ atBot (𝓝 (-k₁))) (htop : Tendsto ψ atTop (𝓝 k₂))
    (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    -- USER-INPUT: contamination level above the breakdown point; MMY eq. (3.22) (ε₁*)
    (hε : k₁ / (k₁ + k₂) < ε) (hε1 : ε < 1) :
    ∀ B : ℝ, ∃ (x₀ θ : ℝ), B < θ ∧
      IsMLocationRoot ψ (contaminate P (Measure.dirac x₀) ε) θ := by
  sorry

/-- **Odd scores break down at `1/2`** (`MMY §3.2.1`: `k₁ = k₂` gives `ε* = 0.5`): for
`ε < 1/2` the contaminated roots stay uniformly bounded. -/
theorem mLocationRoot_bounded_of_odd {P : Measure ℝ} [IsProbabilityMeasure P]
    {ψ : ℝ → ℝ} {k ε : ℝ}
    -- USER-INPUT: monotone score with symmetric limits ∓k; MMY §3.2.1 (odd ψ)
    (hψm : Monotone ψ) (hbot : Tendsto ψ atBot (𝓝 (-k))) (htop : Tendsto ψ atTop (𝓝 k))
    (hk : 0 < k)
    -- USER-INPUT: contamination level below one half; MMY §3.2.1
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) :
    ∃ B : ℝ, ∀ (Q : Measure ℝ), IsProbabilityMeasure Q → ∀ θ : ℝ,
      IsMLocationRoot ψ (contaminate P Q ε) θ → |θ| ≤ B := by
  sorry

/-- **The Huber location functional has asymptotic breakdown point `1/2`**
(`MMY §3.2.1`): the Huber score is monotone with limits `∓c`, so contaminated roots stay
bounded for every `ε < 1/2`. -/
theorem huberLocationRoot_bounded {P : Measure ℝ} [IsProbabilityMeasure P] {c ε : ℝ}
    (hc : 0 < c) (hε0 : 0 ≤ ε) (hε : ε < 1 / 2) :
    ∃ B : ℝ, ∀ (Q : Measure ℝ), IsProbabilityMeasure Q → ∀ θ : ℝ,
      IsMLocationRoot (huberPsi c) (contaminate P Q ε) θ → |θ| ≤ B := by
  sorry

end StatLean.RobustStatistics
