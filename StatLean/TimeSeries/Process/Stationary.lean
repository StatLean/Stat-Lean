import StatLean.TimeSeries.Process.Defs
import Mathlib.Probability.IdentDistrib

/-!
# Strict stationarity — basic theory (FY §2.1.1)

Consequences of `IsStrictlyStationary`: identical one-dimensional marginals, closure
under time shift, the equivalence with the book's consecutive-window formulation
(FY Definition 2.2 as printed), and the implication *strict + L² ⇒ weak* (the unnumbered
relation of FY §2.1.1, p. 30).

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.1.1,
Definitions 2.1–2.2 and the following remark (pp. 29–30). (`FY §2.1.1`.)

**Proof formalization notes.** `strict + L² ⇒ weak` transports the mean and the lag-`k`
covariance along the equality of the pair laws `(X_{t+k}, X_t) ≐ (X_k, X_0)` (an `n = 2`
instance of the definition); the covariance is a functional of the pair law once both
coordinates are square-integrable, which is where the `L²` hypothesis (stated at time
`0`, propagated by identical distribution) enters. The converse fails (FY p. 30) — no
claim is stated. In `isStrictlyStationary_iff_window`, the general-tuple form follows
from consecutive windows by projecting a sufficiently long window along a measurable
coordinate-selection map.

**Bibliographic comments.** The strict/weak dichotomy and the observation that second
moments see only the weak structure are classical (Khinchin 1934; Wold 1938;
Doob, *Stochastic Processes*, 1953, ch. X).
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : ℤ → Ω → ℝ}

/-- Strictly stationary processes have identically distributed marginals. -/
theorem IsStrictlyStationary.identDistrib (h : IsStrictlyStationary X μ)
    -- LEAN-ONLY: coordinate random variables are measurable; implicit in FY
    (hmeas : ∀ t, Measurable (X t)) (s t : ℤ) :
    IdentDistrib (X s) (X t) μ μ := by
  sorry

/-- Strict stationarity is preserved by time shifts. -/
theorem IsStrictlyStationary.shift (h : IsStrictlyStationary X μ) (k : ℤ) :
    IsStrictlyStationary (shift X k) μ := by
  sorry

/-- **Strict + L² ⇒ weak** (FY §2.1.1, p. 30): a strictly stationary process with a
square-integrable marginal is (weakly) stationary. -/
theorem IsStrictlyStationary.isStationary [IsProbabilityMeasure μ]
    (h : IsStrictlyStationary X μ)
    -- LEAN-ONLY: coordinate random variables are measurable; implicit in FY
    (hmeas : ∀ t, Measurable (X t))
    -- USER-INPUT: finite second moment (at one time; propagates); FY §2.1.1 p. 30
    (hL2 : MemLp (X 0) 2 μ) :
    IsStationary X μ := by
  sorry

/-- The general-tuple formulation of strict stationarity coincides with FY Definition
2.2's consecutive-window form `(X_1, …, X_n) ≐ (X_{1+k}, …, X_{n+k})`. -/
theorem isStrictlyStationary_iff_window
    -- LEAN-ONLY: coordinate random variables are measurable; implicit in FY
    (hmeas : ∀ t, Measurable (X t)) :
    IsStrictlyStationary X μ ↔
      ∀ (n : ℕ) (k : ℤ),
        (μ.map fun ω (i : Fin n) => X ((i : ℕ) + 1 + k) ω)
          = μ.map fun ω (i : Fin n) => X ((i : ℕ) + 1) ω := by
  sorry

end StatLean.TimeSeries
