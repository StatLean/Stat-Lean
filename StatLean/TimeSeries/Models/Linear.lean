import StatLean.TimeSeries.Models.WhiteNoise

/-!
# Linear models — the chapter-1 structural claims (FY §1.3.3–§1.3.5)

The provable claims of FY ch. 1 about the linear model classes:

* **MA(q) is q-dependent in covariance** (FY §1.3.3, "obviously"): observations more
  than `q` apart share no innovations, hence are uncorrelated;
* **MA(1) inversion** (FY §1.3.3, "it can be proved"): for `|a| < 1`, the partial sums
  `Σ_{j≤N} (−a)^j X_{t−j}` recover `ε_t` in probability (the concrete instance
  `a = −0.9` is the book's display);
* **ARIMA is a (typically nonstationary) ARMA(p+d, q)** (FY §1.3.5, "easy to see";
  the book misprints the MA order as `p`): the differenced recurrence composes to the
  AR polynomial `b(z)(1−z)^d` of degree `p + d`.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §1.3.3
(p. 12), §1.3.5 (pp. 13–14). (`FY §1.3.3; §1.3.5`.)

**Proof formalization notes.**
* `IsMA.cov_eq_zero` computes `cov` of the two a.e. finite innovation sums bilinearly
  against `IsWhiteNoise.uncorrelated`; the index gap `|s − t| > q` empties the diagonal.
* In `IsARIMA.satisfiesARMA` the composed AR coefficients are read off the polynomial
  `arPoly b * (1 − X)^d`; sign convention: our `SatisfiesARMA` coefficients are the
  *negatives* of that polynomial's nonconstant coefficients (the constant term is `1`).
* The MA(1) inversion is stated as convergence in probability (`TendstoInMeasure`),
  matching the book's claim; the geometric remainder bound `‖(−a)^N ε_{t−N}‖ → 0` runs
  through Chebyshev on an `L²` bound.

**Bibliographic comments.** Invertibility of moving averages and the AR(∞)
representation are due to H. Wold (1938) and were systematized by G. E. P. Box and
G. M. Jenkins (1970), where ARIMA modeling (differencing to stationarity) originates.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **MA(q) is q-dependent** (FY §1.3.3): observations more than `q` apart are
uncorrelated. -/
theorem IsMA.cov_eq_zero [IsProbabilityMeasure μ] {q : ℕ} {a : Fin q → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (h : IsMA a σ2 X ε μ) {s t : ℤ}
    -- USER-INPUT: the lag exceeds the MA order; FY §1.3.3
    (hgap : (q : ℤ) < |s - t|) :
    cov[X s, X t; μ] = 0 := by
  sorry

/-- **MA(1) inversion** (FY §1.3.3): for an MA(1) with `|a₁| < 1`, the alternating
geometric partial sums of lagged observations recover the innovation in probability:
`Σ_{j=0}^{N} (−a₁)^j X_{t−j} → ε_t`. (The book's display is the instance `a₁ = −0.9`:
`X_t + Σ_{j≥1} 0.9^j X_{t−j} = ε_t`.) -/
theorem IsMA.tendstoInMeasure_inversion [IsProbabilityMeasure μ] {a1 : ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ}
    (h : IsMA (fun _ : Fin 1 => a1) σ2 X ε μ)
    -- USER-INPUT: invertibility |a₁| < 1; FY §1.3.3
    (ha : |a1| < 1) (t : ℤ) :
    TendstoInMeasure μ
      (fun N ω => ∑ j ∈ Finset.range (N + 1), (-a1) ^ j * X (t - (j : ℕ)) ω)
      atTop (ε t) := by
  sorry

/-- **ARIMA(p,d,q) satisfies an ARMA(p+d, q) recurrence** (FY §1.3.5; the book's
"ARMA(p+d, p)" is a misprint for the MA order `q`): the composed AR coefficients are
read off `b(z)(1−z)^d`. Nonstationarity of `Y` itself is the typical situation and is
not claimed here. -/
theorem IsARIMA.satisfiesARMA {p q d : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ} {σ2 : ℝ}
    {Y ε : ℤ → Ω → ℝ} (h : IsARIMA b a d σ2 Y ε μ) :
    SatisfiesARMA
      (fun i : Fin (p + d) =>
        -((arPoly b * (1 - Polynomial.X) ^ d).coeff ((i : ℕ) + 1)))
      a Y ε μ := by
  sorry

end StatLean.TimeSeries
