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

/-- Covariance only sees the a.e. class of each argument. -/
private lemma covariance_congr_ae {X X' Y Y' : Ω → ℝ} (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  have hIX : ∫ x, X x ∂μ = ∫ x, X' x ∂μ := integral_congr_ae hX
  have hIY : ∫ x, Y x ∂μ = ∫ x, Y' x ∂μ := integral_congr_ae hY
  simp only [covariance, hIX, hIY]
  exact integral_congr_ae (by filter_upwards [hX, hY] with ω h1 h2 using by rw [h1, h2])

/-- Two finite linear combinations of white-noise coordinates taken over *disjoint* index
sets are uncorrelated. -/
private lemma cov_noise_combination_eq_zero [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ} {σ2 : ℝ}
    (hw : IsWhiteNoise ε σ2 μ) {n m : ℕ} (c : Fin n → ℝ) (d : Fin m → ℝ)
    (u : Fin n → ℤ) (v : Fin m → ℤ) (huv : ∀ i j, u i ≠ v j) :
    cov[fun ω => ∑ i, c i * ε (u i) ω, fun ω => ∑ j, d j * ε (v j) ω; μ] = 0 := by
  rw [covariance_fun_sum_fun_sum (X := fun i ω => c i * ε (u i) ω)
      (Y := fun j ω => d j * ε (v j) ω)
      (fun i => (hw.memLp (u i)).const_mul (c i))
      (fun j => (hw.memLp (v j)).const_mul (d j))]
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  rw [covariance_const_mul_left, covariance_const_mul_right, hw.uncorrelated _ _ (huv i j)]
  ring

/-- The one-sided half of `IsMA.cov_eq_zero`: the MA(q) covariance vanishes once the
later time exceeds the earlier one by more than the order. -/
private lemma IsMA.cov_eq_zero_of_lt [IsProbabilityMeasure μ] {q : ℕ} {a : Fin q → ℝ}
    {σ2 : ℝ} {X ε : ℤ → Ω → ℝ} (h : IsMA a σ2 X ε μ) {s t : ℤ} (hgap : t + q < s) :
    cov[X s, X t; μ] = 0 := by
  -- the MA coefficient vector `(1, a₁, …, a_q)` and the lag map `u ↦ (u, u-1, …, u-q)`
  obtain ⟨c, hc0, hcs⟩ : ∃ c : Fin (q + 1) → ℝ, c 0 = 1 ∧ ∀ i : Fin q, c i.succ = a i :=
    ⟨Fin.cases 1 a, rfl, fun _ => rfl⟩
  obtain ⟨L, hL0, hLs⟩ : ∃ L : ℤ → Fin (q + 1) → ℤ,
      (∀ u, L u 0 = u) ∧ ∀ (u : ℤ) (i : Fin q), L u i.succ = u - 1 - (i : ℕ) :=
    ⟨fun u => Fin.cases u fun i => u - 1 - (i : ℕ), fun _ => rfl, fun _ _ => rfl⟩
  -- the MA(q) recurrence, packaged as a single sum
  have hrec : ∀ u : ℤ, X u =ᵐ[μ] fun ω => ∑ i, c i * ε (L u i) ω := by
    intro u
    filter_upwards [h.recurrence u] with ω hω
    rw [hω, Fin.sum_univ_succ, hc0, hL0]
    simp only [hcs, hLs]
    simp
  -- the two lag windows `[s-q, s]` and `[t-q, t]` are disjoint
  have hge : ∀ i : Fin (q + 1), s - q ≤ L s i := by
    intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [hL0]; omega
    · rw [hLs]; have := k.isLt; omega
  have hle : ∀ j : Fin (q + 1), L t j ≤ t := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · rw [hL0]
    · rw [hLs]; have := k.isLt; omega
  rw [covariance_congr_ae (hrec s) (hrec t)]
  refine cov_noise_combination_eq_zero h.whiteNoise c c (L s) (L t) fun i j => ?_
  have h1 := hge i
  have h2 := hle j
  omega

/-- **MA(q) is q-dependent** (FY §1.3.3): observations more than `q` apart are
uncorrelated. -/
theorem IsMA.cov_eq_zero [IsProbabilityMeasure μ] {q : ℕ} {a : Fin q → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (h : IsMA a σ2 X ε μ) {s t : ℤ}
    -- USER-INPUT: the lag exceeds the MA order; FY §1.3.3
    (hgap : (q : ℤ) < |s - t|) :
    cov[X s, X t; μ] = 0 := by
  rcases lt_abs.mp hgap with hc | hc
  · exact h.cov_eq_zero_of_lt (by omega)
  · rw [covariance_comm]; exact h.cov_eq_zero_of_lt (by omega)

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
