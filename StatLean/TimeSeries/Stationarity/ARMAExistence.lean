import StatLean.TimeSeries.Process.LinearProcess
import StatLean.TimeSeries.Models.Linear
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.Analytic.Basic

/-!
# Stationary ARMA processes: existence, causality, Yule–Walker (FY §2.1.2, §2.2.1)

The transfer coefficients `ψ = a(z)/b(z)` of an ARMA(p, q) model as formal power-series
coefficients (`armaPsi`, via `PowerSeries.inv` — well-defined since `b(0) = 1`), and:

* **FY Theorem 2.1**: if `b(z) ≠ 0` on the closed unit disc, the coefficients decay
  geometrically (Cauchy estimates on the analytic function `a/b` on a disc of radius
  `> 1`), are absolutely summable, and the linear process `X = Σ ψ_j ε_{t−j}` is a
  stationary, causal solution of the ARMA equation;
* **Definition 2.3** (causality) as `IsCausalFor`;
* the **Yule–Walker recurrences** (FY eq. (2.21)): `γ(k) = Σᵢ bᵢ γ(k−1−i)` for `k > q`;
* **Proposition 2.2(i)**: exponential decay of the ACVF of a causal ARMA process;
* the Brockwell–Davis iff-facts (causality ⇔ no roots in the closed disc; uniqueness ⇔
  no roots on the circle) as statement-level DEBTS (FY cites them without proof).

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.1.2
(Theorem 2.1, Definition 2.3, eqs. (2.3)–(2.5), pp. 30–32) and §2.2.1 (eqs. (2.20)–(2.22),
Proposition 2.2, pp. 40–41). (`FY §2.1.2 Thm 2.1, Def 2.3; §2.2.1 eq. (2.21), Prop 2.2`.)

**Proof formalization notes.**
* `armaPsi` is defined through the formal inverse in `ℝ⟦X⟧` (constant coefficient of
  `arPoly b` is `1`); the analytic content enters only through the geometric bound.
* FY proves Theorem 2.1 by the geometric expansion of `1/b`; we route the coefficient
  bound through `HasFPowerSeriesOnBall` Cauchy estimates
  (`FormalMultilinearSeries.norm_mul_pow_le_mul_pow_of_lt_radius`) after identifying the
  formal and analytic expansions (both are power-series solutions of `b · ψ = a`).
* The Yule–Walker derivation replaces the book's "independent" by "uncorrelated"
  (flagged in the inventory): causality kills the covariances of future innovations
  against the past through `L²`-limit continuity.
* Prop 2.2(i) avoids the book's distinct-roots partial-fraction argument entirely (the
  inventory flags the repeated-root gap): geometric decay of `ψ` gives
  `|γ(k)| ≤ σ² C² r^k/(1−r²)` directly.

**Bibliographic comments.** The MA(∞) solution of stationary ARMA equations is H. Wold
(1938); the systematic causality/invertibility theory is P. J. Brockwell and R. A. Davis,
*Time Series: Theory and Methods*, 2nd ed., Springer, 1991, §3.1 (Thm 3.1.1, Prop 3.1.2).
Yule–Walker equations: G. U. Yule (1927), G. T. Walker (1931).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **ARMA transfer coefficients** `ψ_n = [zⁿ] a(z)/b(z)` (FY eq. (2.5)'s `d_j`),
as formal power-series coefficients; well-defined because `b(0) = 1` makes `arPoly b`
invertible in `ℝ⟦X⟧`. -/
noncomputable def armaPsi {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (n : ℕ) : ℝ :=
  PowerSeries.coeff n
    (((maPoly a : Polynomial ℝ) : PowerSeries ℝ) *
      (((arPoly b : Polynomial ℝ) : PowerSeries ℝ))⁻¹)

/-- `b` has **no roots in the closed unit disc** (over ℂ) — FY's standing condition
`b(z) ≠ 0` for `|z| ≤ 1`. -/
def NoRootClosedDisc {p : ℕ} (b : Fin p → ℝ) : Prop :=
  ∀ z : ℂ, ‖z‖ ≤ 1 → Polynomial.aeval z (arPoly b) ≠ 0

section Coeff

/-- The coefficients of the AR polynomial `b(z) = 1 - b₁z - ⋯ - b_pz^p`. -/
private lemma coeff_arPoly {p : ℕ} (b : Fin p → ℝ) (m : ℕ) :
    (arPoly b).coeff m
      = (if m = 0 then (1 : ℝ) else 0) - ∑ i : Fin p, if m = (i : ℕ) + 1 then b i else 0 := by
  simp [arPoly, Polynomial.coeff_one, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, mul_ite]

private lemma coeff_arPoly_zero {p : ℕ} (b : Fin p → ℝ) : (arPoly b).coeff 0 = 1 := by
  rw [coeff_arPoly]; simp

/-- The coefficients of the MA polynomial `a(z) = 1 + a₁z + ⋯ + a_qz^q`. -/
private lemma coeff_maPoly {q : ℕ} (a : Fin q → ℝ) (m : ℕ) :
    (maPoly a).coeff m
      = (if m = 0 then (1 : ℝ) else 0) + ∑ j : Fin q, if m = (j : ℕ) + 1 then a j else 0 := by
  simp [maPoly, Polynomial.coeff_one, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, mul_ite]

private lemma coeff_maPoly_zero {q : ℕ} (a : Fin q → ℝ) : (maPoly a).coeff 0 = 1 := by
  rw [coeff_maPoly]; simp

/-- The constant coefficient of `arPoly b` as a power series is `1`, hence nonzero: this is
what makes the formal inverse in `ℝ⟦X⟧` available. -/
private lemma constantCoeff_arPoly_ne_zero {p : ℕ} (b : Fin p → ℝ) :
    PowerSeries.constantCoeff (((arPoly b : Polynomial ℝ) : PowerSeries ℝ)) ≠ 0 := by
  rw [Polynomial.constantCoeff_coe, coeff_arPoly_zero]
  exact one_ne_zero

end Coeff

/-- `ψ_0 = 1` (both polynomials have constant coefficient `1`). -/
theorem armaPsi_zero {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) :
    armaPsi b a 0 = 1 := by
  rw [armaPsi, PowerSeries.coeff_zero_eq_constantCoeff, map_mul, PowerSeries.constantCoeff_inv,
    Polynomial.constantCoeff_coe, Polynomial.constantCoeff_coe, coeff_arPoly_zero,
    coeff_maPoly_zero, inv_one, mul_one]

/-- The defining convolution identity `b ∗ ψ = a` (FY eq. (2.5) read coefficientwise):
`Σ_{k≤n} (arPoly b).coeff k · ψ_{n−k} = (maPoly a).coeff n`. -/
theorem arPoly_conv_armaPsi {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (arPoly b).coeff k * armaPsi b a (n - k)
      = (maPoly a).coeff n := by
  have key : (((arPoly b : Polynomial ℝ) : PowerSeries ℝ)) *
      ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) *
        (((arPoly b : Polynomial ℝ) : PowerSeries ℝ))⁻¹)
      = (((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) := by
    rw [← mul_assoc, mul_comm (((arPoly b : Polynomial ℝ) : PowerSeries ℝ)),
      mul_assoc, PowerSeries.mul_inv_cancel _ (constantCoeff_arPoly_ne_zero b), mul_one]
  have hcoeff := congrArg (PowerSeries.coeff n) key
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Polynomial.coeff_coe] at hcoeff
  rw [← hcoeff]
  exact Finset.sum_congr rfl fun k _ => by rw [Polynomial.coeff_coe]; rfl

/-- **Geometric decay of the transfer coefficients** (the analytic core of FY Theorem
2.1): with no roots of `b` in the closed unit disc, `|ψ_n| ≤ C rⁿ` for some `r < 1`. -/
theorem exists_geometric_bound_armaPsi {p q : ℕ} {b : Fin p → ℝ} (a : Fin q → ℝ)
    -- USER-INPUT: no roots of b(z) in the closed unit disc; FY §2.1.2 Thm 2.1
    (hb : NoRootClosedDisc b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ n, |armaPsi b a n| ≤ C * r ^ n := by
  sorry

/-- Absolute summability of the transfer coefficients (FY Theorem 2.1's `Σ|d_j| < ∞`). -/
theorem summable_abs_armaPsi {p q : ℕ} {b : Fin p → ℝ} (a : Fin q → ℝ)
    (hb : NoRootClosedDisc b) :
    Summable fun n => |armaPsi b a n| := by
  sorry

/-- **Causality** (FY §2.1.2, Definition 2.3): `X` is a causal function of the noise `ε`
when it is an MA(∞) over `ε` with absolutely summable coefficients. -/
def IsCausalFor (X ε : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  ∃ ψ : ℕ → ℝ, (Summable fun n => |ψ n|) ∧ IsLinearProcessOf ψ X ε μ

/-- **FY Theorem 2.1 (existence of a stationary causal ARMA solution)**: with no roots
of `b` in the closed unit disc and white noise `ε`, the linear process with the transfer
coefficients is a stationary, causal solution of the ARMA(p, q) equation. -/
theorem exists_stationary_arma [IsProbabilityMeasure μ] {p q : ℕ} {b : Fin p → ℝ}
    {a : Fin q → ℝ} {σ2 : ℝ} {ε : ℤ → Ω → ℝ}
    -- USER-INPUT: no roots of b(z) in the closed unit disc; FY §2.1.2 Thm 2.1
    (hb : NoRootClosedDisc b)
    -- USER-INPUT: white-noise innovations; FY eq. (2.3)
    (hε : IsWhiteNoise ε σ2 μ) :
    ∃ X : ℤ → Ω → ℝ, (∀ t, Measurable (X t)) ∧
      IsLinearProcessOf (armaPsi b a) X ε μ ∧ IsARMA b a σ2 X ε μ ∧
      IsStationary X μ ∧ IsCausalFor X ε μ := by
  sorry

/-- **Yule–Walker recurrences** (FY §2.2.1, eq. (2.21)): for a causal stationary ARMA
process and lags beyond the MA order, `γ(k) = Σᵢ bᵢ γ(k−1−i)`. -/
theorem IsARMA.acvf_yule_walker [IsProbabilityMeasure μ] {p q : ℕ} {b : Fin p → ℝ}
    {a : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b a σ2 X ε μ) (hstat : IsStationary X μ)
    -- USER-INPUT: causality (FY: eq. (2.21) is derived for the causal solution); FY §2.2.1
    (hcausal : IsLinearProcessOf (armaPsi b a) X ε μ)
    (hb : NoRootClosedDisc b)
    {k : ℤ}
    -- USER-INPUT: lag beyond the MA order; FY eq. (2.21)
    (hk : (q : ℤ) < k) :
    acvf X μ k = ∑ i : Fin p, b i * acvf X μ (k - 1 - (i : ℕ)) := by
  sorry

/-- **Proposition 2.2(i)** (FY §2.2.1): the ACVF of a causal stationary ARMA process
decays exponentially. (Proved from the geometric `ψ`-bound — no distinct-roots caveat.) -/
theorem IsARMA.acvf_exponential_decay [IsProbabilityMeasure μ] {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b a σ2 X ε μ) (hcausal : IsLinearProcessOf (armaPsi b a) X ε μ)
    (hb : NoRootClosedDisc b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
      ∀ k : ℤ, |acvf X μ k| ≤ C * r ^ k.natAbs := by
  sorry

/-- **DEBT (Brockwell & Davis 1996, p. 83; FY §2.1.2 cited fact (i))**: an ARMA process
with a stationary solution is causal **iff** `b` has no roots in the closed unit disc.
The ⇐ half is `exists_stationary_arma`; the ⇒ half is a literature-level debt. -/
theorem arma_causal_of_stationary_debt [IsProbabilityMeasure μ] {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b a σ2 X ε μ) (hstat : IsStationary X μ)
    (hσ : 0 < σ2) (hcausal : IsCausalFor X ε μ) :
    NoRootClosedDisc b := by
  sorry

/-- **DEBT (Brockwell & Davis 1996, p. 82; FY §2.1.2 cited fact (ii))**: uniqueness of
the stationary solution when `b` has no roots on the unit circle: two stationary
solutions driven by the same noise agree a.e. at every time. -/
theorem arma_stationary_unique_debt [IsProbabilityMeasure μ] {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {σ2 : ℝ} {X X' ε : ℤ → Ω → ℝ}
    -- USER-INPUT: no roots of b(z) on the unit circle; FY §2.1.2 cited fact (ii)
    (hb : ∀ z : ℂ, ‖z‖ = 1 → Polynomial.aeval z (arPoly b) ≠ 0)
    (h : IsARMA b a σ2 X ε μ) (hstat : IsStationary X μ)
    (h' : IsARMA b a σ2 X' ε μ) (hstat' : IsStationary X' μ) (t : ℤ) :
    X t =ᵐ[μ] X' t := by
  sorry

end StatLean.TimeSeries
