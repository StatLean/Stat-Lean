import StatLean.TimeSeries.Stationarity.ARMAExistence
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Mul

/-!
# The Gaussian ARMA likelihood (FY §3.3.1, eqs. (3.9)–(3.13))

The parametric objects of ARMA maximum likelihood:

* the **model-implied ACVF** `armaACVF b a k = Σ_j ψ_j ψ_{j+|k|}` (unit noise
  variance; FY eq. (2.2) applied to the transfer coefficients `armaPsi`) and its
  Toeplitz matrices `armaToeplitz`;
* the **identifiability/invertibility constraint set** (FY eq. (3.11)):
  `b(z) a(z) ≠ 0` on `|z| ≤ 1` (`ARMAInvertibleParams`);
* the **Gaussian negative twice-log-likelihood** in covariance form
  (`armaNegTwoLogLik`; equivalent to FY's innovations form (3.9) through the LDLᵀ
  factorization, which FY uses only for computation);
* the **profiling identities** (FY eqs. (3.12)–(3.13)): `σ̂² = S/T` and the profiled
  criterion `log(S/T) + T⁻¹ log det Γ_T`;
* structural targets: summability of the model ACVF on the constraint set (geometric
  ψ-decay), the link `acvf X = σ² · armaACVF` for an actual stationary causal ARMA
  process, and positive-definiteness of `armaToeplitz` on the constraint set (via the
  spectral lower bound `g ≥ c > 0` on the circle).

**MLE (FY eq. (3.10)).** The book prints `arg min` — corrected to `arg max` of the
likelihood, i.e. minimization of `armaNegTwoLogLik`; estimator sequences are treated
as hypotheses ("a measurable sequence minimizing the criterion over the constraint
set"), consumed by `ARMA/MLEAsymptotics.lean`.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §3.3.1,
eqs. (3.9)–(3.13) (pp. 93–95). (`FY §3.3.1`.)

**Bibliographic comments.** The innovations-form Gaussian likelihood is Schweppe
(1965) / Ansley (1979); the covariance form is classical multivariate normal theory.
Root-flipping identifiability is Brockwell & Davis (1991) Prop 4.4.2.
-/

open MeasureTheory ProbabilityTheory Filter Polynomial
open scoped ProbabilityTheory Topology Real

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **model-implied ACVF at unit noise variance** (FY eq. (2.2) for the transfer
coefficients): `γ_{b,a}(k) = Σ_{j≥0} ψ_j ψ_{j+|k|}`; junk (`tsum` = 0 convention)
outside the summable regime. -/
noncomputable def armaACVF {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (k : ℤ) : ℝ :=
  ∑' j : ℕ, armaPsi b a j * armaPsi b a (j + k.natAbs)

/-- The model-implied Toeplitz covariance matrix `Γ_T(b, a)` (unit noise variance). -/
noncomputable def armaToeplitz {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (T : ℕ) :
    Matrix (Fin T) (Fin T) ℝ :=
  Matrix.of fun i j => armaACVF b a ((i : ℤ) - (j : ℤ))

/-- **FY eq. (3.11)**: the identifiability/invertibility parameter set
`𝓑 = {(b, a) : b(z) a(z) ≠ 0 for |z| ≤ 1}`. -/
def ARMAInvertibleParams {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) : Prop :=
  NoRootClosedDisc b ∧ ∀ z : ℂ, ‖z‖ ≤ 1 → Polynomial.aeval z (maPoly a) ≠ 0

/-- The **Gaussian negative twice-log-likelihood** of data `x` under the ARMA
parameters `(b, a, σ²)`, covariance form:
`T log(2πσ²) + log det Γ_T + σ⁻² xᵀ Γ_T⁻¹ x` (junk when `Γ_T` is singular, by the
matrix-inverse convention). -/
noncomputable def armaNegTwoLogLik {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    (σ2 : ℝ) {T : ℕ} (x : Fin T → ℝ) : ℝ :=
  (T : ℝ) * Real.log (2 * π * σ2) + Real.log (armaToeplitz b a T).det
    + σ2⁻¹ * (x ⬝ᵥ ((armaToeplitz b a T)⁻¹ *ᵥ x))

/-- The **profiling sum of squares** `S(b, a) = xᵀ Γ_T⁻¹ x` (FY eq. (3.12)'s
numerator). -/
noncomputable def armaProfileS {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    {T : ℕ} (x : Fin T → ℝ) : ℝ :=
  x ⬝ᵥ ((armaToeplitz b a T)⁻¹ *ᵥ x)

/-- **FY eq. (3.13)**: the profiled (σ²-maximized) criterion
`ℓ*(b, a) = log(S(b, a)/T) + T⁻¹ log det Γ_T`. -/
noncomputable def armaProfileCriterion {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ)
    {T : ℕ} (x : Fin T → ℝ) : ℝ :=
  Real.log (armaProfileS b a x / T) + (T : ℝ)⁻¹ * Real.log (armaToeplitz b a T).det

/-- On the constraint set the model ACVF is absolutely summable (geometric ψ-decay,
FY Thm 2.1 machinery). -/
theorem summable_abs_armaACVF {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hB : ARMAInvertibleParams b a) :
    Summable fun k : ℤ => |armaACVF b a k| := by
  sorry

/-- **The model/process ACVF link**: a stationary causal ARMA(p, q) process with noise
variance `σ²` has `acvf X μ k = σ² · armaACVF b a k` (FY eq. (2.2); connects the
parametric likelihood objects to the process). -/
theorem acvf_eq_smul_armaACVF [IsProbabilityMeasure μ] {p q : ℕ}
    {b : Fin p → ℝ} {a : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b a σ2 X ε μ)
    -- USER-INPUT: causal representation; FY §3.1 standing assumption
    (hcausal : IsLinearProcessOf (armaPsi b a) X ε μ)
    -- USER-INPUT: no roots on the closed disc; FY §3.1
    (hroot : NoRootClosedDisc b) (k : ℤ) :
    acvf X μ k = σ2 * armaACVF b a k := by
  sorry

/-- **FY eq. (3.12)**: at fixed `(b, a)` the Gaussian likelihood is maximized in `σ²`
at `σ̂² = S(b, a)/T`, and the minimized value is the profiled criterion up to the
additive constant `T(log(2π) + 1)`. Requires nondegenerate data (`S > 0`). -/
theorem armaNegTwoLogLik_profile {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    {T : ℕ} (hT : 0 < T) {x : Fin T → ℝ}
    -- LEAN-ONLY: nondegenerate profiling sum (a.s. under continuous data laws)
    (hS : 0 < armaProfileS b a x) :
    (∀ σ2 : ℝ, 0 < σ2 →
        armaNegTwoLogLik b a (armaProfileS b a x / T) x ≤ armaNegTwoLogLik b a σ2 x) ∧
      armaNegTwoLogLik b a (armaProfileS b a x / T) x
        = (T : ℝ) * armaProfileCriterion b a x + (T : ℝ) * (Real.log (2 * π) + 1) := by
  sorry

/-- **Positive-definiteness of the model Toeplitz matrices** on the constraint set:
the spectral density of the model is bounded below by a positive constant on the
circle (`|a|²/|b|²` continuous and root-free), so every `Γ_T(b, a)` is positive
definite; in particular invertible. (FY uses this silently in (3.9)–(3.13).) -/
theorem armaToeplitz_posDef {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hB : ARMAInvertibleParams b a) (T : ℕ) :
    (armaToeplitz b a T).PosDef := by
  sorry

end StatLean.TimeSeries
