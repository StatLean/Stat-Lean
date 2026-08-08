import StatLean.TimeSeries.Models.Defs
import StatLean.TimeSeries.ForMathlib.Markov.GeometricErgodicity
import StatLean.TimeSeries.Process.Stationary

/-!
# Threshold autoregression: structure and stationarity (FY §4.1.1, Definition 4.1)

The `k`-regime TAR model is `Models/Defs.lean`'s `IsTAR` (FY eq. (4.1)). This file
carries the §4.1.1 structural facts:

* **SETAR** (`IsSETAR`): the interval-partition special case
  `A_i = (r_{i−1}, r_i]` with `−∞ = r_0 < ⋯ < r_k = +∞`, and the fact that a SETAR
  partition is a legitimate TAR partition;
* the **stationarity claim** of pp. 126–127 ("easy to see from Theorem 2.4"): under
  (a) equal regime scales `σ₁ = ⋯ = σ_k` *(the book prints `σ_p` — typo)* and
  (b) `max_i Σ_j |b_{ij}| < 1`, a strictly stationary solution exists. FY delegates
  this entirely to §2.1.4's Theorem 2.4 + Example 2.1, so we state it as a corollary
  of the Markov-layer debt `nlARKernel_geometricallyErgodic` (whose closure is
  batch F's `ts/f-thm24`): the TAR autoregression function is the `nlARKernel`
  drift function, and the contraction condition (b) is the Lyapunov input;
* the **canonical toy instance** eq. (4.2), `X_t = ∓0.7 X_{t−1} + ε_t` according to the
  sign of `X_{t−1} − r`, exhibited as a two-regime SETAR satisfying (a)+(b).

**Scope.** FY Theorems 4.1 and 4.2 (Chan 1993a: strong consistency; `T(r̂ − r) = O_p(1)`
and the associated asymptotics) and their consumers were **descoped on 2026-08-04** at
the user's direction and are not stated anywhere in this area.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §4.1.1,
Definition 4.1, eqs. (4.1)–(4.3) and the stationarity discussion pp. 126–127.
(`FY §4.1.1`.)

**Bibliographic comments.** Threshold autoregression is H. Tong (1978; *Non-linear Time
Series: A Dynamical System Approach*, OUP 1990); the drift/ergodicity route for TAR
stationarity is An & Huang (1996) and Chan & Tong (1985).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **SETAR interval partition** determined by ordered thresholds
`r : Fin (k − 1) → ℝ`: regime `i` is `(r_{i−1}, r_i]` with the conventions
`r_{−1} = −∞`, `r_{k−1} = +∞`. -/
def setarPartition {k : ℕ} (r : Fin k → ℝ) : Fin (k + 1) → Set ℝ := fun i =>
  {x : ℝ | (∀ j : Fin k, (j : ℕ) < (i : ℕ) → r j < x) ∧
    ∀ j : Fin k, (i : ℕ) ≤ (j : ℕ) → x ≤ r j}

/-- A SETAR partition is a measurable partition of `ℝ` (so `IsTAR` applies to it):
the regimes are measurable, pairwise disjoint, and cover the line. -/
theorem setarPartition_isPartition {k : ℕ} {r : Fin k → ℝ} (hr : StrictMono r) :
    (∀ i, MeasurableSet (setarPartition r i)) ∧
      (Pairwise fun i j => Disjoint (setarPartition r i) (setarPartition r j)) ∧
      (⋃ i, setarPartition r i) = Set.univ := by
  sorry

/-- **SETAR model** (FY §4.1.1): a TAR whose regimes form an interval partition. -/
def IsSETAR {k P : ℕ} (b0 : Fin (k + 1) → ℝ) (b : Fin (k + 1) → Fin P → ℝ)
    (σ : Fin (k + 1) → ℝ) (r : Fin k → ℝ) (d : ℕ) (X ε : ℤ → Ω → ℝ)
    (μ : Measure Ω) : Prop :=
  StrictMono r ∧ IsTAR b0 b σ (setarPartition r) d X ε μ

/-- The **TAR autoregression function** on the state vector `(x_{t−1}, …, x_{t−P})`
extended with the threshold coordinate: `f(𝐱) = Σᵢ (b_{i0} + Σⱼ b_{ij} x_j)·1_{A_i}(x_d)`
(FY eq. (4.1) without the noise term). Used to instantiate the Markov layer's
`nlARKernel`. -/
noncomputable def tarDrift {k P : ℕ} (b0 : Fin k → ℝ) (b : Fin k → Fin P → ℝ)
    (A : Fin k → Set ℝ) (d : ℕ) (x : Fin (P + 1) → ℝ) : ℝ :=
  ∑ i, (A i).indicator
    (fun _ => b0 i + ∑ j : Fin P, b i j * x (j.castSucc)) (x ⟨min d P, by omega⟩)

/-- **FY §4.1.1, pp. 126–127 (delegated to Theorem 2.4)**: under equal regime scales and
the uniform contraction `max_i Σ_j |b_{ij}| < 1`, the TAR state chain is geometrically
ergodic, hence admits a strictly stationary solution. Stated as a corollary of the
Markov-layer statement `nlARKernel_geometricallyErgodic` (FY Thm 2.4(ii)); the closure
of that statement is batch F. -/
theorem exists_stationary_tar [IsProbabilityMeasure μ] {k P : ℕ}
    {b0 : Fin k → ℝ} {b : Fin k → Fin P → ℝ} {σ0 : ℝ} {A : Fin k → Set ℝ} {d : ℕ}
    -- USER-INPUT: measurable partition of ℝ; FY Def 4.1
    (hA : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise fun i j => Disjoint (A i) (A j))
    (hcov : (⋃ i, A i) = Set.univ)
    -- USER-INPUT: equal regime scales (book prints σ_p — typo for σ₁ = ⋯ = σ_k);
    -- FY p. 126 condition (a)
    (hσ : 0 < σ0)
    -- USER-INPUT: uniform contraction; FY p. 126 condition (b)
    (hcontract : ∀ i, (∑ j, |b i j|) < 1)
    -- USER-INPUT: delay within the state window; FY Def 4.1
    (hd : 1 ≤ d) (hdP : d ≤ P)
    -- USER-INPUT: innovation law with a continuous positive density (the Theorem 2.4
    -- hypothesis, in the strengthened form documented in
    -- `ForMathlib/Markov/GeometricErgodicity.lean`); FY §2.1.4 Example 2.1
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ∃ g : ℝ → ℝ, Continuous g ∧ (∀ x, 0 < g x) ∧
      ν = MeasureTheory.volume.withDensity fun x => ENNReal.ofReal (g x))
    (hν2 : Integrable (fun x : ℝ => x ^ 2) ν) (hνmean : ∫ x, x ∂ν = 0) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω') (X' ε' : ℤ → Ω' → ℝ),
      IsProbabilityMeasure μ' ∧
        IsTAR b0 b (fun _ => σ0) A d X' ε' μ' ∧ IsStrictlyStationary X' μ' := by
  sorry

/-- **FY eq. (4.2)** (the canonical toy SETAR): `X_t = −0.7 X_{t−1} + ε_t` when
`X_{t−1} ≤ r` and `X_t = 0.7 X_{t−1} + ε_t` when `X_{t−1} > r` satisfies the two
stationarity conditions of pp. 126–127, so a strictly stationary solution exists. -/
theorem exists_stationary_toy_setar [IsProbabilityMeasure μ] (r : ℝ)
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ∃ g : ℝ → ℝ, Continuous g ∧ (∀ x, 0 < g x) ∧
      ν = MeasureTheory.volume.withDensity fun x => ENNReal.ofReal (g x))
    (hν2 : Integrable (fun x : ℝ => x ^ 2) ν) (hνmean : ∫ x, x ∂ν = 0) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω') (X' ε' : ℤ → Ω' → ℝ),
      IsProbabilityMeasure μ' ∧
        IsTAR (fun _ : Fin 2 => (0 : ℝ))
          (fun i : Fin 2 => fun _ : Fin 1 => if i = 0 then (-0.7 : ℝ) else 0.7)
          (fun _ => (1 : ℝ))
          (fun i : Fin 2 => if i = 0 then {x : ℝ | x ≤ r} else {x : ℝ | r < x})
          1 X' ε' μ' ∧
        IsStrictlyStationary X' μ' := by
  sorry

end StatLean.TimeSeries
