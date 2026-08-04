import StatLean.TimeSeries.ForMathlib.Markov.Chain
import StatLean.Minimaxity.ForMathlib.TotalVariation
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Ergodicity and geometric ergodicity of Markov kernels (FY Definition 2.4)

FY Definition 2.4: the chain with kernel `κ` is *ergodic* (rate `ρ = 1`) resp.
*geometrically ergodic* (rate `ρ < 1`) toward a law `F` when
`ρ⁻ⁿ ‖κⁿ(x, ·) − F‖_TV → 0` for every starting state `x`. We phrase total variation via
the cross-area brick `StatLean.Minimaxity.tvDist` (the sup-over-events distance, half of
the book's `L¹` norm — a constant factor immaterial to every convergence-to-zero
statement, documented deviation).

Also here: the transition kernel `nlARKernel` of the vectorized nonlinear autoregression
`X_t = f(X_{t-1}, …, X_{t-p-1}) + ε_t` (FY eqs. (2.7)–(2.8)) and the **statement-level
debt** for FY Theorem 2.4(ii) — the drift/contraction criterion for geometric ergodicity.
§2.1.4 is excluded from the formalization scope by project decision (`TimeSeries_plan.md`),
but its Theorem 2.4 is the certificate that §2.1.5's remark, §4.1's TAR stationarity
claims and Theorem 4.2's hypothesis (i) consume; per the hypothesis-discipline rule it is
therefore *stated* here as a named `sorry` and consumers derive from it. Proof source (if
ever commissioned): An & Huang (1996); Bhattacharya & Lee (1995) — Meyn–Tweedie drift
machinery.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.1.4:
Definition 2.4 with eq. (2.10) (p. 34), eqs. (2.7)–(2.8) (vectorization), Theorem 2.4
(p. 35). (`FY §2.1.4 Def 2.4, Thm 2.4`.)

**Proof formalization notes.**
* `tvDist` is `ℝ≥0∞`-valued; the rate condition multiplies by `ρ⁻¹ ^ n` in `ℝ≥0∞`
  (for `0 < ρ ≤ 1` the inverse is finite except at `ρ = 1`, where `ρ⁻¹ = 1`).
* `nlARKernel` pushes `(x, ε) ↦ (f(x) + ε, x₀, …, x_{p-1})` through `id ×ₖ const ν`;
  the book's misprint `f(x₁)` for `f(𝐱)` in the vectorization display is corrected.
* Theorem 2.4's "`ε_t` has a positive density" is formalized as `ν = volume.withDensity g`
  with everywhere-positive `g`; "mean zero" as `∫ x dν = 0` plus integrability.

**Bibliographic comments.** Geometric ergodicity and drift criteria are the
Foster–Lyapunov tradition: F. G. Foster (1953), R. L. Tweedie ("Sufficient conditions for
ergodicity and recurrence of Markov chains on a general state space", *Stoch. Proc.
Appl.* **3** (1975), 385–403), and S. P. Meyn and R. L. Tweedie, *Markov Chains and
Stochastic Stability*, Springer, 1993. The nonlinear-AR criteria cited by FY are H. Z. An
and F. C. Huang (*Statist. Sinica* **6** (1996), 943–956) and R. Bhattacharya and C. Lee
(*Statist. Probab. Lett.* **22** (1995), 311–315). Harris-type ergodicity: T. E. Harris
(1956); W. Feller, *An Introduction to Probability Theory and Its Applications* II,
§8.7.
-/

open MeasureTheory ProbabilityTheory Filter StatLean.Minimaxity
open scoped ENNReal Topology

namespace StatLean.TimeSeries

variable {S : Type*} [MeasurableSpace S]

/-- **Ergodicity with rate** (FY Definition 2.4, eq. (2.10)): `F` attracts every starting
state in total variation at rate `ρ ∈ (0, 1]`, i.e. `ρ⁻ⁿ ‖κⁿ(x,·) − F‖_TV → 0` for all
`x`. `ρ = 1` is plain (Harris-type) ergodicity; `ρ < 1` is geometric ergodicity. -/
structure IsErgodicWithRate (κ : Kernel S S) (F : Measure S) (ρ : ℝ≥0∞) : Prop where
  /-- Constitutive (FY Def 2.4): the rate is positive. -/
  rho_pos : 0 < ρ
  /-- Constitutive (FY Def 2.4): the rate is at most one. -/
  rho_le_one : ρ ≤ 1
  /-- Constitutive (FY eq. (2.10)): rated total-variation convergence from every state
  (`tvDist` symmetrized against the book's `‖·‖` only by the constant factor 2). -/
  tendsto : ∀ x : S,
    Tendsto (fun n : ℕ => ρ⁻¹ ^ n * tvDist ((κ ^ n) x) F) atTop (𝓝 0)

/-- **Ergodic kernel** (FY Definition 2.4 with `ρ = 1`). -/
def IsErgodicKernel (κ : Kernel S S) (F : Measure S) : Prop :=
  IsErgodicWithRate κ F 1

/-- **Geometrically ergodic kernel** (FY Definition 2.4 with some `ρ < 1`). -/
def IsGeometricallyErgodic (κ : Kernel S S) (F : Measure S) : Prop :=
  ∃ ρ : ℝ≥0∞, ρ < 1 ∧ IsErgodicWithRate κ F ρ

/-- Rated convergence implies plain total-variation convergence (`ρ⁻¹ ^ n ≥ 1`). -/
theorem IsErgodicWithRate.tendsto_tvDist {κ : Kernel S S} {F : Measure S} {ρ : ℝ≥0∞}
    (h : IsErgodicWithRate κ F ρ) (x : S) :
    Tendsto (fun n : ℕ => tvDist ((κ ^ n) x) F) atTop (𝓝 0) := by
  sorry

/-- Geometric ergodicity is ergodicity. -/
theorem IsGeometricallyErgodic.isErgodicKernel {κ : Kernel S S} {F : Measure S}
    (h : IsGeometricallyErgodic κ F) : IsErgodicKernel κ F := by
  sorry

/-- The attracting law of an ergodic Markov kernel is invariant (the invariance half of
FY Theorem 2.2): kernel averaging is a total-variation contraction, so `F = lim κⁿ⁺¹(x,·)
= κ ∘ lim κⁿ(x,·) = κ ∘ F`. -/
theorem IsErgodicKernel.invariant {κ : Kernel S S} [IsMarkovKernel κ] {F : Measure S}
    [IsProbabilityMeasure F] (h : IsErgodicKernel κ F) [Nonempty S] :
    κ.Invariant F := by
  sorry

/-- Transition kernel of the **vectorized nonlinear autoregression** (FY eqs.
(2.7)–(2.8)): from state `x = (X_{t-1}, …, X_{t-p-1})` draw `ε ∼ ν` and move to
`(f(x) + ε, x₀, …, x_{p-1})`. -/
noncomputable def nlARKernel {p : ℕ} (f : (Fin (p + 1) → ℝ) → ℝ) (ν : Measure ℝ) :
    Kernel (Fin (p + 1) → ℝ) (Fin (p + 1) → ℝ) :=
  ((Kernel.id : Kernel (Fin (p + 1) → ℝ) (Fin (p + 1) → ℝ)).prod
    (Kernel.const _ ν)).map fun xe =>
      (Fin.cons (f xe.1 + xe.2) (fun i => xe.1 i.castSucc) : Fin (p + 1) → ℝ)

/-- The nonlinear-AR kernel is Markov for measurable `f` and a probability noise law. -/
theorem isMarkovKernel_nlARKernel {p : ℕ} {f : (Fin (p + 1) → ℝ) → ℝ}
    (hf : Measurable f) (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    IsMarkovKernel (nlARKernel f ν) := by
  sorry

/-- **FY Theorem 2.4(ii) — statement-level DEBT** (§2.1.4 is outside the formalization
scope by project decision; this named statement is the certificate consumed by the TAR
stationarity claims of §4.1 and by Theorem 4.2(i), which derive from it rather than
carrying provider hypotheses). If the autoregression function is a sup-norm contraction
up to a constant and the noise has an everywhere-positive density with zero mean, the
vectorized chain is geometrically ergodic toward some stationary probability law.
Proof source (not in FY): An & Huang (1996), Thm 2.4(ii) route; Meyn–Tweedie drift
machinery. -/
theorem nlARKernel_geometricallyErgodic
    {p : ℕ} {f : (Fin (p + 1) → ℝ) → ℝ}
    -- USER-INPUT: the autoregression function, measurable; FY §2.1.4 Thm 2.4
    (hf : Measurable f)
    {g : ℝ → ℝ≥0∞} (hg : Measurable g)
    -- USER-INPUT: the noise has an (everywhere) positive density; FY §2.1.4 Thm 2.4
    (hgpos : ∀ x, 0 < g x)
    {ν : Measure ℝ} (hν : ν = MeasureTheory.volume.withDensity g)
    [IsProbabilityMeasure ν]
    -- USER-INPUT: integrable, mean-zero noise; FY §2.1.4 Thm 2.4
    (hint : Integrable (fun x : ℝ => x) ν) (hmean : ∫ x, x ∂ν = 0)
    {lam c : ℝ}
    -- USER-INPUT: sup-norm contraction |f(x)| ≤ λ maxᵢ|xᵢ| + c with λ < 1; FY Thm 2.4(ii)
    (hlam0 : 0 ≤ lam) (hlam : lam < 1) (hc : 0 ≤ c)
    (hbound : ∀ x, |f x| ≤ lam * (⨆ i, |x i|) + c) :
    ∃ F : Measure (Fin (p + 1) → ℝ), IsProbabilityMeasure F ∧
      IsGeometricallyErgodic (nlARKernel f ν) F := by
  sorry

end StatLean.TimeSeries
