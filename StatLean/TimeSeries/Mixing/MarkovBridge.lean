import StatLean.TimeSeries.Mixing.Defs
import StatLean.TimeSeries.ForMathlib.Markov.GeometricErgodicity

/-!
# Mixing of Markov chains: the Davydov identity and its consequences (FY §2.6.1(vi)–(vii))

The bridge between the Markov layer (`ForMathlib/Markov/*`) and the mixing coefficients:

* **eq. (2.58) (Davydov 1973)** — for a strictly stationary Markov process with kernel
  `κ` and marginal `F`, the β-coefficient is the mean total-variation distance of the
  `n`-step transition law from the marginal: `β(n) = ∫ ‖κⁿ(x, ·) − F‖_TV dF(x)`.
  Literature DEBT (needs the conditional-probability description of β against
  `condDistrib`).
* **eq. (2.59)** — a geometric-ergodicity envelope `‖κⁿ(x,·) − F‖_TV ≤ A(x) ρⁿ` with
  `∫ A dF < ∞` gives exponential β-mixing: `β(n) ≤ ρⁿ ∫ A dF`. **Derived here** from
  the (2.58) debt by monotone integration.
* **Bradley reduction (FY §2.6.1(vi), cited Bradley Thms 4.1–4.2)** — for stationary
  Markov chains the process coefficients collapse to the two-marginal coefficients of
  `(X_0, X_n)`; DEBT.

**Normalization warning (for the closure session).** `tvDist` is the sup-over-events
distance `sup_B |P(B) − Q(B)|`; the book's `‖·‖_TV` is twice that. FY's (2.58) is
stated for the conditional form of β, which in the sup-over-events normalization reads
`β(n) = ∫ tvDist (κⁿ x) F dF(x)` with **no factor 2** — verify this calibration against
the finite-partition definition of `betaMixCoeff` before proving anything downstream
of the debt.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.6.1,
eqs. (2.58)–(2.59) (p. 70). (`FY §2.6.1 (2.58)–(2.59)`.)

**Bibliographic comments.** The identity (2.58) is Yu. A. Davydov, *Mixing conditions
for Markov chains* (Theory Probab. Appl. 1973); the reduction of mixing coefficients to
two marginals is R. C. Bradley, *Introduction to Strong Mixing Conditions*, Thms 4.1
and 4.2 (vol. 1); the geometric-ergodicity route to β-mixing is standard from
Nummelin–Tuominen and Meyn–Tweedie ch. 16.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology ENNReal

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **Markov representation** hypothesis tying a real-valued process to a kernel:
the conditional law of `X_{t+n}` given the past through time `t` is `κⁿ(X_t, ·)`,
expressed through conditional expectations of indicators. -/
def IsMarkovOf (X : ℤ → Ω → ℝ) (κ : ProbabilityTheory.Kernel ℝ ℝ) (μ : Measure Ω) :
    Prop :=
  ∀ (t : ℤ) (n : ℕ) (B : Set ℝ), MeasurableSet B →
    (μ[fun ω => (B.indicator (fun _ => (1 : ℝ)) (X (t + n) ω)) | sigmaLE X t])
      =ᵐ[μ] fun ω => (((κ ^ n) (X t ω)) B).toReal

/-- **DEBT (Davydov 1973; FY eq. (2.58))**: for a strictly stationary Markov process
with kernel `κ` and time-`0` marginal `F = μ ∘ X_0⁻¹`,
`β(n) = ∫ tvDist (κⁿ x) F dF(x)` (sup-over-events normalization — see the module
docstring's calibration warning). -/
theorem betaCoeff_eq_integral_tvDist_debt [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStrictlyStationary X μ)
    {κ : ProbabilityTheory.Kernel ℝ ℝ} [ProbabilityTheory.IsMarkovKernel κ]
    -- USER-INPUT: Markov representation; FY §2.6.1(vi) setting
    (hmarkov : IsMarkovOf X κ μ) (n : ℕ) :
    betaCoeff X μ n
      = (∫⁻ x, StatLean.Minimaxity.tvDist ((κ ^ n) x) (μ.map (X 0))
          ∂(μ.map (X 0))).toReal := by
  sorry

/-- **FY eq. (2.59), derived from the (2.58) debt**: a pointwise geometric envelope
`tvDist (κⁿ x) F ≤ A(x) ρⁿ` with `A` integrable gives `β(n) ≤ ρⁿ ∫ A dF`; in
particular the process is (exponentially) β-mixing. -/
theorem isBetaMixing_of_geometric_envelope [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStrictlyStationary X μ)
    {κ : ProbabilityTheory.Kernel ℝ ℝ} [ProbabilityTheory.IsMarkovKernel κ]
    (hmarkov : IsMarkovOf X κ μ)
    {A : ℝ → ℝ} (hA : Measurable A) (hA0 : ∀ x, 0 ≤ A x)
    (hAint : Integrable A (μ.map (X 0)))
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    -- USER-INPUT: geometric TV envelope; FY eq. (2.59)
    (henv : ∀ (x : ℝ) (n : ℕ),
      StatLean.Minimaxity.tvDist ((κ ^ n) x) (μ.map (X 0))
        ≤ ENNReal.ofReal (A x * ρ ^ n)) :
    (∀ n : ℕ, betaCoeff X μ n ≤ (∫ x, A x ∂(μ.map (X 0))) * ρ ^ n) ∧
      IsBetaMixing X μ := by
  sorry

/-- **DEBT (Bradley Thms 4.1–4.2; FY §2.6.1(vi))**: for a strictly stationary Markov
process the α-coefficient collapses to the two-marginal coefficient of `(X_0, X_n)`:
`α(σ{X_s : s ≤ 0}, σ{X_s : s ≥ n}) = α(σ(X_0), σ(X_n))`. (Same statement holds for
β, ρ, φ, ψ; α is the consumed one.) -/
theorem alphaCoeff_eq_two_marginal_debt [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ} (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStrictlyStationary X μ)
    {κ : ProbabilityTheory.Kernel ℝ ℝ} [ProbabilityTheory.IsMarkovKernel κ]
    (hmarkov : IsMarkovOf X κ μ) (n : ℕ) :
    alphaCoeff X μ n
      = alphaMixCoeff μ (MeasurableSpace.comap (X 0) inferInstance)
          (MeasurableSpace.comap (X n) inferInstance) := by
  sorry

end StatLean.TimeSeries
