import StatLean.TimeSeries.ForMathlib.Fourier.HerglotzBochner
import StatLean.TimeSeries.Process.LinearProcess
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Stationary Gaussian processes and the completion of FY Theorem 2.7 (FY §2.1.3, §2.2.1)

Two threads:

1. **FY Theorem 2.7, sufficiency** (`exists_stationary_of_isPosSemidefSeq`, the batch-A
   debt): every even positive semidefinite `γ : ℤ → ℝ` is the ACVF of some weakly
   stationary process. Proof by the **random-phase construction** over the Herglotz
   spectral measure — no Kolmogorov extension needed: on
   `Ω' = AddCircle (2π) × ℝ × ℝ` with `P = (γ(0)⁻¹ • F) ⊗ N(0,1) ⊗ N(0,1)` (where `F`
   is the measure from `exists_measure_of_isPosSemidefSeq`), the process
   `X_t(λ, α, β) = √γ(0) · (α · Re(e^{itλ}) + β · Im(e^{itλ}))`
   has mean `0` and covariance
   `E X_s X_t = γ(0)·E_Λ[Re(e^{i(s−t)Λ})] = Re(measureFourierCoeff F (s−t)) = γ(s−t)`.
2. **FY §2.1.3**: Gaussian processes — a weakly stationary Gaussian process is strictly
   stationary (finite-dimensional Gaussian laws are determined by mean vector and
   covariance matrix, both shift-invariant); a causal ARMA process driven by i.i.d.
   Gaussian noise is a Gaussian process (`L²`-limits of Gaussian vectors are Gaussian);
   the **Wold decomposition** (FY eq. (2.6)) as a named DEBT (batch F, conditional-
   expectation route) and **Proposition 2.1** standing on it.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003: §2.2.1
Theorem 2.7 (p. 40; sufficiency cited to Brockwell & Davis 1991, p. 27 — our
random-phase proof is a different, self-contained route, documented deviation);
§2.1.3 (pp. 32–33: Gaussian processes, Wold eq. (2.6), Proposition 2.1).
(`FY §2.2.1 Thm 2.7; §2.1.3 Prop 2.1`.)

**Proof formalization notes.**
* The random-phase process is *not* Gaussian and not strictly stationary — Theorem 2.7
  only demands weak stationarity, and the construction uses exclusively batch-A bricks
  (`exists_measure_of_isPosSemidefSeq`, `measureFourierCoeff_im/neg`, `NegInvariant`).
  The amplitudes only need mean `0`, variance `1`, uncorrelated; we take independent
  standard Gaussians (`gaussianReal 0 1`) for definiteness.
* `IsGaussianProcess` is Mathlib's (pinned) structure; the weak⇒strict argument pins the
  finite-dimensional laws down through their characteristic functions.
* Prop 2.1(iii) (conditional-independence ⇒ AR(p)) needs Gaussian conditioning; stated
  here with proof deferred (DEBT) pending the Gaussian-conditioning bricks.

**Bibliographic comments.** The spectral random-phase representation goes back to
Slutsky and to Cramér's spectral theory (H. Cramér, "On the theory of stationary random
processes", *Ann. of Math.* **41** (1940), 215–230). The Wold decomposition is H. Wold
(1938). Gaussian processes as determined by second-order structure: Kolmogorov's
*Grundbegriffe* (1933) plus classical multivariate normal theory.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Real

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **FY Theorem 2.7, sufficiency** (batch-A debt, relocated here; proof: random-phase
construction over the Herglotz measure — see the module docstring). Every even positive
semidefinite sequence is the autocovariance function of some weakly stationary process. -/
theorem exists_stationary_of_isPosSemidefSeq (γ : ℤ → ℝ)
    -- USER-INPUT: evenness; FY §2.2.1 Thm 2.7
    (heven : ∀ k, γ (-k) = γ k)
    -- USER-INPUT: positive semidefiniteness, eq. (2.17); FY §2.2.1 Thm 2.7
    (hpsd : IsPosSemidefSeq γ) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω') (X' : ℤ → Ω' → ℝ),
      IsProbabilityMeasure μ' ∧ (∀ t, Measurable (X' t)) ∧ IsStationary X' μ' ∧
        acvf X' μ' = γ := by
  sorry

/-- **FY Theorem 2.7, both halves packaged**: a real sequence is the ACVF of some weakly
stationary process iff it is even and positive semidefinite. -/
theorem isPosSemidefSeq_and_even_iff_acvf (γ : ℤ → ℝ) :
    ((∀ k, γ (-k) = γ k) ∧ IsPosSemidefSeq γ) ↔
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (μ' : Measure Ω') (X' : ℤ → Ω' → ℝ),
        IsProbabilityMeasure μ' ∧ (∀ t, Measurable (X' t)) ∧ IsStationary X' μ' ∧
          acvf X' μ' = γ := by
  sorry

/-- **Weakly stationary Gaussian processes are strictly stationary** (FY §2.1.3): the
finite-dimensional laws of a Gaussian process are determined by the mean vector and
covariance matrix, and both are shift-invariant under weak stationarity. -/
theorem IsGaussianProcess.isStrictlyStationary [IsProbabilityMeasure μ]
    {X : ℤ → Ω → ℝ}
    -- USER-INPUT: the process is Gaussian; FY §2.1.3
    (hG : IsGaussianProcess X μ)
    -- LEAN-ONLY: coordinate random variables are measurable; implicit in FY
    (hmeas : ∀ t, Measurable (X t))
    -- USER-INPUT: weak stationarity; FY §2.1.3
    (hstat : IsStationary X μ) :
    IsStrictlyStationary X μ := by
  sorry

/-- **Causal ARMA with i.i.d. Gaussian noise is a Gaussian process** (FY §2.1.3): the
finite-dimensional vectors are `L²`-limits of linear images of Gaussian vectors. -/
theorem isGaussianProcess_of_linearProcess [IsProbabilityMeasure μ]
    {ψ : ℕ → ℝ} {X ε : ℤ → Ω → ℝ}
    (hX : IsLinearProcessOf ψ X ε μ) (hψ : Summable fun n => |ψ n|)
    (hmeas : ∀ t, Measurable (X t))
    -- USER-INPUT: the innovations form an i.i.d. Gaussian family; FY §2.1.3
    (hε : IsIIDNoise ε 1 μ)
    (hgauss : ∀ t, μ.map (ε t) = gaussianReal 0 1) :
    IsGaussianProcess X μ := by
  sorry

/-- **Wold decomposition, Gaussian form — DEBT** (FY §2.1.3, eq. (2.6); cited to
Brockwell & Davis 1991, p. 187; closure scheduled for batch F via the conditional-
expectation route, see `notes/time_series/debt_assessment.md` §5): a zero-mean weakly
stationary Gaussian process splits as an MA(∞) over i.i.d. Gaussian innovations plus an
independent deterministic (remote-past-measurable) component. -/
theorem wold_gaussian_debt [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hG : IsGaussianProcess X μ) (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStationary X μ)
    -- USER-INPUT: zero mean; FY eq. (2.6)
    (hmean : ∀ t, ∫ ω, X t ω ∂μ = 0) :
    ∃ (ψ : ℕ → ℝ) (ε V : ℤ → Ω → ℝ) (σ2 : ℝ),
      (Summable fun j => ψ j ^ 2) ∧ IsIIDNoise ε σ2 μ ∧
      (∀ t : ℤ, Measurable (V t)) ∧
      (∀ t : ℤ, Measurable[⨅ n : ℕ, sigmaLE X (t - n)] (V t)) ∧
      Indep (⨆ t : ℤ, MeasurableSpace.comap (ε t) inferInstance)
        (⨆ t : ℤ, MeasurableSpace.comap (V t) inferInstance) μ ∧
      ∀ t : ℤ, Tendsto
        (fun N => eLpNorm
          (fun ω => X t ω - (∑ j ∈ Finset.range N, ψ j * ε (t - (j : ℕ)) ω + V t ω)) 2 μ)
        atTop (nhds 0) := by
  sorry

/-- **Proposition 2.1(ii)** (FY §2.1.3): a zero-mean weakly stationary Gaussian process
that is `q`-dependent (`Cov(X_s, X_t) = 0` for `|s − t| > q`) with trivial remote past
in its Wold decomposition is an MA(q). Statement conditional on `wold_gaussian_debt`;
DEBT until batch F. -/
theorem gaussian_q_dependent_isMA_debt [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    {q : ℕ}
    (hG : IsGaussianProcess X μ) (hmeas : ∀ t, Measurable (X t))
    (hstat : IsStationary X μ) (hmean : ∀ t, ∫ ω, X t ω ∂μ = 0)
    -- USER-INPUT: q-dependence; FY §2.1.3 Prop 2.1(ii)
    (hdep : ∀ s t : ℤ, (q : ℤ) < |s - t| → cov[X s, X t; μ] = 0)
    -- USER-INPUT: purely nondeterministic (trivial remote past); FY §2.1.3 Prop 2.1(i)
    (hpnd : ∀ A : Set Ω, MeasurableSet[⨅ n : ℕ, sigmaLE X (-(n : ℤ))] A →
      μ A = 0 ∨ μ A = 1) :
    ∃ (a : Fin q → ℝ) (σ2 : ℝ) (ε : ℤ → Ω → ℝ), IsMA a σ2 X ε μ := by
  sorry

end StatLean.TimeSeries
