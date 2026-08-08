import StatLean.TimeSeries.ARMA.ScoreAnalysis

/-!
# Consistency of the ARMA Gaussian MLE (Hannan program, step 1)

The consistency half of the commissioned Hannan Theorem 3.2 proof: the profiled
Gaussian criterion `armaProfileCriterion` converges (uniformly on compact subsets of
the constraint set) to a deterministic contrast that is uniquely minimized at the true
parameter, so approximate minimizers converge in probability.

* `armaContrast` — the limit contrast `K(θ) = log σ²_θ` where `σ²_θ` is the one-step
  prediction variance of the true process under the working model θ (by the
  Kolmogorov–Szegő/innovations identity the criterion's log-det term vanishes in the
  limit: `T⁻¹ log det Γ_T(θ) → 0` on the constraint set);
* `armaContrast_uniqueMin` — identifiability: `K(θ) ≥ K(θ₀)` with equality iff the
  transfer functions agree; under coprime minimal orders, iff `θ = θ₀`;
* `logdet_armaToeplitz_vanishes` — the Szegő-type limit `T⁻¹ log det Γ_T(θ) → 0`
  (from the innovations recursion: `det Γ_T = ∏ ν_j` and `ν_j → σ²_∞ = 1` for the
  unit-variance model ACVF, geometric rate on the constraint set);
* `criterion_tendsto_contrast` — pointwise stochastic convergence of the profiled
  criterion (ergodic-type LLN for the quadratic form; the α-mixing route via the
  batch-C toolbox after Pham–Tran, or the direct L² route via MA(∞) truncation —
  proof plan in the lane prompt);
* `mle_consistent` — approximate minimizers over the constraint set converge in
  probability to `θ₀` (argmin-consistency wiring following the
  `StatLean/Bayesian` `ArgminConsistency` pattern; compactness supplied by
  restricting to a compact `𝓑`-subset containing `θ₀`, as Hannan does).

**Reference.** Hannan (1973) §2; Brockwell & Davis (1991) §10.8 (Props 10.8.1–10.8.3);
FY Theorem 3.2 cites both. (`Hannan 1973 / B&D §10.8`.)
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

/-- The **asymptotic one-step prediction variance** of the unit-variance true model
`θ₀ = (b₀, a₀)` filtered through the working model `θ = (b, a)`: in spectral terms
`σ²(θ; θ₀) = exp(∫ log(g_{θ₀}/g_θ)) · 1`-shaped; realized time-domain as
`Σ_j c_j²` where `c = π(θ) ∗ ψ(θ₀)` is the composite filter (the coefficients of
`(b(z)/a(z)) · (a₀(z)/b₀(z))`). -/
noncomputable def armaContrastVar {p q : ℕ} (b0 : Fin p → ℝ) (a0 : Fin q → ℝ)
    (b : Fin p → ℝ) (a : Fin q → ℝ) : ℝ :=
  ∑' n : ℕ, (∑ jk ∈ Finset.range (n + 1),
    armaPi b a jk * armaPsi b0 a0 (n - jk)) ^ 2

/-- The composite filter has leading coefficient `1`, so the contrast variance is at
least `1`, with equality iff the working model matches the true transfer function. -/
theorem one_le_armaContrastVar {p q : ℕ} {b0 b : Fin p → ℝ} {a0 a : Fin q → ℝ}
    (hB0 : ARMAInvertibleParams b0 a0) (hB : ARMAInvertibleParams b a) :
    1 ≤ armaContrastVar b0 a0 b a := by
  sorry

/-- **Identifiability**: contrast variance `= 1` iff the transfer functions agree,
i.e. `b(z) a₀(z) = b₀(z) a(z)`; under coprimality and equal orders, iff the
parameters agree. -/
theorem armaContrastVar_eq_one_iff {p q : ℕ} {b0 b : Fin p → ℝ} {a0 a : Fin q → ℝ}
    (hB0 : ARMAInvertibleParams b0 a0) (hB : ARMAInvertibleParams b a)
    -- USER-INPUT: coprime minimal true orders; Hannan 1973
    (hcop : IsCoprime (arPoly b0) (maPoly a0)) :
    armaContrastVar b0 a0 b a = 1 ↔ b = b0 ∧ a = a0 := by
  sorry

/-- **Szegő-type limit**: on the constraint set, `T⁻¹ log det Γ_T(b, a) → 0`
(unit-variance model; `det Γ_T = ∏_{j<T} ν_j` with innovations variances `ν_j ↓ 1`
geometrically). -/
theorem logdet_armaToeplitz_vanishes {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hB : ARMAInvertibleParams b a) :
    Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * Real.log (armaToeplitz b a T).det)
      atTop (𝓝 0) := by
  sorry

section Process

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Pointwise LLN for the profiled criterion**: at each fixed `θ` in the constraint
set, `armaProfileCriterion θ (data_T) →p log(σ² · armaContrastVar θ₀ θ)` under the
true ARMA law. -/
theorem criterion_tendsto_contrast [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 b : Fin p → ℝ} {a0 a : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hB0 : ARMAInvertibleParams b0 a0) (hB : ARMAInvertibleParams b a)
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ)
    (hmeas : ∀ t, Measurable (X t)) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun T : ℕ => (μ {ω | δ ≤
        |armaProfileCriterion b a (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
          - Real.log (σ2 * armaContrastVar b0 a0 b a)|}).toReal)
      atTop (𝓝 0) := by
  sorry

/-- **Consistency of approximate MLE sequences** over a compact identifiable
neighbourhood: any measurable approximate-minimizer sequence of the profiled
criterion over a compact `K ⊆ 𝓑` containing `θ₀` in its interior converges in
probability to `θ₀`. -/
theorem mle_consistent [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 : Fin p → ℝ} {a0 : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hB0 : ARMAInvertibleParams b0 a0)
    (hcop : IsCoprime (arPoly b0) (maPoly a0))
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ)
    (hmeas : ∀ t, Measurable (X t))
    {K : Set ((Fin p → ℝ) × (Fin q → ℝ))}
    -- USER-INPUT: compact identifiable search region containing the truth; Hannan §2
    (hK : IsCompact K) (hKB : ∀ ba ∈ K, ARMAInvertibleParams ba.1 ba.2)
    (hK0 : (b0, a0) ∈ K)
    (θ : (T : ℕ) → Ω → (Fin p → ℝ) × (Fin q → ℝ))
    (hθmeas : ∀ T, Measurable (θ T))
    {δT : ℕ → ℝ} (hδT : Tendsto δT atTop (𝓝 0)) (hδT0 : ∀ T, 0 ≤ δT T)
    -- USER-INPUT: approximate minimization over K; FY eq. (3.10) (argmax corrected)
    (hargmin : ∀ (T : ℕ) (ω : Ω), θ T ω ∈ K ∧ ∀ ba ∈ K,
      armaProfileCriterion (θ T ω).1 (θ T ω).2
          (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
        ≤ armaProfileCriterion ba.1 ba.2
            (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) + δT T)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun T : ℕ =>
        (μ {ω | δ ≤ dist (θ T ω) (b0, a0)}).toReal) atTop (𝓝 0) := by
  sorry

end Process

end StatLean.TimeSeries
