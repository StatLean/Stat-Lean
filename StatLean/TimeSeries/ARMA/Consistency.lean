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

section CompositeFilter

/-! ### The composite filter `c = π(θ) ∗ ψ(θ₀)`

The inversion coefficients `π(b, a)` are the transfer coefficients of the *reversed*
parameter pair: `arPoly b = maPoly (−b)` and `maPoly a = arPoly (−a)` (the sign
conventions of `arPoly`/`maPoly` differ by exactly the sign of the coefficients), so
`armaPi b a = armaPsi (−a) (−b)` and the whole `ARMAExistence` analytic layer
(geometric decay in particular) applies verbatim to `π`. -/

private lemma coeff_arPoly_zero' {p : ℕ} (b : Fin p → ℝ) : (arPoly b).coeff 0 = 1 := by
  simp [arPoly, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]

private lemma coeff_maPoly_zero' {q : ℕ} (a : Fin q → ℝ) : (maPoly a).coeff 0 = 1 := by
  simp [maPoly, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]

/-- The AR polynomial of the negated coefficients is the MA polynomial. -/
private lemma arPoly_neg {q : ℕ} (a : Fin q → ℝ) : arPoly (fun j => -a j) = maPoly a := by
  simp [arPoly, maPoly, sub_eq_add_neg]

/-- The MA polynomial of the negated coefficients is the AR polynomial. -/
private lemma maPoly_neg {p : ℕ} (b : Fin p → ℝ) : maPoly (fun i => -b i) = arPoly b := by
  simp [arPoly, maPoly, sub_eq_add_neg]

/-- The inversion coefficients are the transfer coefficients of the reversed pair. -/
private lemma armaPi_eq_armaPsi {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) (n : ℕ) :
    armaPi b a n = armaPsi (fun j => -a j) (fun i => -b i) n := by
  rw [armaPi, armaPsi, maPoly_neg, arPoly_neg]

private lemma armaPi_zero {p q : ℕ} (b : Fin p → ℝ) (a : Fin q → ℝ) :
    armaPi b a 0 = 1 := by
  rw [armaPi_eq_armaPsi, armaPsi_zero]

/-- **Geometric decay of the inversion coefficients** on the constraint set (the
`ψ`-statement of `ARMAExistence` read through `armaPi_eq_armaPsi`). -/
private lemma exists_geometric_bound_armaPi {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hB : ARMAInvertibleParams b a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ n, |armaPi b a n| ≤ C * r ^ n := by
  have hroot : NoRootClosedDisc (fun j => -a j) := by
    intro z hz
    rw [arPoly_neg]
    exact hB.2 z hz
  obtain ⟨C, hC, r, hr0, hr1, hbnd⟩ := exists_geometric_bound_armaPsi (fun i => -b i) hroot
  exact ⟨C, hC, r, hr0, hr1, fun n => by rw [armaPi_eq_armaPsi]; exact hbnd n⟩

/-- A single pair `(C, r)` dominating both filters of the composite. -/
private lemma exists_common_geometric_bound {p q : ℕ} {b0 b : Fin p → ℝ} {a0 a : Fin q → ℝ}
    (hB0 : ARMAInvertibleParams b0 a0) (hB : ARMAInvertibleParams b a) :
    ∃ C r : ℝ, 1 ≤ C ∧ 0 ≤ r ∧ r < 1 ∧
      (∀ n, |armaPi b a n| ≤ C * r ^ n) ∧ (∀ n, |armaPsi b0 a0 n| ≤ C * r ^ n) := by
  obtain ⟨C₁, hC₁, r₁, hr₁0, hr₁1, hb₁⟩ := exists_geometric_bound_armaPi hB
  obtain ⟨C₂, hC₂, r₂, hr₂0, hr₂1, hb₂⟩ := exists_geometric_bound_armaPsi a0 hB0.1
  refine ⟨max 1 (max C₁ C₂), max r₁ r₂, le_max_left _ _, le_trans hr₁0 (le_max_left _ _),
    max_lt hr₁1 hr₂1, fun n => ?_, fun n => ?_⟩
  · refine (hb₁ n).trans (mul_le_mul (le_trans (le_max_left _ _) (le_max_right _ _))
      (pow_le_pow_left₀ hr₁0 (le_max_left _ _) n) (by positivity) ?_)
    exact le_trans zero_le_one (le_max_left _ _)
  · refine (hb₂ n).trans (mul_le_mul (le_trans (le_max_right _ _) (le_max_right _ _))
      (pow_le_pow_left₀ hr₂0 (le_max_right _ _) n) (by positivity) ?_)
    exact le_trans zero_le_one (le_max_left _ _)

/-- The composite filter coefficients `c_n = Σ_{k ≤ n} π_k(θ) ψ_{n−k}(θ₀)`. -/
private noncomputable def contrastCoeff {p q : ℕ} (b0 : Fin p → ℝ) (a0 : Fin q → ℝ)
    (b : Fin p → ℝ) (a : Fin q → ℝ) (n : ℕ) : ℝ :=
  ∑ jk ∈ Finset.range (n + 1), armaPi b a jk * armaPsi b0 a0 (n - jk)

private lemma armaContrastVar_eq_tsum {p q : ℕ} (b0 : Fin p → ℝ) (a0 : Fin q → ℝ)
    (b : Fin p → ℝ) (a : Fin q → ℝ) :
    armaContrastVar b0 a0 b a = ∑' n : ℕ, contrastCoeff b0 a0 b a n ^ 2 := rfl

private lemma contrastCoeff_zero {p q : ℕ} (b0 : Fin p → ℝ) (a0 : Fin q → ℝ)
    (b : Fin p → ℝ) (a : Fin q → ℝ) : contrastCoeff b0 a0 b a 0 = 1 := by
  simp [contrastCoeff, armaPi_zero, armaPsi_zero]

/-- The composite filter inherits (a polynomially corrected) geometric decay. -/
private lemma abs_contrastCoeff_le {p q : ℕ} {b0 b : Fin p → ℝ} {a0 a : Fin q → ℝ}
    {C r : ℝ} (hC : 1 ≤ C) (hr0 : 0 ≤ r)
    (hπ : ∀ n, |armaPi b a n| ≤ C * r ^ n) (hψ : ∀ n, |armaPsi b0 a0 n| ≤ C * r ^ n)
    (n : ℕ) : |contrastCoeff b0 a0 b a n| ≤ C ^ 2 * ((n : ℝ) + 1) * r ^ n := by
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ k ∈ Finset.range (n + 1),
      |armaPi b a k * armaPsi b0 a0 (n - k)| ≤ C ^ 2 * r ^ n := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [abs_mul]
    calc |armaPi b a k| * |armaPsi b0 a0 (n - k)|
        ≤ (C * r ^ k) * (C * r ^ (n - k)) :=
          mul_le_mul (hπ k) (hψ _) (abs_nonneg _) (by positivity)
      _ = C ^ 2 * (r ^ k * r ^ (n - k)) := by ring
      _ = C ^ 2 * r ^ n := by rw [← pow_add]; congr 2; omega
  calc ∑ k ∈ Finset.range (n + 1), |armaPi b a k * armaPsi b0 a0 (n - k)|
      ≤ ∑ _k ∈ Finset.range (n + 1), C ^ 2 * r ^ n := Finset.sum_le_sum hterm
    _ = C ^ 2 * ((n : ℝ) + 1) * r ^ n := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- Summability of the squared composite filter (geometric with a quadratic
correction). -/
private lemma summable_sq_contrastCoeff {p q : ℕ} {b0 b : Fin p → ℝ} {a0 a : Fin q → ℝ}
    (hB0 : ARMAInvertibleParams b0 a0) (hB : ARMAInvertibleParams b a) :
    Summable fun n : ℕ => contrastCoeff b0 a0 b a n ^ 2 := by
  obtain ⟨C, r, hC, hr0, hr1, hπ, hψ⟩ := exists_common_geometric_bound hB0 hB
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hr2 : ‖r ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r)]
    nlinarith
  have hgeom : Summable fun n : ℕ => ((n : ℝ) + 1) ^ 2 * (r ^ 2) ^ n := by
    have h0 : Summable fun n : ℕ => (r ^ 2) ^ n := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 0 hr2
    have h1 : Summable fun n : ℕ => (n : ℝ) ^ 1 * (r ^ 2) ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr2
    have h2 : Summable fun n : ℕ => (n : ℝ) ^ 2 * (r ^ 2) ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hr2
    have := (h2.add (h1.mul_left 2)).add h0
    refine this.congr fun n => ?_
    ring
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun n => ?_)
    (hgeom.mul_left (C ^ 4))
  have habs := abs_contrastCoeff_le hC hr0 hπ hψ n
  have hnn : 0 ≤ C ^ 2 * ((n : ℝ) + 1) * r ^ n := by positivity
  calc contrastCoeff b0 a0 b a n ^ 2 = |contrastCoeff b0 a0 b a n| ^ 2 := (sq_abs _).symm
    _ ≤ (C ^ 2 * ((n : ℝ) + 1) * r ^ n) ^ 2 := by
        exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ = C ^ 4 * (((n : ℝ) + 1) ^ 2 * (r ^ 2) ^ n) := by
        rw [← pow_mul, mul_comm 2 n, pow_mul]
        ring

end CompositeFilter

/-- The composite filter has leading coefficient `1`, so the contrast variance is at
least `1`, with equality iff the working model matches the true transfer function. -/
theorem one_le_armaContrastVar {p q : ℕ} {b0 b : Fin p → ℝ} {a0 a : Fin q → ℝ}
    (hB0 : ARMAInvertibleParams b0 a0) (hB : ARMAInvertibleParams b a) :
    1 ≤ armaContrastVar b0 a0 b a := by
  have hsum := summable_sq_contrastCoeff hB0 hB
  have h0 : contrastCoeff b0 a0 b a 0 ^ 2 ≤ ∑' n : ℕ, contrastCoeff b0 a0 b a n ^ 2 :=
    hsum.le_tsum 0 fun n _ => sq_nonneg _
  rw [armaContrastVar_eq_tsum]
  rwa [contrastCoeff_zero, one_pow] at h0

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
