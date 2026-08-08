import StatLean.TimeSeries.ARMA.ScoreAnalysis
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef

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
  simp [arPoly, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow]

private lemma coeff_maPoly_zero' {q : ℕ} (a : Fin q → ℝ) : (maPoly a).coeff 0 = 1 := by
  simp [maPoly, Polynomial.finset_sum_coeff, Polynomial.coeff_X_pow]

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

/-- The composite filter is the coefficient sequence of the composite transfer function
`(b(z)/a(z)) · (a₀(z)/b₀(z))`. -/
private lemma contrastCoeff_eq_coeff {p q : ℕ} (b0 b : Fin p → ℝ) (a0 a : Fin q → ℝ) (n : ℕ) :
    contrastCoeff b0 a0 b a n
      = PowerSeries.coeff n
          ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ) *
              ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) *
            ((((maPoly a0 : Polynomial ℝ) : PowerSeries ℝ)) *
              ((((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ)))⁻¹)) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rfl

/-- The contrast variance is `1` exactly when the composite filter is `δ₀`. -/
private lemma armaContrastVar_eq_one_iff_coeff {p q : ℕ} {b0 b : Fin p → ℝ} {a0 a : Fin q → ℝ}
    (hB0 : ARMAInvertibleParams b0 a0) (hB : ARMAInvertibleParams b a) :
    armaContrastVar b0 a0 b a = 1 ↔ ∀ n : ℕ, n ≠ 0 → contrastCoeff b0 a0 b a n = 0 := by
  have hsum := summable_sq_contrastCoeff hB0 hB
  constructor
  · intro hvar n hn
    have hpair := hsum.sum_le_tsum ({0, n} : Finset ℕ) (fun i _ => sq_nonneg _)
    rw [Finset.sum_pair (Ne.symm hn), ← armaContrastVar_eq_tsum, hvar,
      contrastCoeff_zero, one_pow] at hpair
    have hle : contrastCoeff b0 a0 b a n ^ 2 ≤ 0 := by linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm hle (sq_nonneg _))
  · intro hzero
    rw [armaContrastVar_eq_tsum]
    have h : ∀ n : ℕ, contrastCoeff b0 a0 b a n ^ 2 = if n = 0 then 1 else 0 := by
      intro n
      rcases eq_or_ne n 0 with rfl | hn
      · rw [contrastCoeff_zero, if_pos rfl, one_pow]
      · rw [hzero n hn, if_neg hn]
        ring
    rw [tsum_congr h]
    exact tsum_ite_eq (0 : ℕ) (fun _ : ℕ => (1 : ℝ))

/-- **Identifiability, honest form** (this is what the contrast variance sees): the
contrast variance equals `1` exactly when the two transfer functions agree, i.e.
`b(z) a₀(z) = b₀(z) a(z)` as polynomials. Recovering `(b, a) = (b₀, a₀)` from this needs
the *working* pair to be coprime as well — see `armaContrastVar_eq_one_not_identifiable`. -/
private lemma armaContrastVar_eq_one_iff_transfer {p q : ℕ} {b0 b : Fin p → ℝ}
    {a0 a : Fin q → ℝ} (hB0 : ARMAInvertibleParams b0 a0) (hB : ARMAInvertibleParams b a) :
    armaContrastVar b0 a0 b a = 1 ↔ arPoly b * maPoly a0 = arPoly b0 * maPoly a := by
  have hAne : PowerSeries.constantCoeff (((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, coeff_maPoly_zero']
    exact one_ne_zero
  have hB0ne : PowerSeries.constantCoeff (((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ)) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, coeff_arPoly_zero']
    exact one_ne_zero
  have hcoeff : armaContrastVar b0 a0 b a = 1 ↔
      (((arPoly b : Polynomial ℝ) : PowerSeries ℝ) *
          ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) *
        ((((maPoly a0 : Polynomial ℝ) : PowerSeries ℝ)) *
          ((((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) = 1 := by
    rw [armaContrastVar_eq_one_iff_coeff hB0 hB, PowerSeries.ext_iff]
    constructor
    · intro h n
      rw [← contrastCoeff_eq_coeff, PowerSeries.coeff_one]
      rcases eq_or_ne n 0 with rfl | hn
      · rw [contrastCoeff_zero, if_pos rfl]
      · rw [h n hn, if_neg hn]
    · intro h n hn
      have := h n
      rw [← contrastCoeff_eq_coeff, PowerSeries.coeff_one, if_neg hn] at this
      exact this
  rw [hcoeff]
  constructor
  · intro h
    have h2 : ((arPoly b : Polynomial ℝ) : PowerSeries ℝ) *
        ((maPoly a0 : Polynomial ℝ) : PowerSeries ℝ)
        = ((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ) *
            ((maPoly a : Polynomial ℝ) : PowerSeries ℝ) := by
      have hmul := congrArg (fun S => S * ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) *
        (((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ)))) h
      simp only [one_mul] at hmul
      rw [show ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ)) *
            ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) *
          ((((maPoly a0 : Polynomial ℝ) : PowerSeries ℝ)) *
            ((((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) *
          ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) *
            (((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ)))
          = ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ)) *
              (((maPoly a0 : Polynomial ℝ) : PowerSeries ℝ))) *
            (((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) *
                ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) *
              (((((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ))) *
                ((((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ)))⁻¹)) from by ring,
        PowerSeries.mul_inv_cancel _ hAne, PowerSeries.mul_inv_cancel _ hB0ne, mul_one,
        mul_one] at hmul
      rw [hmul]
      ring
    refine (Polynomial.coe_inj (R := ℝ)).1 ?_
    rw [Polynomial.coe_mul, Polynomial.coe_mul]
    exact h2
  · intro h
    have h2 : ((arPoly b : Polynomial ℝ) : PowerSeries ℝ) *
        ((maPoly a0 : Polynomial ℝ) : PowerSeries ℝ)
        = ((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ) *
            ((maPoly a : Polynomial ℝ) : PowerSeries ℝ) := by
      rw [← Polynomial.coe_mul, ← Polynomial.coe_mul, h]
    calc ((arPoly b : Polynomial ℝ) : PowerSeries ℝ) *
          ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))⁻¹ *
          ((((maPoly a0 : Polynomial ℝ) : PowerSeries ℝ)) *
            ((((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ)))⁻¹)
        = (((arPoly b : Polynomial ℝ) : PowerSeries ℝ) *
            ((maPoly a0 : Polynomial ℝ) : PowerSeries ℝ)) *
          (((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))⁻¹ *
            ((((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) := by ring
      _ = (((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ) *
            ((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) *
          (((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))⁻¹ *
            ((((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) := by rw [h2]
      _ = ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) *
            ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) *
          ((((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ)) *
            ((((arPoly b0 : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) := by ring
      _ = 1 := by
          rw [PowerSeries.mul_inv_cancel _ hAne, PowerSeries.mul_inv_cancel _ hB0ne, mul_one]

/-- **Falsity witness for the frozen forward implication of `armaContrastVar_eq_one_iff`.**

With `p = q = 1`, true parameters `b₀ = a₀ = 0` (so `b₀(z) = a₀(z) = 1`: white noise, and
`IsCoprime 1 1` holds) and working parameters `b = 1/2`, `a = −1/2`, the working transfer
function is `b(z)/a(z) = (1 − z/2)/(1 − z/2) = 1`: the working model is a *non-minimal*
representation of the same white noise. Both parameter pairs lie in `𝓑`, the contrast
variance is `1`, yet `b ≠ b₀`. Identifiability of the *parameters* needs coprimality of
the **working** pair too (or a search region of minimal representations); the contrast
variance only ever sees the transfer function — `armaContrastVar_eq_one_iff_transfer`. -/
private lemma arPoly_witness_zero : arPoly (fun _ : Fin 1 => (0 : ℝ)) = 1 := by simp [arPoly]

private lemma maPoly_witness_zero : maPoly (fun _ : Fin 1 => (0 : ℝ)) = 1 := by simp [maPoly]

private lemma maPoly_witness_neg :
    maPoly (fun _ : Fin 1 => (-(1 / 2) : ℝ)) = arPoly (fun _ : Fin 1 => (1 / 2 : ℝ)) :=
  maPoly_neg (fun _ : Fin 1 => (1 / 2 : ℝ))

private lemma noRoot_witness : NoRootClosedDisc (fun _ : Fin 1 => (1 / 2 : ℝ)) := by
  intro z hz hzero
  have hev : Polynomial.aeval z (arPoly (fun _ : Fin 1 => (1 / 2 : ℝ))) = 1 - z / 2 := by
    simp [arPoly]
    ring
  rw [hev] at hzero
  have hz2 : z = 2 := by linear_combination -2 * hzero
  rw [hz2] at hz
  norm_num at hz

private lemma invertible_witness_zero :
    ARMAInvertibleParams (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ)) := by
  constructor
  · intro z _
    rw [arPoly_witness_zero]
    simp
  · intro z _
    rw [maPoly_witness_zero]
    simp

private lemma invertible_witness_half :
    ARMAInvertibleParams (fun _ : Fin 1 => (1 / 2 : ℝ)) (fun _ : Fin 1 => (-(1 / 2) : ℝ)) := by
  refine ⟨noRoot_witness, fun z hz => ?_⟩
  rw [maPoly_witness_neg]
  exact noRoot_witness z hz

private theorem armaContrastVar_eq_one_not_identifiable :
    ∃ (b0 b : Fin 1 → ℝ) (a0 a : Fin 1 → ℝ),
      ARMAInvertibleParams b0 a0 ∧ ARMAInvertibleParams b a ∧
        IsCoprime (arPoly b0) (maPoly a0) ∧ armaContrastVar b0 a0 b a = 1 ∧ b ≠ b0 := by
  refine ⟨fun _ => 0, fun _ => 1 / 2, fun _ => 0, fun _ => -(1 / 2),
    invertible_witness_zero, invertible_witness_half, ?_, ?_, ?_⟩
  · rw [arPoly_witness_zero, maPoly_witness_zero]
    exact isCoprime_one_left
  · refine (armaContrastVar_eq_one_iff_transfer invertible_witness_zero
      invertible_witness_half).2 ?_
    rw [arPoly_witness_zero, maPoly_witness_zero, maPoly_witness_neg, mul_one, one_mul]
  · intro h
    have := congrFun h 0
    norm_num at this

/-- The two witness pairs have the **same transfer coefficients** (both are white noise:
`(1 − z/2)/(1 − z/2) = 1 = 1/1`). -/
private lemma armaPsi_witness_eq :
    armaPsi (fun _ : Fin 1 => (1 / 2 : ℝ)) (fun _ : Fin 1 => (-(1 / 2) : ℝ))
      = armaPsi (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ)) := by
  have hne : PowerSeries.constantCoeff
      (((arPoly (fun _ : Fin 1 => (1 / 2 : ℝ)) : Polynomial ℝ) : PowerSeries ℝ)) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, coeff_arPoly_zero']
    exact one_ne_zero
  funext n
  rw [armaPsi, armaPsi, maPoly_witness_neg, arPoly_witness_zero, maPoly_witness_zero,
    PowerSeries.mul_inv_cancel _ hne]
  simp

/-- **Falsity witness for `mle_consistent` as frozen**: two *distinct* parameter points of
the constraint set, the first one coprime (a legitimate `θ₀`), at which the profiled
criterion is identically equal *for every sample of every length*. Taking
`K = {θ₀, θ₁}` (finite, hence compact, and containing `θ₀`) and the constant sequence
`θ T ω = θ₁` satisfies every hypothesis of `mle_consistent` — including `hargmin` with
`δT = 0` — while `dist (θ T ω) θ₀` is a fixed positive number. -/
private theorem mle_consistent_not_identifiable :
    ∃ θ0 θ1 : (Fin 1 → ℝ) × (Fin 1 → ℝ),
      ARMAInvertibleParams θ0.1 θ0.2 ∧ ARMAInvertibleParams θ1.1 θ1.2 ∧
        IsCoprime (arPoly θ0.1) (maPoly θ0.2) ∧ θ0 ≠ θ1 ∧
        ∀ (T : ℕ) (x : Fin T → ℝ),
          armaProfileCriterion θ1.1 θ1.2 x = armaProfileCriterion θ0.1 θ0.2 x := by
  refine ⟨(fun _ => 0, fun _ => 0), (fun _ => 1 / 2, fun _ => -(1 / 2)),
    invertible_witness_zero, invertible_witness_half, ?_, ?_, ?_⟩
  · rw [arPoly_witness_zero, maPoly_witness_zero]
    exact isCoprime_one_left
  · intro h
    have := congrFun (congrArg Prod.fst h) 0
    norm_num at this
  · intro T x
    have hacvf : armaACVF (fun _ : Fin 1 => (1 / 2 : ℝ)) (fun _ : Fin 1 => (-(1 / 2) : ℝ))
        = armaACVF (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ)) := by
      funext k
      simp only [armaACVF, armaPsi_witness_eq]
    have hT : armaToeplitz (fun _ : Fin 1 => (1 / 2 : ℝ)) (fun _ : Fin 1 => (-(1 / 2) : ℝ)) T
        = armaToeplitz (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ)) T := by
      ext i j
      simp only [armaToeplitz, Matrix.of_apply, hacvf]
    simp only [armaProfileCriterion, armaProfileS, hT]

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
  constructor
  · -- **FALSE AS FROZEN.** The hypotheses constrain only the *true* pair to be coprime,
    -- so a non-minimal working pair with the same transfer function is a counterexample:
    -- `armaContrastVar_eq_one_not_identifiable` exhibits (in Lean) `p = q = 1`,
    -- `b₀ = a₀ = 0`, `b = 1/2`, `a = −1/2`, where both pairs are in `𝓑`,
    -- `IsCoprime (arPoly b₀) (maPoly a₀)` holds, the contrast variance is `1`, and
    -- `b ≠ b₀`. The provable statement is the transfer-function one,
    -- `armaContrastVar_eq_one_iff_transfer`:
    --   `armaContrastVar b₀ a₀ b a = 1 ↔ arPoly b * maPoly a₀ = arPoly b₀ * maPoly a`,
    -- which is PROVED above; the frozen conclusion follows from it only after adding
    -- `IsCoprime (arPoly b) (maPoly a)` (minimality of the *working* model) to the
    -- hypotheses. Repair the statement, do not attempt this branch.
    sorry
  · rintro ⟨rfl, rfl⟩
    exact (armaContrastVar_eq_one_iff_transfer hB0 hB).2 rfl

section Szego

/-! ### The Szegő-type limit `T⁻¹ log det Γ_T → 0`

The route avoids the innovations recursion entirely. With `ψ̃(m, s) = ψ_{m−s} 1{s ≤ m}`
the Cholesky-type kernel of the model ACVF (`Γ_{st} = Σ_m ψ̃(m,s) ψ̃(m,t)`) and
`π̃(i, k) = π_{k−i} 1{i ≤ k}` the (upper-triangular, unit-diagonal, determinant-one)
inversion matrix, the whitened matrix `N_T = Π_T Γ_T Π_Tᵀ` has entries
`N_{ij} = Σ_m u_i(m) u_j(m)` with `u_i(m) = Σ_{k<T} π̃(i,k) ψ̃(m,k)`. The convolution
identity `π ∗ ψ = δ` makes `u_i(m) = 1{i = m}` for every `m < T`, so

  `N_T = 1 + G_T`,  `G_{ij} = Σ_{m ≥ T} u_i(m) u_j(m)`,

with `G_T` positive semidefinite and — this is the whole point — of *bounded trace*:
`|u_i(m)| ≤ C²(T − i) r^{m−i}` gives `tr G_T ≤ C⁴ Σ_{d ≥ 1} d² r^{2d}/(1 − r²) =: K`
uniformly in `T`. Since `det Γ_T = det N_T = ∏(1 + λ_j(G_T))`,

  `0 ≤ log det Γ_T ≤ Σ_j λ_j(G_T) = tr G_T ≤ K`,

which is `O(1)`, not merely `O(T)`: dividing by `T` gives the limit. -/

open Matrix

variable {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}

/-- The **one-sided transfer kernel** `ψ̃(m, s) = ψ_{m−s} 1{s ≤ m}` (the lower-triangular
unit-diagonal Cholesky-type factor of the model ACVF). -/
private noncomputable def psiK (b : Fin p → ℝ) (a : Fin q → ℝ) (m s : ℕ) : ℝ :=
  if s ≤ m then armaPsi b a (m - s) else 0

/-- The **one-sided inversion kernel** `π̃(i, k) = π_{k−i} 1{i ≤ k}`. -/
private noncomputable def piK (b : Fin p → ℝ) (a : Fin q → ℝ) (i k : ℕ) : ℝ :=
  if i ≤ k then armaPi b a (k - i) else 0

private lemma psiK_eq_zero (b : Fin p → ℝ) (a : Fin q → ℝ) {m s : ℕ} (h : m < s) :
    psiK b a m s = 0 := by
  simp [psiK, Nat.not_le.2 h]

private lemma piK_eq_zero (b : Fin p → ℝ) (a : Fin q → ℝ) {i k : ℕ} (h : k < i) :
    piK b a i k = 0 := by
  simp [piK, Nat.not_le.2 h]

private lemma piK_self (b : Fin p → ℝ) (a : Fin q → ℝ) (i : ℕ) : piK b a i i = 1 := by
  simp [piK, armaPi_zero]

/-- **The convolution identity `π ∗ ψ = δ`** (the two power series are inverse). -/
private lemma armaPi_conv_armaPsi (b : Fin p → ℝ) (a : Fin q → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), armaPi b a k * armaPsi b a (n - k)
      = if n = 0 then 1 else 0 := by
  have hAne : PowerSeries.constantCoeff (((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, coeff_maPoly_zero']
    exact one_ne_zero
  have hBne : PowerSeries.constantCoeff (((arPoly b : Polynomial ℝ) : PowerSeries ℝ)) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, coeff_arPoly_zero']
    exact one_ne_zero
  have key : ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ)) *
        ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) *
      (((((maPoly a : Polynomial ℝ) : PowerSeries ℝ))) *
        ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) = 1 := by
    calc ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ)) *
          ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) *
        (((((maPoly a : Polynomial ℝ) : PowerSeries ℝ))) *
          ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ)))⁻¹)
        = ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)) *
            ((((maPoly a : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) *
          ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ)) *
            ((((arPoly b : Polynomial ℝ) : PowerSeries ℝ)))⁻¹) := by ring
      _ = 1 := by
          rw [PowerSeries.mul_inv_cancel _ hAne, PowerSeries.mul_inv_cancel _ hBne, mul_one]
  have hc := congrArg (PowerSeries.coeff n) key
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    PowerSeries.coeff_one] at hc
  exact hc

/-- The filtered kernel `u_i(m) = Σ_{k<T} π̃(i,k) ψ̃(m,k)`: the rows of `Π_T Ψ̃`. -/
private noncomputable def uSeq (b : Fin p → ℝ) (a : Fin q → ℝ) (T i m : ℕ) : ℝ :=
  ∑ k ∈ Finset.range T, piK b a i k * psiK b a m k

/-- **Whitening below the horizon**: for `m < T` the filtered kernel is `1{i = m}` —
this is the convolution identity `π ∗ ψ = δ`, and it is what makes `Π Γ Πᵀ − 1` a
*tail* Gram matrix. -/
private lemma uSeq_eq_of_lt (b : Fin p → ℝ) (a : Fin q → ℝ) {T i m : ℕ} (hm : m < T) :
    uSeq b a T i m = if i = m then 1 else 0 := by
  have hsub : Finset.range (m + 1) ⊆ Finset.range T := Finset.range_mono hm
  have hrestrict : uSeq b a T i m
      = ∑ k ∈ Finset.range (m + 1), piK b a i k * psiK b a m k := by
    refine (Finset.sum_subset hsub ?_).symm
    intro k _ hk
    rw [Finset.mem_range, not_lt] at hk
    rw [psiK_eq_zero b a (by omega), mul_zero]
  have hpsi : ∑ k ∈ Finset.range (m + 1), piK b a i k * psiK b a m k
      = ∑ k ∈ Finset.range (m + 1), piK b a i k * armaPsi b a (m - k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_range] at hk
    rw [psiK, if_pos (by omega)]
  rw [hrestrict, hpsi]
  by_cases him : i ≤ m
  · have hzero : ∑ k ∈ Finset.Ico 0 i, piK b a i k * armaPsi b a (m - k) = 0 :=
      Finset.sum_eq_zero fun k hk => by
        rw [Finset.mem_Ico] at hk
        rw [piK_eq_zero b a hk.2, zero_mul]
    have hsplit : ∑ k ∈ Finset.range (m + 1), piK b a i k * armaPsi b a (m - k)
        = ∑ k ∈ Finset.Ico i (m + 1), piK b a i k * armaPsi b a (m - k) := by
      rw [Finset.range_eq_Ico,
        ← Finset.sum_Ico_consecutive (fun k => piK b a i k * armaPsi b a (m - k))
          (Nat.zero_le i) (by omega : i ≤ m + 1), hzero, zero_add]
    have hshift : ∑ k ∈ Finset.Ico i (m + 1), piK b a i k * armaPsi b a (m - k)
        = ∑ d ∈ Finset.range ((m - i) + 1), armaPi b a d * armaPsi b a ((m - i) - d) := by
      rw [Finset.sum_Ico_eq_sum_range, show m + 1 - i = (m - i) + 1 by omega]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [piK, if_pos (Nat.le_add_right _ _)]
      congr 2 <;> omega
    rw [hsplit, hshift, armaPi_conv_armaPsi]
    by_cases h : i = m
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]
  · rw [Finset.sum_eq_zero fun k hk => by
      rw [Finset.mem_range] at hk
      rw [piK_eq_zero b a (by omega), zero_mul], if_neg (by omega)]

/-- **Above the horizon**: the geometric estimate `|u_i(m)| ≤ C²(T − i) r^{m−i}`, whose
`(T − i)` factor (rather than `T`) is what keeps the trace bounded. -/
private lemma abs_uSeq_le {C r : ℝ} (hC : 1 ≤ C) (hr0 : 0 ≤ r)
    (hπ : ∀ n, |armaPi b a n| ≤ C * r ^ n) (hψ : ∀ n, |armaPsi b a n| ≤ C * r ^ n)
    {T i m : ℕ} (hi : i < T) (hm : T ≤ m) :
    |uSeq b a T i m| ≤ C ^ 2 * ((T : ℝ) - i) * r ^ (m - i) := by
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hzero : ∑ k ∈ Finset.Ico 0 i, piK b a i k * psiK b a m k = 0 :=
    Finset.sum_eq_zero fun k hk => by
      rw [Finset.mem_Ico] at hk
      rw [piK_eq_zero b a hk.2, zero_mul]
  have hsplit : uSeq b a T i m = ∑ k ∈ Finset.Ico i T, piK b a i k * psiK b a m k := by
    rw [uSeq, Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive (fun k => piK b a i k * psiK b a m k)
        (Nat.zero_le i) (le_of_lt hi), hzero, zero_add]
  have hterm : ∀ k ∈ Finset.Ico i T,
      |piK b a i k * psiK b a m k| ≤ C ^ 2 * r ^ (m - i) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hkm : k ≤ m := by omega
    rw [piK, if_pos hk.1, psiK, if_pos hkm, abs_mul]
    calc |armaPi b a (k - i)| * |armaPsi b a (m - k)|
        ≤ (C * r ^ (k - i)) * (C * r ^ (m - k)) :=
          mul_le_mul (hπ _) (hψ _) (abs_nonneg _) (by positivity)
      _ = C ^ 2 * (r ^ (k - i) * r ^ (m - k)) := by ring
      _ = C ^ 2 * r ^ (m - i) := by rw [← pow_add]; congr 2; omega
  calc |uSeq b a T i m| ≤ ∑ k ∈ Finset.Ico i T, |piK b a i k * psiK b a m k| := by
        rw [hsplit]; exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.Ico i T, C ^ 2 * r ^ (m - i) := Finset.sum_le_sum hterm
    _ = C ^ 2 * ((T : ℝ) - i) * r ^ (m - i) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        have : ((T - i : ℕ) : ℝ) = (T : ℝ) - i := by
          push_cast [Nat.cast_sub (le_of_lt hi)]
          ring
        rw [this]
        ring

/-- Each kernel product is summable in the absolute time `m` (geometric ψ-decay). -/
private lemma summable_psiK_mul (a : Fin q → ℝ) (hb : NoRootClosedDisc b) (s t : ℕ) :
    Summable fun m : ℕ => psiK b a m s * psiK b a m t := by
  obtain ⟨C, hC, r₀, hr₀, hr₁, hbnd₀⟩ := exists_geometric_bound_armaPsi a hb
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = max r₀ (1 / 2) := ⟨_, rfl⟩
  have hrpos : (0 : ℝ) < r := lt_of_lt_of_le (by norm_num) (hrdef ▸ le_max_right r₀ (1 / 2))
  have hrlt : r < 1 := hrdef ▸ max_lt hr₁ (by norm_num)
  have hbnd : ∀ n, |armaPsi b a n| ≤ C * r ^ n := fun n =>
    (hbnd₀ n).trans (by
      have h : r₀ ^ n ≤ r ^ n := pow_le_pow_left₀ hr₀ (hrdef ▸ le_max_left r₀ (1 / 2)) n
      nlinarith)
  have hCr : ∀ u : ℕ, 0 ≤ C / r ^ u := fun u => div_nonneg hC (by positivity)
  have hker : ∀ m u : ℕ, |psiK b a m u| ≤ C / r ^ u * r ^ m := by
    intro m u
    unfold psiK
    split_ifs with h
    · have hsplit : r ^ m = r ^ (m - u) * r ^ u := by rw [← pow_add]; congr 1; omega
      calc |armaPsi b a (m - u)| ≤ C * r ^ (m - u) := hbnd _
        _ = C / r ^ u * (r ^ (m - u) * r ^ u) := by field_simp
        _ = C / r ^ u * r ^ m := by rw [← hsplit]
    · rw [abs_zero]
      exact mul_nonneg (hCr u) (by positivity)
  refine Summable.of_abs (Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun m => ?_)
    ((summable_geometric_of_lt_one (sq_nonneg r) (by nlinarith)).mul_left
      (C / r ^ s * (C / r ^ t))))
  rw [abs_mul]
  calc |psiK b a m s| * |psiK b a m t|
      ≤ (C / r ^ s * r ^ m) * (C / r ^ t * r ^ m) :=
        mul_le_mul (hker m s) (hker m t) (abs_nonneg _) (mul_nonneg (hCr s) (by positivity))
    _ = C / r ^ s * (C / r ^ t) * (r ^ 2) ^ m := by rw [← pow_mul]; ring

/-- **The Cholesky-type factorization of the model ACVF**: `γ(s − t) = Σ_m ψ̃(m,s) ψ̃(m,t)`. -/
private lemma armaACVF_eq_tsum_psiK (a : Fin q → ℝ) (hb : NoRootClosedDisc b) (s t : ℕ) :
    armaACVF b a ((s : ℤ) - (t : ℤ)) = ∑' m : ℕ, psiK b a m s * psiK b a m t := by
  have main : ∀ u v : ℕ, v ≤ u →
      armaACVF b a ((u : ℤ) - (v : ℤ)) = ∑' m : ℕ, psiK b a m u * psiK b a m v := by
    intro u v hvu
    have hs := summable_psiK_mul a hb u v
    have hzero : ∑ i ∈ Finset.range u, psiK b a i u * psiK b a i v = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rw [psiK_eq_zero b a (Finset.mem_range.1 hi), zero_mul]
    have hsplit := hs.sum_add_tsum_nat_add u
    rw [hzero, zero_add] at hsplit
    rw [← hsplit, armaACVF, show ((u : ℤ) - (v : ℤ)).natAbs = u - v by omega]
    refine tsum_congr fun j => ?_
    have h1 : psiK b a (j + u) u = armaPsi b a j := by simp [psiK]
    have h2 : psiK b a (j + u) v = armaPsi b a (j + (u - v)) := by
      rw [psiK, if_pos (by omega)]
      congr 1
      omega
    rw [h1, h2]
  rcases le_total t s with h | h
  · exact main s t h
  · have hsymm : armaACVF b a ((s : ℤ) - (t : ℤ)) = armaACVF b a ((t : ℤ) - (s : ℤ)) := by
      simp only [armaACVF, show ((s : ℤ) - (t : ℤ)).natAbs = ((t : ℤ) - (s : ℤ)).natAbs by omega]
    rw [hsymm, main t s h]
    exact tsum_congr fun m => mul_comm _ _

/-- Fubini for a weighted Gram pairing of `ℓ²`-type sequences. -/
private lemma tsum_weighted_gram {T : ℕ} (v : Fin T → ℕ → ℝ)
    (hv : ∀ i j, Summable fun m : ℕ => v i m * v j m) (c d : Fin T → ℝ) :
    ∑' m : ℕ, (∑ i, c i * v i m) * (∑ j, d j * v j m)
      = ∑ i, ∑ j, c i * d j * ∑' m : ℕ, v i m * v j m := by
  have hsummand : ∀ i j : Fin T, Summable fun m : ℕ => (c i * v i m) * (d j * v j m) := by
    intro i j
    exact ((hv i j).mul_left (c i * d j)).congr fun m => by ring
  have hexp : ∀ m : ℕ, (∑ i, c i * v i m) * (∑ j, d j * v j m)
      = ∑ i, ∑ j, (c i * v i m) * (d j * v j m) := fun m => Finset.sum_mul_sum _ _ _ _
  rw [tsum_congr hexp,
    Summable.tsum_finsetSum (fun i _ => summable_sum fun j _ => hsummand i j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Summable.tsum_finsetSum (fun j _ => hsummand i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← tsum_mul_left]
  exact tsum_congr fun m => by ring

private lemma summable_uSeq_mul (hb : NoRootClosedDisc b) (T i j : ℕ) :
    Summable fun m : ℕ => uSeq b a T i m * uSeq b a T j m := by
  have h : ∀ m : ℕ, uSeq b a T i m * uSeq b a T j m
      = ∑ k ∈ Finset.range T, ∑ l ∈ Finset.range T,
          (piK b a i k * piK b a j l) * (psiK b a m k * psiK b a m l) := by
    intro m
    rw [uSeq, uSeq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  refine Summable.congr ?_ fun m => (h m).symm
  exact summable_sum fun k _ => summable_sum fun l _ => (summable_psiK_mul a hb k l).mul_left _

/-- The **inversion matrix** `Π_T` (upper triangular with unit diagonal). -/
private noncomputable def piMat (b : Fin p → ℝ) (a : Fin q → ℝ) (T : ℕ) :
    Matrix (Fin T) (Fin T) ℝ :=
  Matrix.of fun i k => piK b a (i : ℕ) (k : ℕ)

/-- The **tail Gram matrix** `G_T = Π_T Γ_T Π_Tᵀ − 1`. -/
private noncomputable def gramTail (b : Fin p → ℝ) (a : Fin q → ℝ) (T : ℕ) :
    Matrix (Fin T) (Fin T) ℝ :=
  Matrix.of fun i j => ∑' m : ℕ, uSeq b a T (i : ℕ) (m + T) * uSeq b a T (j : ℕ) (m + T)

private lemma det_piMat (b : Fin p → ℝ) (a : Fin q → ℝ) (T : ℕ) : (piMat b a T).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [piMat, piK_self]
  · intro i j hij
    exact piK_eq_zero b a hij

/-- **The whitened Toeplitz matrix is `1` plus a tail Gram matrix.** -/
private lemma piMat_mul_toeplitz_mul_transpose (hB : ARMAInvertibleParams b a) (T : ℕ) :
    piMat b a T * armaToeplitz b a T * (piMat b a T)ᵀ = 1 + gramTail b a T := by
  have huFin : ∀ x m : ℕ,
      uSeq b a T x m = ∑ k : Fin T, piK b a x (k : ℕ) * psiK b a m (k : ℕ) := by
    intro x m
    rw [uSeq, ← Fin.sum_univ_eq_sum_range (fun k => piK b a x k * psiK b a m k) T]
  ext i j
  have hgram := tsum_weighted_gram (T := T) (fun k m => psiK b a m (k : ℕ))
    (fun k l => summable_psiK_mul a hB.1 (k : ℕ) (l : ℕ))
    (fun k => piK b a (i : ℕ) (k : ℕ)) (fun l => piK b a (j : ℕ) (l : ℕ))
  have hentry : (piMat b a T * armaToeplitz b a T * (piMat b a T)ᵀ) i j
      = ∑' m : ℕ, uSeq b a T (i : ℕ) m * uSeq b a T (j : ℕ) m := by
    simp only [huFin]
    rw [hgram]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, piMat, Matrix.of_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hΓ : (∑' m : ℕ, psiK b a m (l : ℕ) * psiK b a m (k : ℕ)) = armaToeplitz b a T l k :=
      (armaACVF_eq_tsum_psiK a hB.1 (l : ℕ) (k : ℕ)).symm
    rw [hΓ]
    ring
  rw [hentry]
  have hsplit := (summable_uSeq_mul (a := a) hB.1 T (i : ℕ) (j : ℕ)).sum_add_tsum_nat_add T
  rw [← hsplit]
  have hhead : ∑ m ∈ Finset.range T, uSeq b a T (i : ℕ) m * uSeq b a T (j : ℕ) m
      = (1 : Matrix (Fin T) (Fin T) ℝ) i j := by
    have hterm : ∀ m ∈ Finset.range T,
        uSeq b a T (i : ℕ) m * uSeq b a T (j : ℕ) m
          = (if (i : ℕ) = m then (1 : ℝ) else 0) * (if (j : ℕ) = m then 1 else 0) := by
      intro m hm
      rw [Finset.mem_range] at hm
      rw [uSeq_eq_of_lt b a hm, uSeq_eq_of_lt b a hm]
    rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single (i : ℕ)]
    · rw [if_pos rfl, one_mul, Matrix.one_apply]
      by_cases h : i = j
      · rw [if_pos h, if_pos (by rw [h])]
      · rw [if_neg h, if_neg (by simpa [Fin.ext_iff, eq_comm] using h)]
    · intro m _ hm
      rw [if_neg (Ne.symm hm), zero_mul]
    · intro h
      exact absurd (Finset.mem_range.2 i.isLt) h
  rw [hhead]
  rfl

private lemma gramTail_posSemidef (hB : ARMAInvertibleParams b a) (T : ℕ) :
    (gramTail b a T).PosSemidef := by
  have hsummable : ∀ i j : Fin T,
      Summable fun m : ℕ => uSeq b a T (i : ℕ) (m + T) * uSeq b a T (j : ℕ) (m + T) :=
    fun i j => (summable_nat_add_iff T).2 (summable_uSeq_mul (a := a) hB.1 T (i : ℕ) (j : ℕ))
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun c => ?_
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, gramTail, Matrix.of_apply]
    exact tsum_congr fun m => mul_comm _ _
  · have hquad : star c ⬝ᵥ (gramTail b a T *ᵥ c)
        = ∑' m : ℕ, (∑ i, c i * uSeq b a T (i : ℕ) (m + T)) *
            (∑ j, c j * uSeq b a T (j : ℕ) (m + T)) := by
      rw [tsum_weighted_gram (fun i m => uSeq b a T (i : ℕ) (m + T)) hsummable c c]
      simp only [dotProduct, mulVec, gramTail, Matrix.of_apply, star_trivial, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hquad]
    refine tsum_nonneg fun m => ?_
    exact mul_self_nonneg _

/-- **The uniform trace bound**: `tr G_T ≤ K` with `K` free of `T` — the quantitative
heart of the Szegő limit. -/
private lemma trace_gramTail_le {C r : ℝ} (hC : 1 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hπ : ∀ n, |armaPi b a n| ≤ C * r ^ n) (hψ : ∀ n, |armaPsi b a n| ≤ C * r ^ n)
    (hB : ARMAInvertibleParams b a) (T : ℕ) :
    (gramTail b a T).trace
      ≤ C ^ 4 / (1 - r ^ 2) * ∑' d : ℕ, ((d : ℝ) + 1) ^ 2 * (r ^ 2) ^ (d + 1) := by
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC
  have hr2 : (0 : ℝ) ≤ r ^ 2 := sq_nonneg r
  have hr2lt : r ^ 2 < 1 := by nlinarith
  have hgeom : Summable fun m : ℕ => (r ^ 2) ^ m := summable_geometric_of_lt_one hr2 hr2lt
  have hgeomval : ∑' m : ℕ, (r ^ 2) ^ m = (1 - r ^ 2)⁻¹ := tsum_geometric_of_lt_one hr2 hr2lt
  have hmaj : Summable fun d : ℕ => ((d : ℝ) + 1) ^ 2 * (r ^ 2) ^ (d + 1) := by
    have h0 : Summable fun n : ℕ => (r ^ 2) ^ n := hgeom
    have h1 : Summable fun n : ℕ => (n : ℝ) ^ 1 * (r ^ 2) ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1
        (by rw [Real.norm_eq_abs, abs_of_nonneg hr2]; exact hr2lt)
    have h2 : Summable fun n : ℕ => (n : ℝ) ^ 2 * (r ^ 2) ^ n :=
      summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2
        (by rw [Real.norm_eq_abs, abs_of_nonneg hr2]; exact hr2lt)
    have hsum := ((h2.add (h1.mul_left 2)).add h0).mul_right (r ^ 2)
    refine hsum.congr fun n => ?_
    rw [pow_succ]
    ring
  -- the diagonal estimate
  have hdiag : ∀ i : Fin T, gramTail b a T i i
      ≤ C ^ 4 / (1 - r ^ 2) * (((T - (i : ℕ) : ℕ) : ℝ) ^ 2 * (r ^ 2) ^ ((T : ℕ) - (i : ℕ))) := by
    intro i
    have hi : (i : ℕ) < T := i.isLt
    have hterm : ∀ m : ℕ,
        uSeq b a T (i : ℕ) (m + T) * uSeq b a T (i : ℕ) (m + T)
          ≤ C ^ 4 * (((T - (i : ℕ) : ℕ) : ℝ) ^ 2 * (r ^ 2) ^ ((T : ℕ) - (i : ℕ))) *
              (r ^ 2) ^ m := by
      intro m
      have hb := abs_uSeq_le hC hr0 hπ hψ hi (Nat.le_add_left T m)
      have hcast : ((T : ℝ) - (i : ℕ)) = ((T - (i : ℕ) : ℕ) : ℝ) := by
        rw [Nat.cast_sub (le_of_lt hi)]
      have hexp : r ^ (m + T - (i : ℕ)) = r ^ m * r ^ (T - (i : ℕ)) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hcast, hexp] at hb
      have hsq : (uSeq b a T (i : ℕ) (m + T)) ^ 2
          ≤ (C ^ 2 * ((T - (i : ℕ) : ℕ) : ℝ) * (r ^ m * r ^ (T - (i : ℕ)))) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hb 2
      calc uSeq b a T (i : ℕ) (m + T) * uSeq b a T (i : ℕ) (m + T)
          = (uSeq b a T (i : ℕ) (m + T)) ^ 2 := (sq _).symm
        _ ≤ (C ^ 2 * ((T - (i : ℕ) : ℕ) : ℝ) * (r ^ m * r ^ (T - (i : ℕ)))) ^ 2 := hsq
        _ = C ^ 4 * (((T - (i : ℕ) : ℕ) : ℝ) ^ 2 * (r ^ 2) ^ ((T : ℕ) - (i : ℕ))) *
              (r ^ 2) ^ m := by
            rw [← pow_mul, ← pow_mul, mul_comm 2 m, mul_comm 2 (T - (i : ℕ)), pow_mul, pow_mul]
            ring
    have hsum1 : Summable fun m : ℕ =>
        uSeq b a T (i : ℕ) (m + T) * uSeq b a T (i : ℕ) (m + T) :=
      (summable_nat_add_iff T).2 (summable_uSeq_mul (a := a) hB.1 T (i : ℕ) (i : ℕ))
    have hsum2 := hgeom.mul_left
      (C ^ 4 * (((T - (i : ℕ) : ℕ) : ℝ) ^ 2 * (r ^ 2) ^ ((T : ℕ) - (i : ℕ))))
    have := hsum1.tsum_le_tsum hterm hsum2
    rw [tsum_mul_left, hgeomval] at this
    calc gramTail b a T i i
        = ∑' m : ℕ, uSeq b a T (i : ℕ) (m + T) * uSeq b a T (i : ℕ) (m + T) := rfl
      _ ≤ C ^ 4 * (((T - (i : ℕ) : ℕ) : ℝ) ^ 2 * (r ^ 2) ^ ((T : ℕ) - (i : ℕ))) *
            (1 - r ^ 2)⁻¹ := this
      _ = C ^ 4 / (1 - r ^ 2) *
            (((T - (i : ℕ) : ℕ) : ℝ) ^ 2 * (r ^ 2) ^ ((T : ℕ) - (i : ℕ))) := by
          rw [div_eq_mul_inv]
          ring
  have hconst : (0 : ℝ) ≤ C ^ 4 / (1 - r ^ 2) := by
    have : (0 : ℝ) < 1 - r ^ 2 := by nlinarith
    positivity
  calc (gramTail b a T).trace
      = ∑ i : Fin T, gramTail b a T i i := rfl
    _ ≤ ∑ i : Fin T, C ^ 4 / (1 - r ^ 2) *
          (((T - (i : ℕ) : ℕ) : ℝ) ^ 2 * (r ^ 2) ^ ((T : ℕ) - (i : ℕ))) :=
        Finset.sum_le_sum fun i _ => hdiag i
    _ = C ^ 4 / (1 - r ^ 2) *
          ∑ i ∈ Finset.range T, ((T - i : ℕ) : ℝ) ^ 2 * (r ^ 2) ^ (T - i) := by
        rw [← Finset.mul_sum,
          Fin.sum_univ_eq_sum_range (fun i => ((T - i : ℕ) : ℝ) ^ 2 * (r ^ 2) ^ (T - i)) T]
    _ ≤ C ^ 4 / (1 - r ^ 2) * ∑' d : ℕ, ((d : ℝ) + 1) ^ 2 * (r ^ 2) ^ (d + 1) := by
        refine mul_le_mul_of_nonneg_left ?_ hconst
        have hreflect : ∑ i ∈ Finset.range T, ((T - i : ℕ) : ℝ) ^ 2 * (r ^ 2) ^ (T - i)
            = ∑ d ∈ Finset.range T, ((d : ℝ) + 1) ^ 2 * (r ^ 2) ^ (d + 1) := by
          rw [← Finset.sum_range_reflect
            (fun d => ((d : ℝ) + 1) ^ 2 * (r ^ 2) ^ (d + 1)) T]
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.mem_range] at hi
          have h1 : T - 1 - i + 1 = T - i := by omega
          rw [h1]
          congr 1
          rw [Nat.cast_sub (by omega : i ≤ T)]
          have : ((T - 1 - i : ℕ) : ℝ) + 1 = (T : ℝ) - i := by
            rw [Nat.cast_sub (by omega : i ≤ T - 1), Nat.cast_sub (by omega : 1 ≤ T)]
            push_cast
            ring
          rw [this]
        rw [hreflect]
        exact hmaj.sum_le_tsum _ (fun d _ => by positivity)

/-- `det (1 + G) = ∏(1 + λ_j(G))` for positive semidefinite `G`: bounded below by `1`,
and its logarithm bounded above by `tr G`. -/
private lemma det_one_add_bounds {n : ℕ} {G : Matrix (Fin n) (Fin n) ℝ}
    (hGh : G.IsHermitian) (hnn : ∀ i, 0 ≤ Matrix.IsHermitian.eigenvalues hGh i) :
    1 ≤ (1 + G).det ∧ Real.log (1 + G).det ≤ G.trace := by
  obtain ⟨d, hd⟩ : ∃ d : Fin n → ℝ, d = Matrix.IsHermitian.eigenvalues hGh := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : unitary (Matrix (Fin n) (Fin n) ℝ),
      U = Matrix.IsHermitian.eigenvectorUnitary hGh := ⟨_, rfl⟩
  have hnn' : ∀ i, 0 ≤ d i := by rw [hd]; exact hnn
  have hdet : (1 + G).det = ∏ i, (1 + d i) := by
    have hspec : (1 : Matrix (Fin n) (Fin n) ℝ) + G
        = Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ) U
            (1 + Matrix.diagonal (RCLike.ofReal ∘ d)) := by
      rw [map_add, map_one, hd, hU, ← Matrix.IsHermitian.spectral_theorem hGh]
    have hUdet : ((U : Matrix (Fin n) (Fin n) ℝ)).det *
        (star (U : Matrix (Fin n) (Fin n) ℝ)).det = 1 := by
      have hmul : (U : Matrix (Fin n) (Fin n) ℝ) * star (U : Matrix (Fin n) (Fin n) ℝ) = 1 := by
        simp
      rw [← Matrix.det_mul, hmul, Matrix.det_one]
    have hdiag : (1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.diagonal (RCLike.ofReal ∘ d)
        = Matrix.diagonal fun i => 1 + d i := by
      rw [← Matrix.diagonal_one, Matrix.diagonal_add]
      rfl
    rw [hspec, Unitary.conjStarAlgAut_apply, hdiag, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_diagonal]
    calc ((U : Matrix (Fin n) (Fin n) ℝ)).det * (∏ i, (1 + d i))
          * (star (U : Matrix (Fin n) (Fin n) ℝ)).det
        = (((U : Matrix (Fin n) (Fin n) ℝ)).det *
            (star (U : Matrix (Fin n) (Fin n) ℝ)).det) * ∏ i, (1 + d i) := by ring
      _ = ∏ i, (1 + d i) := by rw [hUdet, one_mul]
  have htrace : G.trace = ∑ i, d i := by
    rw [hd]
    simpa using Matrix.IsHermitian.trace_eq_sum_eigenvalues hGh
  refine ⟨?_, ?_⟩
  · rw [hdet]
    exact Finset.one_le_prod fun i _ => by linarith [hnn' i]
  · rw [hdet, htrace, Real.log_prod fun i _ => by
      have := hnn' i
      positivity]
    refine Finset.sum_le_sum fun i _ => ?_
    have h := Real.log_le_sub_one_of_pos (x := 1 + d i) (by linarith [hnn' i])
    linarith

/-- The two-sided bound `0 ≤ log det Γ_T ≤ K` with `K` free of `T`. -/
private lemma log_det_armaToeplitz_bounds {C r : ℝ} (hC : 1 ≤ C) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hπ : ∀ n, |armaPi b a n| ≤ C * r ^ n) (hψ : ∀ n, |armaPsi b a n| ≤ C * r ^ n)
    (hB : ARMAInvertibleParams b a) (T : ℕ) :
    0 ≤ Real.log (armaToeplitz b a T).det ∧
      Real.log (armaToeplitz b a T).det
        ≤ C ^ 4 / (1 - r ^ 2) * ∑' d : ℕ, ((d : ℝ) + 1) ^ 2 * (r ^ 2) ^ (d + 1) := by
  have hdet : (armaToeplitz b a T).det = (1 + gramTail b a T).det := by
    rw [← piMat_mul_toeplitz_mul_transpose hB T, Matrix.det_mul, Matrix.det_mul,
      Matrix.det_transpose, det_piMat]
    ring
  have hpsd := gramTail_posSemidef (a := a) hB T
  obtain ⟨h1, h2⟩ := det_one_add_bounds hpsd.1 (Matrix.PosSemidef.eigenvalues_nonneg hpsd)
  refine ⟨?_, ?_⟩
  · rw [hdet]
    exact Real.log_nonneg h1
  · rw [hdet]
    exact h2.trans (trace_gramTail_le hC hr0 hr1 hπ hψ hB T)

end Szego

/-- **Szegő-type limit**: on the constraint set, `T⁻¹ log det Γ_T(b, a) → 0`
(unit-variance model; `det Γ_T = ∏_{j<T} ν_j` with innovations variances `ν_j ↓ 1`
geometrically). -/
theorem logdet_armaToeplitz_vanishes {p q : ℕ} {b : Fin p → ℝ} {a : Fin q → ℝ}
    (hB : ARMAInvertibleParams b a) :
    Tendsto (fun T : ℕ => (T : ℝ)⁻¹ * Real.log (armaToeplitz b a T).det)
      atTop (𝓝 0) := by
  obtain ⟨C, r, hC, hr0, hr1, hπ, hψ⟩ := exists_common_geometric_bound hB hB
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ,
      K = C ^ 4 / (1 - r ^ 2) * ∑' d : ℕ, ((d : ℝ) + 1) ^ 2 * (r ^ 2) ^ (d + 1) := ⟨_, rfl⟩
  refine squeeze_zero_norm (fun T => ?_) (tendsto_const_div_atTop_nhds_zero_nat K)
  obtain ⟨hlow, hhigh⟩ := log_det_armaToeplitz_bounds hC hr0 hr1 hπ hψ hB T
  have hTnn : (0 : ℝ) ≤ (T : ℝ)⁻¹ := inv_nonneg.2 (Nat.cast_nonneg T)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hTnn hlow), div_eq_mul_inv, mul_comm K]
  exact mul_le_mul_of_nonneg_left (hKdef ▸ hhigh) hTnn

section Process

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The one missing analytic input of this lane** (named debt): the *quadratic-form
law of large numbers*

  `T⁻¹ · xᵀ Γ_T(θ)⁻¹ x  →p  σ² · armaContrastVar θ₀ θ`

for data from the true ARMA law. This is Hannan's ergodic step: `T⁻¹ Σ_t r_t(θ)²` for
the stationary `θ`-residual process `r(θ)` (an iid-driven linear process) converges by
the *pointwise ergodic theorem*, which Mathlib does not have; the `L²` route is blocked
because the ACVF of `r(θ)²` involves fourth cumulants and FY assumes only two moments.
Everything else in `criterion_tendsto_contrast` is discharged from this input below
(the `log`-continuity transfer and the deterministic `T⁻¹ log det Γ_T → 0`, which is
PROVED as `logdet_armaToeplitz_vanishes`). -/
private theorem armaProfileS_tendstoInProb [IsProbabilityMeasure μ] {p q : ℕ}
    {b0 b : Fin p → ℝ} {a0 a : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b0 a0 σ2 X ε μ) (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hB0 : ARMAInvertibleParams b0 a0) (hB : ARMAInvertibleParams b a)
    (hcausal : IsLinearProcessOf (armaPsi b0 a0) X ε μ)
    (hmeas : ∀ t, Measurable (X t)) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun T : ℕ => (μ {ω | η ≤
        |(T : ℝ)⁻¹ * armaProfileS b a (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
          - σ2 * armaContrastVar b0 a0 b a|}).toReal)
      atTop (𝓝 0) := by
  sorry

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
  -- the limit is `≥ σ² > 0`, so `log` is continuous there (`one_le_armaContrastVar`)
  have hc : 0 < σ2 * armaContrastVar b0 a0 b a := by
    nlinarith [one_le_armaContrastVar hB0 hB]
  obtain ⟨η, hη, hlog⟩ : ∃ η > 0, ∀ y : ℝ, |y - σ2 * armaContrastVar b0 a0 b a| < η →
      |Real.log y - Real.log (σ2 * armaContrastVar b0 a0 b a)| < δ / 2 := by
    have hcont : ContinuousAt Real.log (σ2 * armaContrastVar b0 a0 b a) :=
      Real.continuousAt_log (ne_of_gt hc)
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨η, hη, hball⟩ := hcont (δ / 2) (by linarith)
    refine ⟨η, hη, fun y hy => ?_⟩
    have := hball (x := y) (by rwa [Real.dist_eq])
    rwa [Real.dist_eq] at this
  -- the log-determinant term is deterministic and vanishes
  have hLsmall : ∀ᶠ T : ℕ in atTop,
      |(T : ℝ)⁻¹ * Real.log (armaToeplitz b a T).det| < δ / 2 := by
    have hball := (logdet_armaToeplitz_vanishes hB).eventually
      (Metric.ball_mem_nhds (0 : ℝ) (by linarith : (0 : ℝ) < δ / 2))
    filter_upwards [hball] with T hT
    simpa [Real.dist_eq] using hT
  refine squeeze_zero' (Eventually.of_forall fun T => ENNReal.toReal_nonneg) ?_
    (armaProfileS_tendstoInProb h hiid hσ hB0 hB hcausal hmeas hη)
  filter_upwards [hLsmall] with T hT
  refine ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono fun ω hω => ?_)
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra hcon
  push Not at hcon
  have h1 := hlog _ hcon
  have hsplit : armaProfileCriterion b a (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω)
        - Real.log (σ2 * armaContrastVar b0 a0 b a)
      = (Real.log ((T : ℝ)⁻¹ *
            armaProfileS b a (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
          - Real.log (σ2 * armaContrastVar b0 a0 b a))
        + (T : ℝ)⁻¹ * Real.log (armaToeplitz b a T).det := by
    rw [armaProfileCriterion, div_eq_inv_mul]
    ring
  rw [hsplit] at hω
  have habs := abs_add_le
    (Real.log ((T : ℝ)⁻¹ * armaProfileS b a (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω))
      - Real.log (σ2 * armaContrastVar b0 a0 b a))
    ((T : ℝ)⁻¹ * Real.log (armaToeplitz b a T).det)
  linarith

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
  -- **FALSE AS FROZEN**, for the identifiability reason isolated (and formalized) in
  -- `mle_consistent_not_identifiable`: nothing here forces the *working* pairs in `K` to
  -- be coprime, and the profiled criterion is a function of the transfer function only.
  -- Concretely (`p = q = 1`): with `b₀ = a₀ = 0`, `K = {(0,0), (1/2, −1/2)}` (finite,
  -- hence compact; both members in `𝓑`; `(b₀,a₀) ∈ K`; `hcop` holds) and the *constant*
  -- measurable sequence `θ T ω = (1/2, −1/2)`, the hypothesis `hargmin` holds with
  -- `δT = 0` because
  --   `armaProfileCriterion (1/2) (−1/2) x = armaProfileCriterion 0 0 x` for every `x`
  -- (`mle_consistent_not_identifiable`, PROVED: the two models have the same `armaPsi`,
  -- hence the same `armaACVF`, hence the same `Γ_T`), while
  -- `dist (θ T ω) (b₀,a₀) = ‖(1/2, −1/2)‖ > 0` for all `T`, so the conclusion fails for
  -- any `δ` below that distance.
  --
  -- REPAIR (then this lane's wiring closes): add minimality of the search region, e.g.
  -- `(hcopK : ∀ ba ∈ K, IsCoprime (arPoly ba.1) (maPoly ba.2))`. With it,
  -- `armaContrastVar_eq_one_iff_transfer` upgrades to parameter identifiability, and the
  -- standard argmin-consistency argument runs on: (i) `criterion_tendsto_contrast`
  -- (PROVED here modulo the single named debt `armaProfileS_tendstoInProb`),
  -- (ii) `one_le_armaContrastVar` + continuity of `θ ↦ armaContrastVar θ₀ θ` giving a
  -- positive contrast gap `inf {K(θ) − K(θ₀) : θ ∈ K, dist θ θ₀ ≥ δ} > 0` on the compact
  -- `K`, and (iii) a finite subcover / stochastic-equicontinuity step to make the
  -- convergence in (i) uniform over `K`.
  sorry

end Process

end StatLean.TimeSeries
