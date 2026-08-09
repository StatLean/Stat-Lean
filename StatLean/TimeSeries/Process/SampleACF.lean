import StatLean.TimeSeries.ForMathlib.PosSemidefSequence
import StatLean.TimeSeries.ForMathlib.Probability.TriangularCLT
import StatLean.TimeSeries.Models.Linear
import StatLean.TimeSeries.Process.Stationary
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Sampling theory of the ACVF/ACF (FY §2.2.2, Theorem 2.8, eqs. (2.23)–(2.27))

Deterministic and asymptotic properties of the sample autocovariance `γ̂` and sample
autocorrelation `ρ̂` (divisor-`T`, mean-corrected — FY eq. (2.23), defined in
`Process/Defs.lean`):

* the divisor-`T` sample ACVF is a **positive semidefinite sequence** (FY §2.2.2's
  "may be shown" claim; false for the `1/(T−k)` divisor);
* **FY Theorem 2.8** for two-sided linear processes (eq. (2.24)) with IID innovations —
  (i) the sample-mean CLT [ledger-(a) debt: B&D §7.3 m-dependent route],
  (ii) the CLT for `γ̂(0)` [ledger-(b) debt], (iii) **Bartlett's formula** (eq. (2.26)),
  stated in Cramér–Wold form [ledger-(b) debt];
* **FY eq. (2.27)**, *proved* from the Bartlett statement: for an MA(q) process and lag
  `j > q`, `√T ρ̂(j) →d N(0, 1 + 2Σ_{t=1}^q ρ(t)²)` — the basis of the ±1.96/√T
  confidence bands and the §3.4.4 ACF order-identification rule.

**Misprint corrections (stated as provable, per project policy).**
* FY eq. (2.25) prints `ν₂² = 2σ⁴ Σ_j ρ(j)²`; dimensional analysis and
  B&D (1991) Prop 7.3.4 give `ν₂² = (η − 3)γ(0)² + 2 Σ_{j∈ℤ} γ(j)²` with
  `η = Eε⁴/σ⁴` — we state the corrected form.
* FY eq. (2.27) prints `1 + 2Σ_{t=1}^q ρ(q)²`; the correct summand is `ρ(t)²`.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.2.2
(pp. 41–43), Theorem 2.8, eqs. (2.23)–(2.27). (`FY §2.2.2`.)

**Bibliographic comments.** Bartlett's formula is M. S. Bartlett (1946), *On the
theoretical specification and sampling properties of autocorrelated time-series*; the
modern proofs via m-dependent truncation are Brockwell & Davis (1991), §7.2–7.3
(Props 7.3.1–7.3.4, Thm 7.2.1). The psd property of the divisor-`T` estimator and its
failure for `1/(T−k)` are discussed in B&D (1991), §7.2 and Percival–Walden (1993).

The CLT statements are phrased through pointwise characteristic-function convergence
(Lévy-equivalent to convergence in distribution), matching the batch-A/B debt
conventions. The linear-process hypothesis is spelled as an explicit two-sided `L²`
partial-sum limit — definitionally `IsFilteredBy` (`Spectral/LinearFilter.lean`), which
this Process-layer file must not import.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-! ### Positive semidefiniteness of the divisor-`T` sample ACVF

The mechanism: write `y` for the mean-corrected data zero-padded to all of `ℤ`
(`padData`). The divisor-`T` sample ACVF is exactly the (un-normalized) autocorrelation
of this compactly supported sequence, `T·γ̂(k) = Σ_s y_s y_{s+k}` at *every* lag `k ∈ ℤ`
(`sum_padData_eq_rawACVF`) — this is where the divisor `T` rather than `T − k` is used,
and where the `1/(T−k)` estimator fails. The quadratic form then collapses to a sum of
squares, `Σ_{ij} a_i a_j γ̂(t_i − t_j) = T⁻¹ Σ_s (Σ_i a_i y_{s+t_i})² ≥ 0`. -/

/-- The mean-corrected data vector as a function on `ℕ`, junk `0` outside the window. -/
private noncomputable def padNat {T : ℕ} (x : Fin T → ℝ) (n : ℕ) : ℝ :=
  if h : n < T then x ⟨n, h⟩ - sampleMean x else 0

/-- The mean-corrected data vector, zero-padded to all of `ℤ`. -/
private noncomputable def padData {T : ℕ} (x : Fin T → ℝ) (s : ℤ) : ℝ :=
  if h : 0 ≤ s ∧ s.toNat < T then x ⟨s.toNat, h.2⟩ - sampleMean x else 0

/-- The un-normalized (divisor-free) sample ACVF: the inner sum of `sampleACVF`. -/
private noncomputable def rawACVF {T : ℕ} (x : Fin T → ℝ) (k : ℕ) : ℝ :=
  ∑ t : Fin T, if h : (t : ℕ) + k < T then
    (x t - sampleMean x) * (x ⟨(t : ℕ) + k, h⟩ - sampleMean x) else 0

private lemma sampleACVF_eq_raw {T : ℕ} (x : Fin T → ℝ) (k : ℕ) :
    sampleACVF x k = (T : ℝ)⁻¹ * rawACVF x k := rfl

/-- `padData` is supported in the data window `[0, T)`. -/
private lemma padData_eq_zero {T : ℕ} (x : Fin T → ℝ) {s : ℤ}
    (hs : s ∉ Finset.Ico (0 : ℤ) (T : ℤ)) : padData x s = 0 := by
  rw [padData, dif_neg]
  simp only [Finset.mem_Ico, not_and, not_lt] at hs
  rintro ⟨h1, h2⟩
  have := hs h1
  omega

private lemma padData_of_nonneg {T : ℕ} (x : Fin T → ℝ) {s : ℤ} (hs : 0 ≤ s) :
    padData x s = padNat x s.toNat := by
  rw [padData, padNat]
  by_cases h : s.toNat < T
  · rw [dif_pos ⟨hs, h⟩, dif_pos h]
  · rw [dif_neg (fun hc => h hc.2), dif_neg h]

private lemma rawACVF_eq_range {T : ℕ} (x : Fin T → ℝ) (m : ℕ) :
    rawACVF x m = ∑ n ∈ Finset.range T, padNat x n * padNat x (n + m) := by
  rw [rawACVF, ← Fin.sum_univ_eq_sum_range (fun n => padNat x n * padNat x (n + m)) T]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : padNat x (i : ℕ) = x i - sampleMean x := by
    rw [padNat, dif_pos i.isLt]
  rw [h1, padNat]
  by_cases h2 : (i : ℕ) + m < T
  · rw [dif_pos h2, dif_pos h2]
  · rw [dif_neg h2, dif_neg h2, mul_zero]

/-- At a nonnegative lag the window sum over `[0, T)` is the raw sample ACVF. -/
private lemma sum_padData_ico {T : ℕ} (x : Fin T → ℝ) (m : ℕ) :
    ∑ s ∈ Finset.Ico (0 : ℤ) (T : ℤ), padData x s * padData x (s + (m : ℤ))
      = rawACVF x m := by
  rw [rawACVF_eq_range]
  refine Finset.sum_nbij' (fun s => s.toNat) (fun n => (n : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro s hs; simp only [Finset.mem_Ico] at hs; simp only [Finset.mem_range]; omega
  · intro n hn; simp only [Finset.mem_range] at hn; simp only [Finset.mem_Ico]; omega
  · intro s hs; simp only [Finset.mem_Ico] at hs; dsimp only; omega
  · intro n hn; simp only [Finset.mem_range] at hn; dsimp only; omega
  · intro s hs
    simp only [Finset.mem_Ico] at hs
    dsimp only
    rw [padData_of_nonneg x (by omega), padData_of_nonneg x (by omega)]
    congr 2
    omega

/-- The window may be enlarged freely: the padding kills every extra term. -/
private lemma sum_padData_window {T : ℕ} (x : Fin T → ℝ) (k : ℤ) {S : Finset ℤ}
    (hS : Finset.Ico (0 : ℤ) (T : ℤ) ⊆ S) :
    ∑ s ∈ S, padData x s * padData x (s + k)
      = ∑ s ∈ Finset.Ico (0 : ℤ) (T : ℤ), padData x s * padData x (s + k) :=
  (Finset.sum_subset hS fun s _ hs => by rw [padData_eq_zero x hs, zero_mul]).symm

/-- The window sum is even in the lag (reindex by the lag, on a window large enough to
absorb the shift). -/
private lemma sum_padData_symm {T : ℕ} (x : Fin T → ℝ) (k : ℤ) :
    ∑ s ∈ Finset.Ico (0 : ℤ) (T : ℤ), padData x s * padData x (s + k)
      = ∑ s ∈ Finset.Ico (0 : ℤ) (T : ℤ), padData x s * padData x (s + -k) := by
  obtain ⟨K, hK1, hK2⟩ : ∃ K : ℤ, -K ≤ k ∧ k ≤ K := ⟨|k|, neg_abs_le k, le_abs_self k⟩
  have hsub1 : Finset.Ico (0 : ℤ) (T : ℤ) ⊆ Finset.Ico (-K) ((T : ℤ) + K) := by
    intro s hs; simp only [Finset.mem_Ico] at *; omega
  have hsub2 : Finset.Ico (0 : ℤ) (T : ℤ) ⊆ Finset.Ico (-K + k) ((T : ℤ) + K + k) := by
    intro s hs; simp only [Finset.mem_Ico] at *; omega
  rw [← sum_padData_window x k hsub1, ← sum_padData_window x (-k) hsub2]
  refine Finset.sum_nbij' (fun s => s + k) (fun u => u - k) ?_ ?_ ?_ ?_ ?_
  · intro s hs; simp only [Finset.mem_Ico] at *; omega
  · intro u hu; simp only [Finset.mem_Ico] at *; omega
  · intro s _; ring
  · intro u _; ring
  · intro s _; rw [show s + k + -k = s from by ring, mul_comm]

/-- **The key deterministic identity**: at *every* integer lag, the raw divisor-`T`
sample ACVF is the window sum `Σ_s y_s y_{s+k}` of the zero-padded mean-corrected data. -/
private lemma sum_padData_eq_rawACVF {T : ℕ} (x : Fin T → ℝ) (k : ℤ) {S : Finset ℤ}
    (hS : Finset.Ico (0 : ℤ) (T : ℤ) ⊆ S) :
    ∑ s ∈ S, padData x s * padData x (s + k) = rawACVF x k.natAbs := by
  rw [sum_padData_window x k hS]
  by_cases hk : 0 ≤ k
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = (m : ℤ) := ⟨k.toNat, by omega⟩
    rw [show ((m : ℤ)).natAbs = m from by omega]
    exact sum_padData_ico x m
  · rw [sum_padData_symm x k]
    obtain ⟨m, hm⟩ : ∃ m : ℕ, -k = (m : ℤ) := ⟨(-k).toNat, by omega⟩
    rw [hm, show k.natAbs = m from by omega]
    exact sum_padData_ico x m

/-- The shifted form of `sum_padData_eq_rawACVF`, on an explicit integer window. -/
private lemma sum_padData_shift {T : ℕ} (x : Fin T → ℝ) (b k A B : ℤ)
    (hA : A + b ≤ 0) (hB : (T : ℤ) ≤ B + b) :
    ∑ s ∈ Finset.Ico A B, padData x (s + b) * padData x (s + b + k) = rawACVF x k.natAbs := by
  rw [← sum_padData_eq_rawACVF x k (S := Finset.Ico (A + b) (B + b))
      (by intro s hs; simp only [Finset.mem_Ico] at *; omega)]
  refine Finset.sum_nbij' (fun s => s + b) (fun u => u - b) ?_ ?_ ?_ ?_ ?_
  · intro s hs; simp only [Finset.mem_Ico] at *; omega
  · intro u hu; simp only [Finset.mem_Ico] at *; omega
  · intro s _; ring
  · intro u _; ring
  · intro s _; rfl

/-- **FY §2.2.2 (eq. (2.23) claim)**: the divisor-`T` sample ACVF, extended evenly to
`ℤ` (it vanishes at lags `≥ T`), is a positive semidefinite sequence — the property
that fails for the `1/(T−k)` divisor. Deterministic. -/
theorem isPosSemidefSeq_sampleACVF {T : ℕ} (x : Fin T → ℝ) :
    IsPosSemidefSeq fun k : ℤ => sampleACVF x k.natAbs := by
  intro n t a
  -- a bound on the time points, giving one window `[−M, T+M)` that carries every shift
  obtain ⟨M, hM⟩ : ∃ M : ℤ, ∀ i, -M ≤ t i ∧ t i ≤ M := by
    refine ⟨∑ i, |t i|, fun i => ?_⟩
    have h1 : |t i| ≤ ∑ i, |t i| :=
      Finset.single_le_sum (f := fun i => |t i|) (fun j _ => abs_nonneg (t j)) (Finset.mem_univ i)
    have h2 := neg_abs_le (t i)
    have h3 := le_abs_self (t i)
    omega
  -- each entry of the quadratic form is a window sum of the padded data
  have key : ∀ i j : Fin n,
      sampleACVF x (t i - t j).natAbs
        = (T : ℝ)⁻¹ * ∑ s ∈ Finset.Ico (-M) ((T : ℤ) + M),
            padData x (s + t i) * padData x (s + t j) := by
    intro i j
    rw [sampleACVF_eq_raw]
    congr 1
    rw [← sum_padData_shift x (t j) (t i - t j) (-M) ((T : ℤ) + M)
      (by have := hM j; omega) (by have := hM j; omega)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [show s + t j + (t i - t j) = s + t i from by ring, mul_comm]
  -- the quadratic form is a sum of squares
  have main : (T : ℝ)⁻¹ * ∑ s ∈ Finset.Ico (-M) ((T : ℤ) + M),
        (∑ i, a i * padData x (s + t i)) ^ 2
      = ∑ i, ∑ j, a i * a j * sampleACVF x (t i - t j).natAbs := by
    have e1 : ∀ s : ℤ, (∑ i, a i * padData x (s + t i)) ^ 2
        = ∑ i, ∑ j, (a i * padData x (s + t i)) * (a j * padData x (s + t j)) := by
      intro s; rw [sq, Fintype.sum_mul_sum]
    calc (T : ℝ)⁻¹ * ∑ s ∈ Finset.Ico (-M) ((T : ℤ) + M),
            (∑ i, a i * padData x (s + t i)) ^ 2
        = (T : ℝ)⁻¹ * ∑ s ∈ Finset.Ico (-M) ((T : ℤ) + M), ∑ i, ∑ j,
            (a i * padData x (s + t i)) * (a j * padData x (s + t j)) := by
          rw [Finset.sum_congr rfl (fun s _ => e1 s)]
      _ = (T : ℝ)⁻¹ * ∑ i, ∑ j, ∑ s ∈ Finset.Ico (-M) ((T : ℤ) + M),
            (a i * padData x (s + t i)) * (a j * padData x (s + t j)) := by
          congr 1
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ j, a i * a j * sampleACVF x (t i - t j).natAbs := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [key i j, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => by ring
  rw [← main]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun s _ => sq_nonneg _)

/-! ### The MA(q) second-order structure

The MA(q) recurrence is a single finite lag combination `X_t = Σ_{i≤q} c_i ε_{t−i}` of the
innovations, with the coefficient vector `c = (1, a₁, …, a_q)` independent of `t`. All the
second-order facts below (stationarity, `γ(0)`) are read off the one bilinear covariance
computation `cov_eq_of_ma`, whose value depends on `(s, t)` only through `s − t`. -/

/-- Covariance only sees the a.e. class of each argument (private copy of the
`Models/Linear.lean` helper). -/
private lemma covariance_congr_ae {X X' Y Y' : Ω → ℝ} (hX : X =ᵐ[μ] X') (hY : Y =ᵐ[μ] Y') :
    cov[X, Y; μ] = cov[X', Y'; μ] := by
  have hIX : ∫ x, X x ∂μ = ∫ x, X' x ∂μ := integral_congr_ae hX
  have hIY : ∫ x, Y x ∂μ = ∫ x, Y' x ∂μ := integral_congr_ae hY
  simp only [covariance, hIX, hIY]
  exact integral_congr_ae (by filter_upwards [hX, hY] with ω h1 h2 using by rw [h1, h2])

/-- The MA(q) coefficient vector `(1, a₁, …, a_q)`. -/
private def maCoeff {q : ℕ} (a : Fin q → ℝ) : Fin (q + 1) → ℝ := Fin.cases 1 a

private lemma maCoeff_zero {q : ℕ} (a : Fin q → ℝ) : maCoeff a 0 = 1 := rfl

private lemma maCoeff_succ {q : ℕ} (a : Fin q → ℝ) (i : Fin q) : maCoeff a i.succ = a i := rfl

/-- The MA(q) recurrence packaged as a single lag combination with a `t`-independent
coefficient vector. -/
private lemma IsMA.rec_sum {q : ℕ} {a : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsMA a σ2 X ε μ) (u : ℤ) :
    X u =ᵐ[μ] fun ω => ∑ i : Fin (q + 1), maCoeff a i * ε (u - ((i : ℕ) : ℤ)) ω := by
  have hlag : ∀ i : Fin q, u - ((((i.succ : Fin (q + 1)) : ℕ) : ℤ)) = u - 1 - ((i : ℕ) : ℤ) := by
    intro i; rw [Fin.val_succ]; push_cast; ring
  filter_upwards [h.recurrence u] with ω hω
  rw [hω, Fin.sum_univ_succ]
  simp only [maCoeff_zero, maCoeff_succ, Fin.val_zero, Nat.cast_zero, sub_zero, one_mul,
    hlag, Finset.univ_eq_empty, Finset.sum_empty, zero_add]

/-- Bilinear expansion of the covariance of two finite linear combinations of white noise:
only coinciding time indices contribute, each with weight `σ²`. -/
private lemma cov_noise_comb [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ} {σ2 : ℝ}
    (hw : IsWhiteNoise ε σ2 μ) {n m : ℕ} (c : Fin n → ℝ) (d : Fin m → ℝ)
    (u : Fin n → ℤ) (v : Fin m → ℤ) :
    cov[fun ω => ∑ i, c i * ε (u i) ω, fun ω => ∑ j, d j * ε (v j) ω; μ]
      = ∑ i, ∑ j, if u i = v j then c i * d j * σ2 else 0 := by
  rw [covariance_fun_sum_fun_sum (X := fun i ω => c i * ε (u i) ω)
      (Y := fun j ω => d j * ε (v j) ω)
      (fun i => (hw.memLp (u i)).const_mul (c i))
      (fun j => (hw.memLp (v j)).const_mul (d j))]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [covariance_const_mul_left, covariance_const_mul_right]
  by_cases hij : u i = v j
  · rw [if_pos hij, hij, covariance_self (hw.memLp (v j)).aestronglyMeasurable.aemeasurable,
      hw.variance_eq]
    ring
  · rw [if_neg hij, hw.uncorrelated _ _ hij]
    ring

/-- The general two-time MA(q) covariance: a finite sum over the coinciding lag pairs. -/
private lemma IsMA.cov_eq_of_ma [IsProbabilityMeasure μ] {q : ℕ} {a : Fin q → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (h : IsMA a σ2 X ε μ) (s t : ℤ) :
    cov[X s, X t; μ]
      = ∑ i : Fin (q + 1), ∑ j : Fin (q + 1),
          if s - ((i : ℕ) : ℤ) = t - ((j : ℕ) : ℤ) then maCoeff a i * maCoeff a j * σ2 else 0 := by
  rw [covariance_congr_ae (h.rec_sum s) (h.rec_sum t)]
  exact cov_noise_comb h.whiteNoise _ _ _ _

/-- Each MA(q) marginal is in `L²`. -/
private lemma IsMA.memLp_two [IsProbabilityMeasure μ] {q : ℕ} {a : Fin q → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (h : IsMA a σ2 X ε μ) (t : ℤ) : MemLp (X t) 2 μ :=
  MemLp.ae_eq (h.rec_sum t).symm
    (memLp_finset_sum Finset.univ fun i _ =>
      (h.whiteNoise.memLp (t - ((i : ℕ) : ℤ))).const_mul (maCoeff a i))

/-- The MA(q) mean is zero at every time. -/
private lemma IsMA.integral_eq_zero [IsProbabilityMeasure μ] {q : ℕ} {a : Fin q → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (h : IsMA a σ2 X ε μ) (t : ℤ) : ∫ ω, X t ω ∂μ = 0 := by
  rw [integral_congr_ae (h.rec_sum t),
    integral_finset_sum (Finset.univ : Finset (Fin (q + 1))) (fun (i : Fin (q + 1)) _ =>
      ((h.whiteNoise.memLp (t - ((i : ℕ) : ℤ))).integrable one_le_two).const_mul (maCoeff a i))]
  simp [integral_const_mul, h.whiteNoise.integral_eq_zero]

/-- An MA(q) process (finite MA of white noise) is weakly stationary. (Stated here for
the (2.27) assembly; candidate for promotion to `Models/Linear.lean`.) -/
theorem IsMA.isStationary [IsProbabilityMeasure μ] {q : ℕ} {a : Fin q → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (h : IsMA a σ2 X ε μ) (hmeas : ∀ t, Measurable (X t)) :
    IsStationary X μ := by
  refine ⟨h.memLp_two, fun s t => by rw [h.integral_eq_zero s, h.integral_eq_zero t],
    fun t k => ?_⟩
  rw [h.cov_eq_of_ma (t + k) t, h.cov_eq_of_ma k 0]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  refine if_congr ⟨fun hc => by omega, fun hc => by omega⟩ rfl rfl

/-- The MA(q) lag-0 autocovariance: `γ(0) = σ²(1 + Σ_j a_j²)` (FY eq. (2.18)
specialized; positivity of `γ(0)` for `σ² > 0` follows). -/
theorem IsMA.acvf_zero_eq [IsProbabilityMeasure μ] {q : ℕ} {a : Fin q → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (h : IsMA a σ2 X ε μ) :
    acvf X μ 0 = σ2 * (1 + ∑ j, a j ^ 2) := by
  rw [acvf, h.cov_eq_of_ma 0 0]
  have hdiag : ∀ i j : Fin (q + 1),
      ((0 : ℤ) - ((i : ℕ) : ℤ) = 0 - ((j : ℕ) : ℤ)) ↔ i = j := by
    intro i j
    constructor
    · intro hc; exact Fin.val_injective (by omega)
    · rintro rfl; rfl
  have hinner : ∀ i : Fin (q + 1),
      (∑ j : Fin (q + 1),
        if (0 : ℤ) - ((i : ℕ) : ℤ) = 0 - ((j : ℕ) : ℤ) then maCoeff a i * maCoeff a j * σ2 else 0)
        = maCoeff a i * maCoeff a i * σ2 := by
    intro i
    rw [Finset.sum_congr rfl (fun j _ =>
      if_congr (hdiag i j) rfl rfl), Finset.sum_ite_eq Finset.univ i]
    simp
  rw [Finset.sum_congr rfl (fun i _ => hinner i), Fin.sum_univ_succ]
  simp only [maCoeff_zero, maCoeff_succ, one_mul, mul_add, mul_one, Finset.mul_sum]
  refine congrArg (fun z => σ2 + z) (Finset.sum_congr rfl fun i _ => by ring)

/-! ## The sample-mean CLT (FY Theorem 2.8(i))

The route is the truncation route of B&D §7.3, but the m-dependent blocking step is
*unnecessary*: for a **finite** filter window the partial sum `Σ_{t≤T} Σ_{|k|≤N} a_k ε_{t−k}`
regroups (`sum_window_swap`) into `Σ_n c_{n,T} ε_{n+1−N}`, an exactly weighted sum of
**independent** innovations, so the Lindeberg triangular-array CLT applies directly. The
window coefficients equal `Σ_{|k|≤N} a_k` on the bulk and are uniformly bounded on the
`4N` boundary indices, giving the row-variance limit `σ²(Σ_{|k|≤N} a_k)²`. The truncation
level is then removed by an `L²` defect bound that is **uniform in `T`**: the `ℓ¹` energy
budget `Σ_n c_n² ≤ (max_n |c_n|)(Σ_n |c_n|) ≤ B · (T B)` converts the `ℓ¹` tail mass
`B = Σ_{|k|>N}|a_k|` of the filter into `‖·‖₂ ≤ √σ² B`, free of `T`. A three-`ε`
characteristic-function argument closes the double limit. -/

/-- The weight attached to the innovation `ε_{n+1−M}` when the window-`M` truncated
filter is summed over the data window `t = 1, …, T`. -/
private noncomputable def winCoef (b : ℤ → ℝ) (T M n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
    if 1 ≤ (n : ℤ) + 1 - (M : ℤ) + k ∧ (n : ℤ) + 1 - (M : ℤ) + k ≤ (T : ℤ) then b k else 0

/-- **The window swap**: summing a window-`M` finite filter over the data window
`t = 1, …, T` regroups it as a weighted sum of the *inputs* `F(n + 1 − M)`,
`n = 0, …, T + 2M − 1`. Deterministic; used with `F = ε · ω` and with `F = 1`. -/
private lemma sum_window_swap (b : ℤ → ℝ) (F : ℤ → ℝ) (T M : ℕ) :
    ∑ t ∈ Finset.range T, ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), b k * F ((t : ℤ) + 1 - k)
      = ∑ n ∈ Finset.range (T + 2 * M), winCoef b T M n * F ((n : ℤ) + 1 - (M : ℤ)) := by
  classical
  have hR : ∀ n ∈ Finset.range (T + 2 * M),
      winCoef b T M n * F ((n : ℤ) + 1 - (M : ℤ))
        = ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
            (if 1 ≤ (n : ℤ) + 1 - (M : ℤ) + k ∧ (n : ℤ) + 1 - (M : ℤ) + k ≤ (T : ℤ) then
              b k * F ((n : ℤ) + 1 - (M : ℤ)) else 0) := by
    intro n _
    rw [winCoef, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by split <;> simp
  rw [Finset.sum_congr rfl hR, Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_Icc] at hk
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = (M : ℤ) - k := ⟨((M : ℤ) - k).toNat, by omega⟩
  have hdle : d ≤ 2 * M := by omega
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun t => t + d) (fun n => n - d) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [Finset.mem_range] at ht
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_, ?_⟩ <;> push_cast <;> omega
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    simp only [Finset.mem_range]
    have h1 : (1 : ℤ) ≤ (n : ℤ) + 1 - (M : ℤ) + k := hn.2.1
    have h2 : (n : ℤ) + 1 - (M : ℤ) + k ≤ (T : ℤ) := hn.2.2
    omega
  · intro t _; dsimp only; omega
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    have h1 : (1 : ℤ) ≤ (n : ℤ) + 1 - (M : ℤ) + k := hn.2.1
    dsimp only
    omega
  · intro t ht
    dsimp only
    congr 2
    push_cast
    omega

/-- Each window weight is bounded by the total mass of the filter. -/
private lemma abs_winCoef_le (b : ℤ → ℝ) (T M n : ℕ) :
    |winCoef b T M n| ≤ ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |b k| := by
  rw [winCoef]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  split
  · exact le_rfl
  · simp

/-- The window weights have total mass at most `T ·Σ|b|`: the `ℓ¹` energy budget. -/
private lemma sum_abs_winCoef_le (b : ℤ → ℝ) (T M : ℕ) :
    ∑ n ∈ Finset.range (T + 2 * M), |winCoef b T M n|
      ≤ (T : ℝ) * ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |b k| := by
  have habs : ∀ n, |winCoef b T M n| ≤ winCoef (fun k => |b k|) T M n := by
    intro n
    rw [winCoef, winCoef]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    split
    · exact le_rfl
    · simp
  have hswap := sum_window_swap (fun k => |b k|) (fun _ => (1 : ℝ)) T M
  simp only [mul_one] at hswap
  calc ∑ n ∈ Finset.range (T + 2 * M), |winCoef b T M n|
      ≤ ∑ n ∈ Finset.range (T + 2 * M), winCoef (fun k => |b k|) T M n :=
        Finset.sum_le_sum fun n _ => habs n
    _ = ∑ t ∈ Finset.range T, ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |b k| := hswap.symm
    _ = (T : ℝ) * ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |b k| := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- A finite weighted sum of *distinct* white-noise coordinates is in `L²`. -/
private lemma memLp_weighted_noise [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ} {σ2 : ℝ}
    (hw : IsWhiteNoise ε σ2 μ) {K : ℕ} (c : Fin K → ℝ) (g : Fin K → ℤ) :
    MemLp (fun ω => ∑ i, c i * ε (g i) ω) 2 μ :=
  memLp_finset_sum Finset.univ fun i _ => (hw.memLp (g i)).const_mul (c i)

/-- **The second-moment identity** for a weighted sum of distinct white-noise
coordinates: `E(Σ cᵢ ε_{gᵢ})² = σ² Σ cᵢ²`. -/
private lemma integral_sq_weighted_noise [IsProbabilityMeasure μ] {ε : ℤ → Ω → ℝ} {σ2 : ℝ}
    (hw : IsWhiteNoise ε σ2 μ) {K : ℕ} (c : Fin K → ℝ) (g : Fin K → ℤ)
    (hg : Function.Injective g) :
    ∫ ω, (∑ i, c i * ε (g i) ω) ^ 2 ∂μ = σ2 * ∑ i, (c i) ^ 2 := by
  have hmem : MemLp (fun ω => ∑ i, c i * ε (g i) ω) 2 μ := memLp_weighted_noise hw c g
  have hmean : ∫ ω, (∑ i, c i * ε (g i) ω) ∂μ = 0 := by
    rw [integral_finset_sum Finset.univ fun i _ =>
      ((hw.memLp (g i)).integrable one_le_two).const_mul (c i)]
    simp [integral_const_mul, hw.integral_eq_zero]
  have hvar : variance (fun ω => ∑ i, c i * ε (g i) ω) μ = σ2 * ∑ i, (c i) ^ 2 := by
    rw [← covariance_self hmem.aestronglyMeasurable.aemeasurable, cov_noise_comb hw c c g g]
    have hinner : ∀ i : Fin K,
        (∑ j, if g i = g j then c i * c j * σ2 else 0) = c i * c i * σ2 := by
      intro i
      rw [Finset.sum_congr rfl (fun j _ =>
        if_congr ⟨fun hc => hg hc, fun hc => by rw [hc]⟩ rfl rfl),
        Finset.sum_ite_eq Finset.univ i]
      simp
    rw [Finset.sum_congr rfl fun i _ => hinner i, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have := variance_eq_sub hmem
  rw [hvar, hmean] at this
  simp only [Pi.pow_apply] at this
  linarith [this]

/-- **CLT for weighted sums of an i.i.d. sequence** (charFun form). The rows are
`X_{n,i} = w_{n,i} Y_i`; the row-variance limit `v` and the individual negligibility of
the weights are the only inputs beyond the sampling law. -/
private lemma tendsto_charFun_weighted_iid' [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {kk : ℕ → ℕ} {w : (n : ℕ) → Fin (kk n) → ℝ} {σ2 v : ℝ}
    (hmeasY : ∀ i, Measurable (Y i))
    (hindepY : iIndepFun Y μ)
    (hidentY : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    (hL2Y : MemLp (Y 0) 2 μ)
    (hmeanY : ∫ ω, Y 0 ω ∂μ = 0)
    (hvarY : variance (Y 0) μ = σ2) (hσ2 : 0 < σ2)
    (hS : Tendsto (fun n => σ2 * ∑ i, (w n i) ^ 2) atTop (𝓝 v))
    (hneg : ∀ c : ℝ, 0 < c → ∀ᶠ n in atTop, ∀ i, (w n i) ^ 2 ≤ c)
    (u : ℝ) :
    Tendsto (fun n => charFun (μ.map fun ω => ∑ i, w n i * Y (i : ℕ) ω) u) atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal v)) u)) := by
  obtain ⟨X, hXdef⟩ : ∃ X : (n : ℕ) → Fin (kk n) → Ω → ℝ,
      X = fun n i ω => w n i * Y (i : ℕ) ω := ⟨_, rfl⟩
  -- Row regularity.
  have hmeas' : ∀ n i, Measurable (X n i) := by
    intro n i; simp only [hXdef]; exact (hmeasY ↑i).const_mul _
  have hL2' : ∀ n i, MemLp (X n i) 2 μ := by
    intro n i; simp only [hXdef]; exact ((hidentY ↑i).symm.memLp_snd hL2Y).const_mul _
  have hmean' : ∀ n i, ∫ ω, X n i ω ∂μ = 0 := by
    intro n i; simp only [hXdef]
    rw [integral_const_mul, ((hidentY ↑i).integral_eq).trans hmeanY, mul_zero]
  have hindep' : ∀ n, iIndepFun (X n) μ := by
    intro n
    have h1 : iIndepFun (fun i : Fin (kk n) => Y (↑i : ℕ)) μ :=
      iIndepFun.precomp Fin.val_injective hindepY
    have h2 := h1.comp (fun i : Fin (kk n) => fun y : ℝ => w n i * y)
      (fun i => measurable_id.const_mul _)
    refine (iIndepFun_congr (fun i => ?_)).2 h2
    filter_upwards with ω; simp only [hXdef, Function.comp]
  -- Row variances.
  have hvar' : Tendsto (fun n => ∑ i, variance (X n i) μ) atTop (𝓝 v) := by
    have hVi : ∀ n i, variance (X n i) μ = (w n i) ^ 2 * σ2 := by
      intro n i; simp only [hXdef]
      rw [variance_const_mul, (hidentY ↑i).variance_eq, hvarY]
    have hcongr : (fun n => ∑ i, variance (X n i) μ)
        = fun n => σ2 * ∑ i, (w n i) ^ 2 := by
      funext n; simp_rw [hVi]; rw [← Finset.sum_mul]; ring
    rw [hcongr]; exact hS
  -- The `L²`-tail of the sampling law vanishes.
  have hsq0 : Integrable (fun ω => (Y 0 ω) ^ 2) μ := hL2Y.integrable_sq
  obtain ⟨tail, htaildef⟩ : ∃ tail : ℕ → ℝ,
      tail = fun (K : ℕ) => ∫ ω in {ω | (K : ℝ) ≤ |Y 0 ω|}, (Y 0 ω) ^ 2 ∂μ := ⟨_, rfl⟩
  have hsmK : ∀ (j K : ℕ), MeasurableSet {ω | (K : ℝ) ≤ |Y j ω|} := fun j K =>
    measurableSet_le measurable_const (hmeasY j).abs
  have htail0 : Tendsto tail atTop (𝓝 0) := by
    simp only [htaildef]
    have hanti : Antitone fun K : ℕ => {ω | (K : ℝ) ≤ |Y 0 ω|} := by
      intro a b hab ω hω
      simp only [Set.mem_setOf_eq] at hω ⊢
      exact le_trans (by exact_mod_cast hab) hω
    have hint : ∃ K : ℕ, IntegrableOn (fun ω => (Y 0 ω) ^ 2) {ω | (K : ℝ) ≤ |Y 0 ω|} μ :=
      ⟨0, hsq0.integrableOn⟩
    have hlim := tendsto_setIntegral_of_antitone (fun K => hsmK 0 K) hanti hint
    have hempty : ⋂ K : ℕ, {ω | (K : ℝ) ≤ |Y 0 ω|} = ∅ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
        not_forall, not_le]
      obtain ⟨K, hK⟩ := exists_nat_gt |Y 0 ω|
      exact ⟨K, hK⟩
    rw [hempty] at hlim
    simpa using hlim
  -- Identically-distributed coordinates share the same tail integral.
  have htaileq : ∀ (i K : ℕ),
      ∫ ω in {ω | (K : ℝ) ≤ |Y i ω|}, (Y i ω) ^ 2 ∂μ = tail K := by
    intro i K
    have hg : Measurable fun y : ℝ => if (K : ℝ) ≤ |y| then y ^ 2 else 0 :=
      Measurable.ite (measurableSet_le measurable_const measurable_id.abs)
        (measurable_id.pow_const 2) measurable_const
    have hcomp : ∀ j : ℕ, ∫ ω, (if (K : ℝ) ≤ |Y j ω| then (Y j ω) ^ 2 else 0) ∂μ
        = ∫ ω in {ω | (K : ℝ) ≤ |Y j ω|}, (Y j ω) ^ 2 ∂μ := by
      intro j
      rw [← integral_indicator (hsmK j K)]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      by_cases h : (K : ℝ) ≤ |Y j ω| <;> simp [Set.indicator, h]
    simp only [htaildef]
    rw [← hcomp i, ← hcomp 0]
    simpa [Function.comp] using ((hidentY i).comp hg).integral_eq
  -- Bounded row weight energy (from the convergent row variances).
  have henergy : ∀ᶠ n in atTop, ∑ i, (w n i) ^ 2 ≤ (|v| + 1) / σ2 := by
    filter_upwards [hS.eventually_le_const (show v < |v| + 1 by
      have := le_abs_self v; linarith)] with n hn
    rw [le_div_iff₀ hσ2, mul_comm]
    exact hn
  -- Lindeberg's condition for the (closed-set) triangular array.
  have hlin : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => ∑ i, ∫ ω in {ω | ε ≤ |X n i ω|}, (X n i ω) ^ 2 ∂μ) atTop (𝓝 0) := by
    intro ε hε
    refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
    · refine Eventually.of_forall fun n => hb.trans_le (Finset.sum_nonneg fun i _ => ?_)
      exact setIntegral_nonneg (measurableSet_le measurable_const (hmeas' n i).abs)
        fun ω _ => sq_nonneg _
    · -- Pick a truncation level `K` making the shared tail small, then use negligibility.
      have hEpos : (0 : ℝ) < (|v| + 1) / σ2 + 1 := by
        have : (0 : ℝ) ≤ (|v| + 1) / σ2 := by positivity
        linarith
      obtain ⟨K, hKtail, hK1⟩ :=
        (((tendsto_order.1 htail0).2 (b / ((|v| + 1) / σ2 + 1))
          (div_pos hb hEpos)).and (eventually_ge_atTop 1)).exists
      have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
      filter_upwards [hneg ((ε / K) ^ 2) (by positivity), henergy] with n hn hnE
      have haik : ∀ i, |w n i| ≤ ε / K := by
        intro i
        calc |w n i| = Real.sqrt ((w n i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
          _ ≤ Real.sqrt ((ε / K) ^ 2) := Real.sqrt_le_sqrt (hn i)
          _ = ε / K := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
      have hterm : ∀ i, ∫ ω in {ω | ε ≤ |X n i ω|}, (X n i ω) ^ 2 ∂μ
          ≤ (w n i) ^ 2 * tail K := by
        intro i
        have hXsq : ∀ ω, (X n i ω) ^ 2 = (w n i) ^ 2 * (Y (↑i : ℕ) ω) ^ 2 := by
          intro ω; simp only [hXdef]; rw [mul_pow]
        rw [setIntegral_congr_fun (measurableSet_le measurable_const (hmeas' n i).abs)
              (fun ω _ => hXsq ω), integral_const_mul]
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        rw [← htaileq (↑i) K]
        refine setIntegral_mono_set
          (((hidentY ↑i).symm.memLp_snd hL2Y).integrable_sq).integrableOn
          (Eventually.of_forall fun ω => sq_nonneg _) (Eventually.of_forall fun ω hω => ?_)
        have h1 : ε ≤ |w n i| * |Y (↑i : ℕ) ω| := by
          rw [← abs_mul]; simpa only [hXdef] using hω
        have h3 : ε ≤ (ε / K) * |Y (↑i : ℕ) ω| :=
          le_trans h1 (mul_le_mul_of_nonneg_right (haik i) (abs_nonneg _))
        change (K : ℝ) ≤ |Y (↑i : ℕ) ω|
        by_contra hcon
        have hle : (ε / K) * |Y (↑i : ℕ) ω| < (ε / K) * K :=
          mul_lt_mul_of_pos_left (not_le.1 hcon) (by positivity)
        rw [div_mul_cancel₀ ε (ne_of_gt hKpos)] at hle
        exact absurd (lt_of_le_of_lt h3 hle) (lt_irrefl ε)
      have htailnn : 0 ≤ tail K := by
        rw [htaildef]; exact setIntegral_nonneg (hsmK 0 K) fun ω _ => sq_nonneg _
      calc ∑ i, ∫ ω in {ω | ε ≤ |X n i ω|}, (X n i ω) ^ 2 ∂μ
          ≤ ∑ i, (w n i) ^ 2 * tail K := Finset.sum_le_sum fun i _ => hterm i
        _ = (∑ i, (w n i) ^ 2) * tail K := by rw [← Finset.sum_mul]
        _ ≤ ((|v| + 1) / σ2 + 1) * tail K := by
            refine mul_le_mul_of_nonneg_right (by linarith) htailnn
        _ < b := by
            have := (mul_lt_mul_of_pos_left hKtail hEpos)
            rwa [mul_div_cancel₀ b (ne_of_gt hEpos)] at this
  have hmain :=
    tendsto_charFun_rowSum_gaussian_of_lindeberg hmeas' hindep' hmean' hL2' hvar' hlin u
  simpa only [hXdef] using hmain

/-! ### `L²` bookkeeping and the characteristic-function comparison -/

/-- `L²` control from a second-moment bound. -/
private lemma eLpNorm_two_le_of_integral_sq_le {f : Ω → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : MemLp f 2 μ) (h : ∫ ω, f ω ^ 2 ∂μ ≤ C ^ 2) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal C := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hpow : ∀ ω, ‖f ω‖ ^ ((2 : ENNReal).toReal) = f ω ^ 2 := by
    intro ω
    rw [show ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.norm_eq_abs, sq_abs]
  rw [integral_congr_ae (Eventually.of_forall hpow),
    show ((2 : ENNReal).toReal)⁻¹ = 1 / (2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow]
  calc Real.sqrt (∫ ω, f ω ^ 2 ∂μ) ≤ Real.sqrt (C ^ 2) := Real.sqrt_le_sqrt h
    _ = C := Real.sqrt_sq hC

/-- On a probability space an `L²` bound controls the `L¹` norm. -/
private lemma integral_abs_le_of_eLpNorm_two [IsProbabilityMeasure μ] {f : Ω → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hf : AEStronglyMeasurable f μ) (h : eLpNorm f 2 μ ≤ ENNReal.ofReal C) :
    ∫ ω, |f ω| ∂μ ≤ C := by
  have h1 : ∫ ω, |f ω| ∂μ = (∫⁻ ω, ‖f ω‖ₑ ∂μ).toReal := by
    simpa [Real.norm_eq_abs] using integral_norm_eq_lintegral_enorm hf
  have h2 : eLpNorm f 1 μ ≤ ENNReal.ofReal C :=
    le_trans (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hf) h
  rw [eLpNorm_one_eq_lintegral_enorm] at h2
  rw [h1]
  calc (∫⁻ ω, ‖f ω‖ₑ ∂μ).toReal ≤ (ENNReal.ofReal C).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
    _ = C := ENNReal.toReal_ofReal hC

/-- charFun of a pushforward, as an integral on the base space. -/
private lemma charFun_map_eq_integral' {f : Ω → ℝ} (hf : AEMeasurable f μ) (u : ℝ) :
    charFun (μ.map f) u = ∫ ω, Complex.exp (Complex.I * (u * f ω : ℝ)) ∂μ := by
  rw [charFun_apply_real, integral_map hf (by fun_prop)]
  simp only [Complex.ofReal_mul]
  congr 1 with ω
  ring_nf

private lemma integrable_cexp_mul_I' [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f) :
    Integrable (fun ω => Complex.exp (Complex.I * (f ω : ℝ))) μ := by
  refine (integrable_const (1 : ℝ)).mono'
    (Complex.measurable_exp.comp (by fun_prop)).aestronglyMeasurable ?_
  filter_upwards with ω
  simp [Complex.norm_exp]

/-- **The `L¹` charFun comparison**: `‖E e^{iuZ} − E e^{iuW}‖ ≤ |u| E|Z − W|`. -/
private lemma norm_charFun_map_sub_le [IsProbabilityMeasure μ] {Z W : Ω → ℝ}
    (hZ : Measurable Z) (hW : Measurable W)
    (hint : Integrable (fun ω => |Z ω - W ω|) μ) (u : ℝ) :
    ‖charFun (μ.map Z) u - charFun (μ.map W) u‖ ≤ |u| * ∫ ω, |Z ω - W ω| ∂μ := by
  rw [charFun_map_eq_integral' hZ.aemeasurable u, charFun_map_eq_integral' hW.aemeasurable u,
    ← integral_sub (integrable_cexp_mul_I' (hZ.const_mul u))
      (integrable_cexp_mul_I' (hW.const_mul u))]
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [show |u| * ∫ ω, |Z ω - W ω| ∂μ = ∫ ω, |u| * |Z ω - W ω| ∂μ from
    (integral_const_mul _ _).symm]
  refine integral_mono (((integrable_cexp_mul_I' (hZ.const_mul u)).sub
    (integrable_cexp_mul_I' (hW.const_mul u))).norm) (hint.const_mul _) fun ω => ?_
  have hfact : Complex.exp (Complex.I * ((u * Z ω : ℝ)))
        - Complex.exp (Complex.I * ((u * W ω : ℝ)))
      = Complex.exp (Complex.I * ((u * W ω : ℝ))) *
        (Complex.exp (Complex.I * ((u * Z ω - u * W ω : ℝ))) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    push_cast
    ring_nf
  rw [hfact, norm_mul,
    show ‖Complex.exp (Complex.I * ((u * W ω : ℝ)))‖ = 1 from by simp [Complex.norm_exp], one_mul]
  refine le_trans (by simpa using
      Real.norm_exp_I_mul_ofReal_sub_one_le (x := u * Z ω - u * W ω)) ?_
  rw [show u * Z ω - u * W ω = u * (Z ω - W ω) from by ring, abs_mul]

/-! ### The truncated-filter CLT

For a *finite* filter window the partial sum over `t = 1, …, T` is, after the window swap,
an exactly weighted sum of **independent** innovations — no blocking is needed. The row
weights are `T^{-1/2}` times the window coefficients, which equal `Σ_{|k|≤N} a_k` on the
bulk `2N ≤ n < T` and are bounded by `Σ_{|k|≤N}|a_k|` on the `4N` boundary indices. -/

private lemma tendsto_charFun_truncSum [IsProbabilityMeasure μ] {a : ℤ → ℝ} {σ2 : ℝ}
    {ε : ℤ → Ω → ℝ} (hε : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2) (N : ℕ) (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        (Real.sqrt T)⁻¹ * ∑ t ∈ Finset.range T,
          ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε ((t : ℤ) + 1 - k) ω) u)
      atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal
        (σ2 * (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k) ^ 2))) u)) := by
  classical
  have hwn := hε.isWhiteNoise
  obtain ⟨AN, hAN⟩ : ∃ x : ℝ, x = ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k := ⟨_, rfl⟩
  obtain ⟨AA, hAA⟩ : ∃ x : ℝ, x = ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), |a k| := ⟨_, rfl⟩
  have hAAnn : 0 ≤ AA := by rw [hAA]; exact Finset.sum_nonneg fun k _ => abs_nonneg _
  have hginj : Function.Injective fun n : ℕ => (n : ℤ) + 1 - (N : ℤ) := by
    intro p q hpq; simpa using hpq
  -- the innovation reindex `Y n = ε_{n+1−N}`
  have hidentY : ∀ n : ℕ, IdentDistrib (ε ((n : ℤ) + 1 - (N : ℤ)))
      (ε (((0 : ℕ) : ℤ) + 1 - (N : ℤ))) μ μ := fun n => hε.identDistrib _ _
  -- the row weights
  have hsqinv : ∀ T : ℕ, ((Real.sqrt (T : ℝ))⁻¹) ^ 2 = ((T : ℝ))⁻¹ := by
    intro T
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg T)]
  have hrow : ∀ T : ℕ,
      (∑ i : Fin (T + 2 * N), ((Real.sqrt (T : ℝ))⁻¹ * winCoef a T N (i : ℕ)) ^ 2)
        = ((T : ℝ))⁻¹ * ∑ n ∈ Finset.range (T + 2 * N), (winCoef a T N n) ^ 2 := by
    intro T
    rw [Finset.mul_sum,
      ← Fin.sum_univ_eq_sum_range
        (fun n => ((T : ℝ))⁻¹ * (winCoef a T N n) ^ 2) (T + 2 * N)]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_pow, hsqinv T]
  -- the bulk value of the window coefficients
  have hbulk : ∀ T n : ℕ, 2 * N ≤ n → n < T → winCoef a T N n = AN := by
    intro T n h1 h2
    rw [winCoef, hAN]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_Icc] at hk
    exact if_pos ⟨by omega, by omega⟩
  have hbdd : ∀ T n : ℕ, (winCoef a T N n) ^ 2 ≤ AA ^ 2 := by
    intro T n
    have h1 : |winCoef a T N n| ≤ AA := by rw [hAA]; exact abs_winCoef_le a T N n
    calc (winCoef a T N n) ^ 2 = |winCoef a T N n| ^ 2 := (sq_abs _).symm
      _ ≤ AA ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  -- the two-sided bulk/boundary estimate
  have hsand : ∀ T : ℕ, 2 * N ≤ T →
      ((T : ℝ) - 2 * N) * AN ^ 2
          ≤ ∑ n ∈ Finset.range (T + 2 * N), (winCoef a T N n) ^ 2 ∧
        ∑ n ∈ Finset.range (T + 2 * N), (winCoef a T N n) ^ 2
          ≤ ((T : ℝ) - 2 * N) * AN ^ 2 + 4 * N * AA ^ 2 := by
    intro T hT
    have hsub : Finset.Ico (2 * N) T ⊆ Finset.range (T + 2 * N) := by
      intro n hn
      simp only [Finset.mem_Ico] at hn
      simp only [Finset.mem_range]
      omega
    have hsplit := Finset.sum_sdiff (f := fun n => (winCoef a T N n) ^ 2) hsub
    have hIco : ∑ n ∈ Finset.Ico (2 * N) T, (winCoef a T N n) ^ 2
        = ((T : ℝ) - 2 * N) * AN ^ 2 := by
      rw [Finset.sum_congr rfl (fun n hn => by
          simp only [Finset.mem_Ico] at hn
          rw [hbulk T n hn.1 hn.2]), Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      congr 1
      have : ((T - 2 * N : ℕ) : ℝ) = (T : ℝ) - 2 * N := by
        push_cast [Nat.cast_sub hT]; ring
      rw [this]
    have hbdcard : (Finset.range (T + 2 * N) \ Finset.Ico (2 * N) T).card = 4 * N := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.2 hsub, Finset.card_range, Nat.card_Ico]
      omega
    have hbd1 : (0 : ℝ)
        ≤ ∑ n ∈ Finset.range (T + 2 * N) \ Finset.Ico (2 * N) T, (winCoef a T N n) ^ 2 :=
      Finset.sum_nonneg fun n _ => sq_nonneg _
    have hbd2 : ∑ n ∈ Finset.range (T + 2 * N) \ Finset.Ico (2 * N) T, (winCoef a T N n) ^ 2
        ≤ 4 * N * AA ^ 2 := by
      calc ∑ n ∈ Finset.range (T + 2 * N) \ Finset.Ico (2 * N) T, (winCoef a T N n) ^ 2
          ≤ ∑ _n ∈ Finset.range (T + 2 * N) \ Finset.Ico (2 * N) T, AA ^ 2 :=
            Finset.sum_le_sum fun n _ => hbdd T n
        _ = 4 * N * AA ^ 2 := by
            rw [Finset.sum_const, hbdcard, nsmul_eq_mul]
            push_cast
            ring
    exact ⟨by linarith, by linarith⟩
  -- the row-variance limit
  have hTinv : Tendsto (fun T : ℕ => ((T : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hS0 : Tendsto (fun T : ℕ =>
      ((T : ℝ))⁻¹ * ∑ n ∈ Finset.range (T + 2 * N), (winCoef a T N n) ^ 2 - AN ^ 2)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_
      (by simpa using hTinv.mul_const (2 * (N : ℝ) * AN ^ 2 + 4 * (N : ℝ) * AA ^ 2))
    filter_upwards [eventually_ge_atTop (max 1 (2 * N))] with T hT
    have hT1 : 1 ≤ T := le_trans (le_max_left _ _) hT
    have hT2 : 2 * N ≤ T := le_trans (le_max_right _ _) hT
    have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT1
    have hinvnn : (0 : ℝ) ≤ ((T : ℝ))⁻¹ := by positivity
    obtain ⟨h1, h2⟩ := hsand T hT2
    have hkey : ((T : ℝ))⁻¹ * ((T : ℝ) - 2 * N) = 1 - 2 * (N : ℝ) * ((T : ℝ))⁻¹ := by
      field_simp
    have hTne : (T : ℝ) ≠ 0 := ne_of_gt hTpos
    have hL' : ((T : ℝ))⁻¹ * (((T : ℝ) - 2 * (N : ℝ)) * AN ^ 2)
        = AN ^ 2 - 2 * (N : ℝ) * ((T : ℝ))⁻¹ * AN ^ 2 := by field_simp
    have hU' : ((T : ℝ))⁻¹ * ((((T : ℝ) - 2 * (N : ℝ)) * AN ^ 2) + 4 * (N : ℝ) * AA ^ 2)
        = AN ^ 2 - 2 * (N : ℝ) * ((T : ℝ))⁻¹ * AN ^ 2
          + ((T : ℝ))⁻¹ * (4 * (N : ℝ) * AA ^ 2) := by field_simp
    have hR' : ((T : ℝ))⁻¹ * (2 * (N : ℝ) * AN ^ 2 + 4 * (N : ℝ) * AA ^ 2)
        = 2 * (N : ℝ) * ((T : ℝ))⁻¹ * AN ^ 2
          + ((T : ℝ))⁻¹ * (4 * (N : ℝ) * AA ^ 2) := by ring
    have hPnn : (0 : ℝ) ≤ 2 * (N : ℝ) * ((T : ℝ))⁻¹ * AN ^ 2 := by positivity
    have hQnn : (0 : ℝ) ≤ ((T : ℝ))⁻¹ * (4 * (N : ℝ) * AA ^ 2) := by positivity
    rw [Real.norm_eq_abs, abs_le]
    constructor <;>
      linarith [mul_le_mul_of_nonneg_left h1 hinvnn, mul_le_mul_of_nonneg_left h2 hinvnn]
  have hS : Tendsto (fun T : ℕ => σ2 *
      ∑ i : Fin (T + 2 * N), ((Real.sqrt (T : ℝ))⁻¹ * winCoef a T N (i : ℕ)) ^ 2)
      atTop (𝓝 (σ2 * AN ^ 2)) := by
    have h1 : Tendsto (fun T : ℕ =>
        ((T : ℝ))⁻¹ * ∑ n ∈ Finset.range (T + 2 * N), (winCoef a T N n) ^ 2)
        atTop (𝓝 (AN ^ 2)) := by
      have h := hS0.add_const (AN ^ 2)
      rw [zero_add] at h
      exact h.congr fun T => by ring
    have h2 := h1.const_mul σ2
    exact h2.congr fun T => by rw [hrow T]
  -- individual negligibility of the weights
  have hneg : ∀ c : ℝ, 0 < c → ∀ᶠ T : ℕ in atTop, ∀ i : Fin (T + 2 * N),
      ((Real.sqrt (T : ℝ))⁻¹ * winCoef a T N (i : ℕ)) ^ 2 ≤ c := by
    intro c hc
    have h0 : Tendsto (fun T : ℕ => ((T : ℝ))⁻¹ * AA ^ 2) atTop (𝓝 0) := by
      simpa using hTinv.mul_const (AA ^ 2)
    filter_upwards [h0.eventually (eventually_lt_nhds hc)] with T hT i
    have hinvnn : (0 : ℝ) ≤ ((T : ℝ))⁻¹ := by positivity
    rw [mul_pow, hsqinv T]
    nlinarith [hbdd T (i : ℕ), mul_le_mul_of_nonneg_left (hbdd T (i : ℕ)) hinvnn]
  -- the weighted-iid CLT, and the window swap turning it into the statement
  have hmain := tendsto_charFun_weighted_iid'
    (Y := fun n : ℕ => ε ((n : ℤ) + 1 - (N : ℤ)))
    (kk := fun T : ℕ => T + 2 * N)
    (w := fun (T : ℕ) (i : Fin (T + 2 * N)) => (Real.sqrt (T : ℝ))⁻¹ * winCoef a T N (i : ℕ))
    (fun n => hε.measurable _)
    (iIndepFun.precomp hginj hε.iIndep)
    hidentY (hwn.memLp _) (hwn.integral_eq_zero _) (hwn.variance_eq _) hσ hS hneg u
  rw [← hAN]
  refine hmain.congr fun T => ?_
  congr 1
  refine congrArg (fun f : Ω → ℝ => μ.map f) (funext fun ω => ?_)
  rw [sum_window_swap a (fun j => ε j ω) T N, Finset.mul_sum,
    ← Fin.sum_univ_eq_sum_range
      (fun n => (Real.sqrt (T : ℝ))⁻¹ * (winCoef a T N n * ε ((n : ℤ) + 1 - (N : ℤ)) ω))
      (T + 2 * N)]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ### The `L²` defect of a truncation

For a finite filter the normalized partial sum is an `L²`-bounded weighted sum of
independent innovations, and the **`ℓ¹` energy budget** `Σ_n c_n² ≤ (max|c|)(Σ_n|c_n|)
≤ B · T B` turns the `ℓ¹` mass `B` of the filter into a `T`-free `L²` bound. -/

private lemma eLpNorm_windowSum_le [IsProbabilityMeasure μ] {σ2 : ℝ} {ε : ℤ → Ω → ℝ}
    (hw : IsWhiteNoise ε σ2 μ) (hσ : 0 ≤ σ2) (b : ℤ → ℝ) {B : ℝ} (hBnn : 0 ≤ B)
    (T M : ℕ) (hT : 1 ≤ T) (hB : ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |b k| ≤ B) :
    eLpNorm (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), b k * ε ((t : ℤ) + 1 - k) ω) 2 μ
      ≤ ENNReal.ofReal (Real.sqrt σ2 * B) := by
  classical
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  have hginj : Function.Injective fun i : Fin (T + 2 * M) => ((i : ℕ) : ℤ) + 1 - (M : ℤ) := by
    intro p q hpq
    simp only at hpq
    exact Fin.ext (by omega)
  have hpt : (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), b k * ε ((t : ℤ) + 1 - k) ω)
      = fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ i : Fin (T + 2 * M),
          winCoef b T M (i : ℕ) * ε (((i : ℕ) : ℤ) + 1 - (M : ℤ)) ω := by
    funext ω
    rw [sum_window_swap b (fun j => ε j ω) T M,
      ← Fin.sum_univ_eq_sum_range
        (fun n => winCoef b T M n * ε ((n : ℤ) + 1 - (M : ℤ)) ω) (T + 2 * M)]
  rw [hpt]
  have hmemZ : MemLp (fun ω => ∑ i : Fin (T + 2 * M),
      winCoef b T M (i : ℕ) * ε (((i : ℕ) : ℤ) + 1 - (M : ℤ)) ω) 2 μ :=
    memLp_weighted_noise hw _ _
  -- the `ℓ²` energy of the window weights
  have hcsum : ∑ i : Fin (T + 2 * M), (winCoef b T M (i : ℕ)) ^ 2 ≤ (T : ℝ) * B ^ 2 := by
    have h2 : ∀ n : ℕ, (winCoef b T M n) ^ 2 ≤ B * |winCoef b T M n| := by
      intro n
      have h3 := (abs_winCoef_le b T M n).trans hB
      nlinarith [abs_nonneg (winCoef b T M n), sq_abs (winCoef b T M n)]
    calc ∑ i : Fin (T + 2 * M), (winCoef b T M (i : ℕ)) ^ 2
        = ∑ n ∈ Finset.range (T + 2 * M), (winCoef b T M n) ^ 2 :=
          Fin.sum_univ_eq_sum_range (fun n => (winCoef b T M n) ^ 2) (T + 2 * M)
      _ ≤ ∑ n ∈ Finset.range (T + 2 * M), B * |winCoef b T M n| :=
          Finset.sum_le_sum fun n _ => h2 n
      _ = B * ∑ n ∈ Finset.range (T + 2 * M), |winCoef b T M n| := by rw [Finset.mul_sum]
      _ ≤ B * ((T : ℝ) * B) :=
          mul_le_mul_of_nonneg_left
            ((sum_abs_winCoef_le b T M).trans
              (mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg T))) hBnn
      _ = (T : ℝ) * B ^ 2 := by ring
  -- the second moment of the normalized weighted sum
  have hsq : ∫ ω, ((Real.sqrt (T : ℝ))⁻¹ * ∑ i : Fin (T + 2 * M),
        winCoef b T M (i : ℕ) * ε (((i : ℕ) : ℤ) + 1 - (M : ℤ)) ω) ^ 2 ∂μ
      = ((T : ℝ))⁻¹ * (σ2 * ∑ i : Fin (T + 2 * M), (winCoef b T M (i : ℕ)) ^ 2) := by
    have h1 : ∀ ω, ((Real.sqrt (T : ℝ))⁻¹ * ∑ i : Fin (T + 2 * M),
          winCoef b T M (i : ℕ) * ε (((i : ℕ) : ℤ) + 1 - (M : ℤ)) ω) ^ 2
        = ((T : ℝ))⁻¹ * (∑ i : Fin (T + 2 * M),
            winCoef b T M (i : ℕ) * ε (((i : ℕ) : ℤ) + 1 - (M : ℤ)) ω) ^ 2 := by
      intro ω
      rw [mul_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg T)]
    rw [integral_congr_ae (Eventually.of_forall h1), integral_const_mul,
      integral_sq_weighted_noise hw _ _ hginj]
  refine eLpNorm_two_le_of_integral_sq_le (by positivity) (hmemZ.const_mul _) ?_
  rw [hsq, mul_pow, Real.sq_sqrt hσ]
  have h3 : ((T : ℝ))⁻¹ * (σ2 * ∑ i : Fin (T + 2 * M), (winCoef b T M (i : ℕ)) ^ 2)
      ≤ ((T : ℝ))⁻¹ * (σ2 * ((T : ℝ) * B ^ 2)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcsum hσ) (by positivity)
  have h4 : ((T : ℝ))⁻¹ * (σ2 * ((T : ℝ) * B ^ 2)) = σ2 * B ^ 2 := by
    field_simp
  linarith

/-- **The head remainder is `L²`-null**: at a *fixed* sample size `T`, the normalized
partial sum of the filter defects `X_t − m − Σ_{|k|≤M} a_k ε_{t−k}` is a finite sum of
`L²`-null terms, hence vanishes as the truncation level `M` grows. -/
private lemma tendsto_eLpNorm_headRemainder [IsProbabilityMeasure μ] {a : ℤ → ℝ} {m σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (hε : IsIIDNoise ε σ2 μ) (hmeas : ∀ t, Measurable (X t))
    (hfil : ∀ t : ℤ, Tendsto (fun M : ℕ =>
      eLpNorm (fun ω => X t ω - m -
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε (t - k) ω) 2 μ) atTop (𝓝 0))
    (T : ℕ) :
    Tendsto (fun M : ℕ => eLpNorm (fun ω => (Real.sqrt (T : ℝ))⁻¹ *
      ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m -
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω)) 2 μ)
      atTop (𝓝 0) := by
  have hsmul : ∀ (c : ℝ) (g : Ω → ℝ),
      eLpNorm (fun ω => c * g ω) 2 μ = ‖c‖ₑ * eLpNorm g 2 μ := by
    intro c g
    rw [show (fun ω => c * g ω) = c • g from by funext ω; simp, eLpNorm_const_smul]
  have hbound : ∀ M : ℕ,
      eLpNorm (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
        (X ((t : ℤ) + 1) ω - m -
          ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω)) 2 μ
        ≤ ‖(Real.sqrt (T : ℝ))⁻¹‖ₑ * ∑ t ∈ Finset.range T,
            eLpNorm (fun ω => X ((t : ℤ) + 1) ω - m -
              ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω) 2 μ := by
    intro M
    rw [hsmul]
    gcongr
    rw [show (fun ω => ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m -
          ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω))
        = ∑ t ∈ Finset.range T, (fun ω => X ((t : ℤ) + 1) ω - m -
          ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω) from by
      funext ω; simp]
    exact eLpNorm_sum_le (fun t _ =>
      (((hmeas _).sub measurable_const).sub
        (Finset.measurable_sum _ fun k _ =>
          (hε.measurable _).const_mul _)).aestronglyMeasurable) one_le_two
  have hsum0 : Tendsto (fun M : ℕ => ∑ t ∈ Finset.range T,
      eLpNorm (fun ω => X ((t : ℤ) + 1) ω - m -
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω) 2 μ)
      atTop (𝓝 0) := by
    have := tendsto_finset_sum (Finset.range T)
      (fun t (_ : t ∈ Finset.range T) => hfil ((t : ℤ) + 1))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun M => zero_le _) hbound
  have := (ENNReal.Tendsto.const_mul hsum0
    (Or.inr (enorm_ne_top (x := (Real.sqrt (T : ℝ))⁻¹))))
  simpa using this

/-! ### The truncation defect, uniformly in the sample size -/

set_option maxHeartbeats 1000000 in
-- The statement carries several nested `Finset` sums; elaboration needs the larger budget.
private lemma integral_abs_defect_le [IsProbabilityMeasure μ] {a : ℤ → ℝ} {m σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (hε : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (hmeas : ∀ t, Measurable (X t))
    (hfil : ∀ t : ℤ, Tendsto (fun M : ℕ =>
      eLpNorm (fun ω => X t ω - m -
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε (t - k) ω) 2 μ) atTop (𝓝 0))
    {B : ℝ} (hBnn : 0 ≤ B) (N : ℕ)
    (hB : ∀ M : ℕ, N ≤ M →
      ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N : ℤ)) (N : ℤ), |a k| ≤ B)
    (T : ℕ) (hT : 1 ≤ T) :
    Integrable (fun ω => |(Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m)
        - (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
            ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε ((t : ℤ) + 1 - k) ω|) μ ∧
    ∫ ω, |(Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m)
        - (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
            ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε ((t : ℤ) + 1 - k) ω| ∂μ
      ≤ Real.sqrt σ2 * B := by
  classical
  have hwn := hε.isWhiteNoise
  obtain ⟨bco, hbco⟩ : ∃ b : ℤ → ℝ,
      b = fun k => if k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then 0 else a k := ⟨_, rfl⟩
  -- measurability of every piece
  have hmG : ∀ M : ℕ, Measurable (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
      ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), bco k * ε ((t : ℤ) + 1 - k) ω) := fun M =>
    Measurable.const_mul (Finset.measurable_sum _ fun t _ =>
      Finset.measurable_sum _ fun k _ => (hε.measurable _).const_mul _) _
  have hmE : ∀ M : ℕ, Measurable (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
      (X ((t : ℤ) + 1) ω - m -
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω)) := fun M =>
    Measurable.const_mul (Finset.measurable_sum _ fun t _ =>
      ((hmeas _).sub measurable_const).sub
        (Finset.measurable_sum _ fun k _ => (hε.measurable _).const_mul _)) _
  have hmD : Measurable (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
      (X ((t : ℤ) + 1) ω - m)
      - (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
          ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε ((t : ℤ) + 1 - k) ω) := by
    refine Measurable.sub (Measurable.const_mul (Finset.measurable_sum _ fun t _ =>
      (hmeas _).sub measurable_const) _) ?_
    exact Measurable.const_mul (Finset.measurable_sum _ fun t _ =>
      Finset.measurable_sum _ fun k _ => (hε.measurable _).const_mul _) _
  -- the exact splitting `D = E_M + G_M` at every truncation level `M ≥ N`
  have hsplit : ∀ M : ℕ, N ≤ M → ∀ ω,
      (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m)
          - (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
              ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε ((t : ℤ) + 1 - k) ω
        = ((Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
            (X ((t : ℤ) + 1) ω - m -
              ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω))
          + ((Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
              ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), bco k * ε ((t : ℤ) + 1 - k) ω) := by
    intro M hNM ω
    have hsub : Finset.Icc (-(N : ℤ)) (N : ℤ) ⊆ Finset.Icc (-(M : ℤ)) (M : ℤ) := by
      intro k hk
      simp only [Finset.mem_Icc] at *
      omega
    have hkey : ∀ t : ℕ,
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω
          - ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), bco k * ε ((t : ℤ) + 1 - k) ω
        = ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε ((t : ℤ) + 1 - k) ω := by
      intro t
      have hstep := Finset.sum_subset hsub (f := fun k =>
        if k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then a k * ε ((t : ℤ) + 1 - k) ω else 0)
        (fun k _ hk => if_neg hk)
      rw [← Finset.sum_sub_distrib,
        Finset.sum_congr rfl (fun k _ => (show
          a k * ε ((t : ℤ) + 1 - k) ω - bco k * ε ((t : ℤ) + 1 - k) ω
            = if k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then a k * ε ((t : ℤ) + 1 - k) ω else 0 from by
          simp only [hbco]
          by_cases hk : k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) <;> simp [hk])), ← hstep]
      exact Finset.sum_congr rfl fun k hk => if_pos hk
    have hA : ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m)
          - ∑ t ∈ Finset.range T, ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε ((t : ℤ) + 1 - k) ω
        = ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m -
            ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω)
          + ∑ t ∈ Finset.range T,
              ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), bco k * ε ((t : ℤ) + 1 - k) ω := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t _ => by linarith [hkey t]
    linear_combination (Real.sqrt (T : ℝ))⁻¹ * hA
  -- the tail filter has `ℓ¹` mass at most `B`
  have hbcomass : ∀ M : ℕ, N ≤ M →
      ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |bco k| ≤ B := by
    intro M hNM
    have hsub : Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N : ℤ)) (N : ℤ)
        ⊆ Finset.Icc (-(M : ℤ)) (M : ℤ) := Finset.sdiff_subset
    have heq : ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), |bco k|
        = ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N : ℤ)) (N : ℤ), |a k| := by
      rw [← Finset.sum_subset hsub (fun k hk hk' => by
        simp only [Finset.mem_sdiff, not_and, not_not] at hk'
        rw [hbco]
        simp only [if_pos (hk' hk), abs_zero])]
      refine Finset.sum_congr rfl fun k hk => ?_
      simp only [Finset.mem_sdiff] at hk
      rw [hbco]
      simp only [if_neg hk.2]
    rw [heq]
    exact hB M hNM
  -- the tail piece is `L²`-small, uniformly in `T`
  have hGbound : ∀ M : ℕ, N ≤ M →
      eLpNorm (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), bco k * ε ((t : ℤ) + 1 - k) ω) 2 μ
        ≤ ENNReal.ofReal (Real.sqrt σ2 * B) := fun M hNM =>
    eLpNorm_windowSum_le hwn hσ.le bco hBnn T M hT (hbcomass M hNM)
  -- the head piece vanishes as the truncation level grows
  have hE0 := tendsto_eLpNorm_headRemainder hε hmeas hfil T
  -- pass to the limit `M → ∞`
  have hDle : eLpNorm (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
      (X ((t : ℤ) + 1) ω - m)
      - (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
          ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε ((t : ℤ) + 1 - k) ω) 2 μ
      ≤ ENNReal.ofReal (Real.sqrt σ2 * B) := by
    have hlim : Tendsto (fun M : ℕ =>
        eLpNorm (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
          (X ((t : ℤ) + 1) ω - m -
            ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω)) 2 μ
          + ENNReal.ofReal (Real.sqrt σ2 * B)) atTop
        (𝓝 (ENNReal.ofReal (Real.sqrt σ2 * B))) := by
      have := hE0.add (tendsto_const_nhds (x := ENNReal.ofReal (Real.sqrt σ2 * B)))
      simpa using this
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_ge_atTop N] with M hNM
    refine le_trans (le_of_eq (eLpNorm_congr_ae (Eventually.of_forall (hsplit M hNM)))) ?_
    exact le_trans (eLpNorm_add_le (hmE M).aestronglyMeasurable (hmG M).aestronglyMeasurable
      one_le_two) (add_le_add le_rfl (hGbound M hNM))
  have hmemD : MemLp (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
      (X ((t : ℤ) + 1) ω - m)
      - (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
          ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε ((t : ℤ) + 1 - k) ω) 2 μ :=
    ⟨hmD.aestronglyMeasurable, lt_of_le_of_lt hDle ENNReal.ofReal_lt_top⟩
  exact ⟨(hmemD.integrable one_le_two).abs,
    integral_abs_le_of_eLpNorm_two (by positivity) hmD.aestronglyMeasurable hDle⟩

/-- **FY Theorem 2.8(i) — DEBT (ledger (a); proof route: m-dependent approximation +
iid CLT, B&D 1991 §7.3)**: sample-mean CLT for a two-sided linear process
`X_t = m + Σ_{k∈ℤ} a_k ε_{t−k}` with IID(0, σ²) innovations and `Σ_k a_k ≠ 0`:
`√T (X̄_T − m) →d N(0, σ²(Σ_k a_k)²)`. -/
theorem sampleMean_clt_debt [IsProbabilityMeasure μ] {a : ℤ → ℝ} {m σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ}
    -- USER-INPUT: IID(0, σ²) innovations; FY Thm 2.8 / eq. (2.24)
    (hε : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    -- USER-INPUT: absolutely summable coefficients; FY Thm 2.8
    (ha : Summable fun k : ℤ => |a k|)
    -- USER-INPUT: nondegeneracy Σ_k a_k ≠ 0; FY Thm 2.8(i)
    (hane : (∑' k : ℤ, a k) ≠ 0)
    -- LEAN-ONLY: measurability of the process; implicit in FY
    (hmeas : ∀ t, Measurable (X t))
    -- USER-INPUT: two-sided linear representation (FY eq. (2.24)) as the L² limit of
    -- symmetric partial sums (definitionally `IsFilteredBy (X · − m) ε a μ`)
    (hfil : ∀ t : ℤ, Tendsto (fun N : ℕ =>
      eLpNorm (fun ω => X t ω - m -
        ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε (t - k) ω) 2 μ) atTop (𝓝 0))
    (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        Real.sqrt T * ((T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, X ((t : ℤ) + 1) ω - m)) u)
      atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal (σ2 * (∑' k : ℤ, a k) ^ 2))) u)) := by
  classical
  have hwn := hε.isWhiteNoise
  have hsa : Summable a := ha.of_abs
  obtain ⟨A, hA⟩ : ∃ x : ℝ, x = ∑' k : ℤ, a k := ⟨_, rfl⟩
  obtain ⟨Aabs, hAabs⟩ : ∃ x : ℝ, x = ∑' k : ℤ, |a k| := ⟨_, rfl⟩
  -- the symmetric windows exhaust `ℤ`
  have hmono : Monotone fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro p q hpq k hk
    simp only [Finset.mem_Icc] at *
    omega
  have hcov : ∀ k : ℤ, ∃ N : ℕ, k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := fun k =>
    ⟨k.natAbs, by simp only [Finset.mem_Icc]; omega⟩
  have hfin : Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) atTop atTop :=
    tendsto_atTop_finset_of_monotone hmono hcov
  have hANlim : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k) atTop (𝓝 A) := by
    rw [hA]; exact hsa.hasSum.comp hfin
  have hAAlim : Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), |a k|)
      atTop (𝓝 Aabs) := by
    rw [hAabs]; exact ha.hasSum.comp hfin
  -- the `ℓ¹` tail mass
  have hBNnn : ∀ N : ℕ, 0 ≤ Aabs - ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), |a k| := by
    intro N
    have h := ha.sum_le_tsum (Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun k _ => abs_nonneg (a k))
    rw [hAabs]
    linarith
  have hBNlim : Tendsto
      (fun N : ℕ => Aabs - ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), |a k|) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := Aabs) (f := atTop (α := ℕ))).sub hAAlim
    simpa using h
  have hBNbound : ∀ N M : ℕ, N ≤ M →
      ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) \ Finset.Icc (-(N : ℤ)) (N : ℤ), |a k|
        ≤ Aabs - ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), |a k| := by
    intro N M hNM
    have hsub : Finset.Icc (-(N : ℤ)) (N : ℤ) ⊆ Finset.Icc (-(M : ℤ)) (M : ℤ) := by
      intro k hk
      simp only [Finset.mem_Icc] at *
      omega
    have h1 := Finset.sum_sdiff (f := fun k => |a k|) hsub
    have h2 := ha.sum_le_tsum (Finset.Icc (-(M : ℤ)) (M : ℤ)) (fun k _ => abs_nonneg (a k))
    rw [hAabs]
    linarith
  -- the Gaussian limit depends continuously on the variance
  have hGcont : Continuous fun v : ℝ => charFun (gaussianReal 0 (Real.toNNReal v)) u := by
    have hEq : (fun v : ℝ => charFun (gaussianReal 0 (Real.toNNReal v)) u)
        = fun v : ℝ => Complex.exp (-(((max v 0 : ℝ)) : ℂ) * (u : ℂ) ^ 2 / 2) := by
      funext v
      rw [charFun_gaussianReal, Real.coe_toNNReal']
      push_cast
      ring_nf
    rw [hEq]
    fun_prop
  have hlimN : Tendsto (fun N : ℕ => charFun (gaussianReal 0 (Real.toNNReal
        (σ2 * (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k) ^ 2))) u) atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal (σ2 * A ^ 2))) u)) :=
    (hGcont.tendsto (σ2 * A ^ 2)).comp ((hANlim.pow 2).const_mul σ2)
  -- normalization identity for the statement's random variable
  have hSSeq : ∀ (T : ℕ), 1 ≤ T → ∀ ω,
      Real.sqrt (T : ℝ) * ((T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, X ((t : ℤ) + 1) ω - m)
        = (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m) := by
    intro T hT ω
    have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
    have hsum : ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m)
        = (∑ t ∈ Finset.range T, X ((t : ℤ) + 1) ω) - (T : ℝ) * m := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hsum]
    obtain ⟨s, hspos, hsdef⟩ : ∃ s : ℝ, 0 < s ∧ Real.sqrt (T : ℝ) = s :=
      ⟨_, Real.sqrt_pos.2 hTpos, rfl⟩
    have hs2 : s * s = (T : ℝ) := by rw [← hsdef]; exact Real.mul_self_sqrt hTpos.le
    rw [hsdef, ← hs2]
    field_simp
  -- measurability of the two comparison variables
  have hmZ : ∀ T : ℕ, Measurable (fun ω => (Real.sqrt (T : ℝ))⁻¹ *
      ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m)) := fun T =>
    Measurable.const_mul (Finset.measurable_sum _ fun t _ =>
      (hmeas _).sub measurable_const) _
  have hmW : ∀ N T : ℕ, Measurable (fun ω => (Real.sqrt (T : ℝ))⁻¹ *
      ∑ t ∈ Finset.range T,
        ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε ((t : ℤ) + 1 - k) ω) := fun N T =>
    Measurable.const_mul (Finset.measurable_sum _ fun t _ =>
      Finset.measurable_sum _ fun k _ => (hε.measurable _).const_mul _) _
  rw [← hA, Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨N, hN1, hN2⟩ : ∃ N : ℕ,
      |u| * (Real.sqrt σ2 * (Aabs - ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), |a k|)) < δ / 3 ∧
      dist (charFun (gaussianReal 0 (Real.toNNReal
          (σ2 * (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k) ^ 2))) u)
        (charFun (gaussianReal 0 (Real.toNNReal (σ2 * A ^ 2))) u) < δ / 3 := by
    have h1 : Tendsto (fun N : ℕ =>
        |u| * (Real.sqrt σ2 * (Aabs - ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), |a k|)))
        atTop (𝓝 0) := by
      simpa using (hBNlim.const_mul (Real.sqrt σ2)).const_mul |u|
    have e1 := h1.eventually (eventually_lt_nhds (show (0 : ℝ) < δ / 3 by linarith))
    have e2 : ∀ᶠ N : ℕ in atTop,
        dist (charFun (gaussianReal 0 (Real.toNNReal
            (σ2 * (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k) ^ 2))) u)
          (charFun (gaussianReal 0 (Real.toNNReal (σ2 * A ^ 2))) u) < δ / 3 := by
      have h := hlimN.eventually (Metric.ball_mem_nhds
        (charFun (gaussianReal 0 (Real.toNNReal (σ2 * A ^ 2))) u)
        (show (0 : ℝ) < δ / 3 by linarith))
      simpa [Metric.mem_ball] using h
    exact (e1.and e2).exists
  obtain ⟨T0, hT0⟩ := Metric.tendsto_atTop.1
    (tendsto_charFun_truncSum (a := a) hε hσ N u) (δ / 3) (by linarith)
  refine ⟨max 1 T0, fun T hT => ?_⟩
  have hT1 : 1 ≤ T := le_trans (le_max_left _ _) hT
  have hTT0 : T0 ≤ T := le_trans (le_max_right _ _) hT
  rw [show (fun ω => Real.sqrt (T : ℝ) *
        ((T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, X ((t : ℤ) + 1) ω - m))
      = (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m)) from
    funext (hSSeq T hT1)]
  obtain ⟨hint, hbd⟩ := integral_abs_defect_le hε hσ hmeas hfil (hBNnn N) N (hBNbound N) T hT1
  have hd1 : dist (charFun (μ.map fun ω => (Real.sqrt (T : ℝ))⁻¹ *
        ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m)) u)
      (charFun (μ.map fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
        ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε ((t : ℤ) + 1 - k) ω) u) < δ / 3 := by
    rw [dist_eq_norm]
    refine lt_of_le_of_lt
      (le_trans (norm_charFun_map_sub_le (hmZ T) (hmW N T) hint u) ?_) hN1
    exact mul_le_mul_of_nonneg_left hbd (abs_nonneg u)
  have hd2 := hT0 T hTT0
  obtain ⟨P, hP⟩ : ∃ z : ℂ, z = charFun (μ.map fun ω => (Real.sqrt (T : ℝ))⁻¹ *
      ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m)) u := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ z : ℂ, z = charFun (μ.map fun ω => (Real.sqrt (T : ℝ))⁻¹ *
      ∑ t ∈ Finset.range T,
        ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε ((t : ℤ) + 1 - k) ω) u := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ z : ℂ, z = charFun (gaussianReal 0 (Real.toNNReal
      (σ2 * (∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k) ^ 2))) u := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ z : ℂ, z = charFun (gaussianReal 0 (Real.toNNReal (σ2 * A ^ 2))) u :=
    ⟨_, rfl⟩
  rw [← hP, ← hQ] at hd1
  rw [← hQ, ← hR] at hd2
  rw [← hR, ← hS] at hN2
  rw [← hP, ← hS]
  linarith [dist_triangle P Q S, dist_triangle Q R S]

/-! ### Bricks for the lag-0 and Bartlett debts

The **mean correction** in `γ̂(0)` is asymptotically negligible, and this is already a
consequence of the sample-mean layer above: the same ℓ¹ energy budget that produced the
`T`-free `L²` bound of `eLpNorm_windowSum_le` bounds the whole normalized centred partial
sum by `√σ² Σ_k|a_k|` uniformly in `T` (`eLpNorm_normalizedSum_le`), whence
`E|√T X̄_T²| ≤ σ² (Σ_k|a_k|)² / √T → 0` (`tendsto_integral_sqrt_mul_sampleMean_sq`).
So `√T (γ̂(0) − γ(0))` and `√T (T⁻¹ Σ_t X_t² − γ(0))` have the same limit law, which is
the reduction the remaining debts start from.

**Named residues of `sampleACVF_zero_clt_debt` (after this reduction).**
* (R1) the CLT for `T^{-1/2} Σ_{t≤T}(X_t² − γ(0))` at a *fixed* truncation level `N`.
  The truncated square is `2N`-dependent, so Bernstein-block `[1,T]` into big blocks of
  a fixed length `L` separated by guard blocks of length `2N`: the big-block sums are
  functions of **disjoint** innovation blocks, hence independent, and identically
  distributed because the joint law of an i.i.d. family is a product measure and so is
  shift-invariant. Constant weights `T^{-1/2}` then feed the *already present*
  `tendsto_charFun_weighted_iid` — **no new CLT engine is needed**, in contrast with the
  MDS route; `L → ∞` after `T → ∞` removes the guard-block loss.
* (R2) the fourth-moment covariance `Cov(X_s^{(N)2}, X_t^{(N)2})`, i.e. the partition
  formula for `E[ε_i ε_j ε_k ε_l]` over i.i.d. innovations (`η σ⁴` on the diagonal,
  `σ⁴` on each pairing, `0` otherwise). This is the only genuinely *missing analytic
  input* — everything else in (R1)/(R3) reuses machinery in this file.
* (R3) the truncation transfer at the squared level,
  `‖T^{-1/2} Σ_t ((X_t² − EX_t²) − (X_t^{(N)2} − EX_t^{(N)2}))‖₂ → 0` as `N → ∞`,
  uniformly in `T`: factor `X² − X^{(N)2} = (X − X^{(N)})(X + X^{(N)})` and apply
  Cauchy–Schwarz against (R2) together with the ℓ¹ energy budget of
  `eLpNorm_windowSum_le` at the bilinear level.
* (R4) the series identity `Σ_h γ(h)² = σ⁴ Σ_h (Σ_k a_k a_{k+h})²` matching the limit
  produced by (R1)+(R2) to the frozen `(η−3)γ(0)² + 2 Σ_{j∈ℤ} γ(j)²`.
  (The frozen constant is *confirmed* against B&D (1991) Prop 7.3.4: the printed FY
  (2.25) is indeed a misprint, and the docstring's correction is the right one — no
  further amendment is called for.)

**Named residue of `sampleACF_bartlett_clt_debt`.** the joint (lags `0..M`) version of
(R1)–(R4) — the same blocks, assembled through the Cramér–Wold linear combination that
the frozen statement already exhibits — followed by the ratio delta method
`ρ̂(i) = γ̂(i)/γ̂(0)`. Its `bartlettW` covariance is the standard Bartlett formula; no
misprint watch fires there either. -/

/-- The `L²` bound implied by an `eLpNorm` bound (converse of
`eLpNorm_two_le_of_integral_sq_le`). -/
private lemma integral_sq_le_of_eLpNorm_two {f : Ω → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hf : AEStronglyMeasurable f μ) (h : eLpNorm f 2 μ ≤ ENNReal.ofReal C) :
    ∫ ω, f ω ^ 2 ∂μ ≤ C ^ 2 := by
  have hmem : MemLp f 2 μ := ⟨hf, lt_of_le_of_lt h ENNReal.ofReal_lt_top⟩
  rw [hmem.eLpNorm_eq_integral_rpow_norm two_ne_zero (by norm_num)] at h
  have hpow : ∀ ω, ‖f ω‖ ^ ((2 : ENNReal).toReal) = f ω ^ 2 := by
    intro ω
    rw [show ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.norm_eq_abs, sq_abs]
  rw [integral_congr_ae (Eventually.of_forall hpow),
    show ((2 : ENNReal).toReal)⁻¹ = 1 / (2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow] at h
  have hnn : (0 : ℝ) ≤ ∫ ω, f ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  have h2 : Real.sqrt (∫ ω, f ω ^ 2 ∂μ) ≤ C := (ENNReal.ofReal_le_ofReal_iff hC).1 h
  nlinarith [Real.sq_sqrt hnn, Real.sqrt_nonneg (∫ ω, f ω ^ 2 ∂μ)]

/-- **The `T`-free `L²` bound for the normalized centred partial sum**:
`‖T^{-1/2} Σ_{t≤T}(X_t − m)‖₂ ≤ √σ² Σ_k |a_k|`. This is the ℓ¹ energy budget of
`eLpNorm_windowSum_le` applied to the full filter, with the truncation level removed by
`tendsto_eLpNorm_headRemainder`. -/
private lemma eLpNorm_normalizedSum_le [IsProbabilityMeasure μ] {a : ℤ → ℝ} {m σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} (hε : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (ha : Summable fun k : ℤ => |a k|)
    (hmeas : ∀ t, Measurable (X t))
    (hfil : ∀ t : ℤ, Tendsto (fun M : ℕ =>
      eLpNorm (fun ω => X t ω - m -
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε (t - k) ω) 2 μ) atTop (𝓝 0))
    (T : ℕ) (hT : 1 ≤ T) :
    eLpNorm (fun ω => (Real.sqrt (T : ℝ))⁻¹ *
        ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m)) 2 μ
      ≤ ENNReal.ofReal (Real.sqrt σ2 * ∑' k : ℤ, |a k|) := by
  classical
  have hwn := hε.isWhiteNoise
  have hAnn : (0 : ℝ) ≤ ∑' k : ℤ, |a k| := tsum_nonneg fun k => abs_nonneg _
  have hmG : ∀ M : ℕ, Measurable (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
      ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω) := fun M =>
    Measurable.const_mul (Finset.measurable_sum _ fun t _ =>
      Finset.measurable_sum _ fun k _ => (hε.measurable _).const_mul _) _
  have hmE : ∀ M : ℕ, Measurable (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
      (X ((t : ℤ) + 1) ω - m -
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω)) := fun M =>
    Measurable.const_mul (Finset.measurable_sum _ fun t _ =>
      ((hmeas _).sub measurable_const).sub
        (Finset.measurable_sum _ fun k _ => (hε.measurable _).const_mul _)) _
  have hsplit : ∀ (M : ℕ) (ω : Ω),
      (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m)
        = ((Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
            (X ((t : ℤ) + 1) ω - m -
              ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω))
          + ((Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
              ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω) := by
    intro M ω
    have hA : ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m)
        = ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - m -
            ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω)
          + ∑ t ∈ Finset.range T,
              ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun t _ => by ring
    linear_combination (Real.sqrt (T : ℝ))⁻¹ * hA
  have hGbound : ∀ M : ℕ,
      eLpNorm (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω) 2 μ
        ≤ ENNReal.ofReal (Real.sqrt σ2 * ∑' k : ℤ, |a k|) := fun M =>
    eLpNorm_windowSum_le hwn hσ.le a hAnn T M hT
      (ha.sum_le_tsum (Finset.Icc (-(M : ℤ)) (M : ℤ)) (fun k _ => abs_nonneg (a k)))
  have hE0 := tendsto_eLpNorm_headRemainder hε hmeas hfil (m := m) T
  have hlim : Tendsto (fun M : ℕ =>
      eLpNorm (fun ω => (Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T,
        (X ((t : ℤ) + 1) ω - m -
          ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε ((t : ℤ) + 1 - k) ω)) 2 μ
        + ENNReal.ofReal (Real.sqrt σ2 * ∑' k : ℤ, |a k|)) atTop
      (𝓝 (ENNReal.ofReal (Real.sqrt σ2 * ∑' k : ℤ, |a k|))) := by
    have h := hE0.add
      (tendsto_const_nhds (x := ENNReal.ofReal (Real.sqrt σ2 * ∑' k : ℤ, |a k|)))
    simpa using h
  refine ge_of_tendsto hlim (Eventually.of_forall fun M => ?_)
  refine le_trans (le_of_eq (eLpNorm_congr_ae (Eventually.of_forall (hsplit M)))) ?_
  exact le_trans (eLpNorm_add_le (hmE M).aestronglyMeasurable (hmG M).aestronglyMeasurable
    one_le_two) (add_le_add le_rfl (hGbound M))

/-- **The mean correction of `γ̂(0)` is asymptotically negligible** (zero-mean case):
`E|√T X̄_T²| ≤ σ² (Σ_k |a_k|)² / √T → 0`. Hence `√T (γ̂(0) − γ(0))` and
`√T (T⁻¹ Σ_t X_t² − γ(0))` have the same limit law. -/
private lemma tendsto_integral_sqrt_mul_sampleMean_sq [IsProbabilityMeasure μ] {a : ℤ → ℝ}
    {σ2 : ℝ} {X ε : ℤ → Ω → ℝ} (hε : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    (ha : Summable fun k : ℤ => |a k|)
    (hmeas : ∀ t, Measurable (X t))
    (hfil : ∀ t : ℤ, Tendsto (fun M : ℕ =>
      eLpNorm (fun ω => X t ω -
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε (t - k) ω) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun T : ℕ => ∫ ω, |Real.sqrt (T : ℝ) *
        (sampleMean fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ^ 2| ∂μ) atTop (𝓝 0) := by
  classical
  have hAnn : (0 : ℝ) ≤ ∑' k : ℤ, |a k| := tsum_nonneg fun k => abs_nonneg _
  have hfil' : ∀ t : ℤ, Tendsto (fun M : ℕ =>
      eLpNorm (fun ω => X t ω - 0 -
        ∑ k ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), a k * ε (t - k) ω) 2 μ) atTop (𝓝 0) := by
    intro t
    simpa using hfil t
  have hmZ : ∀ T : ℕ, Measurable (fun ω => (Real.sqrt (T : ℝ))⁻¹ *
      ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - 0)) := fun T =>
    Measurable.const_mul (Finset.measurable_sum _ fun t _ =>
      (hmeas _).sub measurable_const) _
  -- the pointwise rewriting `√T X̄² = T^{-1/2} (T^{-1/2} Σ_t X_t)²`
  have hpt : ∀ (T : ℕ), 1 ≤ T → ∀ ω,
      |Real.sqrt (T : ℝ) * (sampleMean fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ^ 2|
        = (Real.sqrt (T : ℝ))⁻¹ *
          ((Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - 0)) ^ 2 := by
    intro T hT ω
    have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
    obtain ⟨s, hspos, hsdef⟩ : ∃ s : ℝ, 0 < s ∧ Real.sqrt (T : ℝ) = s :=
      ⟨_, Real.sqrt_pos.2 hTpos, rfl⟩
    have hs2 : s * s = (T : ℝ) := by rw [← hsdef]; exact Real.mul_self_sqrt hTpos.le
    have hval : Real.sqrt (T : ℝ) *
          (sampleMean fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ^ 2
        = (Real.sqrt (T : ℝ))⁻¹ *
          ((Real.sqrt (T : ℝ))⁻¹ * ∑ t ∈ Finset.range T, (X ((t : ℤ) + 1) ω - 0)) ^ 2 := by
      rw [sampleMean, Fin.sum_univ_eq_sum_range (fun t => X ((t : ℤ) + 1) ω) T, hsdef,
        ← hs2]
      simp only [sub_zero]
      field_simp
    rw [hval, abs_of_nonneg (by positivity)]
  -- the uniform second-moment bound
  have hbound : ∀ T : ℕ, 1 ≤ T →
      ∫ ω, |Real.sqrt (T : ℝ) *
          (sampleMean fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ^ 2| ∂μ
        ≤ (Real.sqrt (T : ℝ))⁻¹ * (Real.sqrt σ2 * ∑' k : ℤ, |a k|) ^ 2 := by
    intro T hT
    rw [integral_congr_ae (Eventually.of_forall (hpt T hT)), integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact integral_sq_le_of_eLpNorm_two (by positivity) (hmZ T).aestronglyMeasurable
      (eLpNorm_normalizedSum_le hε hσ ha hmeas hfil' T hT)
  -- and it tends to zero
  have hsq0 : Tendsto (fun T : ℕ => (Real.sqrt (T : ℝ))⁻¹ *
      (Real.sqrt σ2 * ∑' k : ℤ, |a k|) ^ 2) atTop (𝓝 0) := by
    have h1 : Tendsto (fun T : ℕ => Real.sqrt (T : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun T : ℕ => (Real.sqrt (T : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp h1
    simpa using h2.mul_const ((Real.sqrt σ2 * ∑' k : ℤ, |a k|) ^ 2)
  refine squeeze_zero' ?_ ?_ hsq0
  · filter_upwards with T
    exact integral_nonneg fun ω => abs_nonneg _
  · filter_upwards [eventually_ge_atTop 1] with T hT
    exact hbound T hT

/-- **FY Theorem 2.8(ii) — DEBT (ledger (b); B&D 1991 Prop 7.3.4)**, with the variance
**corrected** from the misprinted eq. (2.25): for a zero-mean two-sided linear process
with IID innovations having finite fourth moment,
`√T (γ̂(0) − γ(0)) →d N(0, (η−3)γ(0)² + 2Σ_{j∈ℤ} γ(j)²)`, `η = Eε⁴/σ⁴`. -/
theorem sampleACVF_zero_clt_debt [IsProbabilityMeasure μ] {a : ℤ → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ}
    -- USER-INPUT: IID(0, σ²) innovations; FY Thm 2.8 / eq. (2.24)
    (hε : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    -- USER-INPUT: finite fourth moment; FY Thm 2.8(ii)
    (hε4 : MemLp (ε 0) 4 μ)
    -- USER-INPUT: absolutely summable coefficients; FY Thm 2.8
    (ha : Summable fun k : ℤ => |a k|)
    -- LEAN-ONLY: measurability of the process; implicit in FY
    (hmeas : ∀ t, Measurable (X t))
    -- USER-INPUT: zero-mean two-sided linear representation (FY eq. (2.24), m = 0)
    (hfil : ∀ t : ℤ, Tendsto (fun N : ℕ =>
      eLpNorm (fun ω => X t ω -
        ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε (t - k) ω) 2 μ) atTop (𝓝 0))
    (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        Real.sqrt T *
          (sampleACVF (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) 0 - acvf X μ 0)) u)
      atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal
        (((∫ ω, ε 0 ω ^ 4 ∂μ) / σ2 ^ 2 - 3) * acvf X μ 0 ^ 2
          + 2 * ∑' j : ℤ, acvf X μ j ^ 2))) u)) := by
  sorry

/-- **Bartlett's asymptotic covariance** (FY eq. (2.26)):
`w_{ij} = Σ_{k=1}^∞ [ρ(k+i) + ρ(k−i) − 2ρ(i)ρ(k)]·[ρ(k+j) + ρ(k−j) − 2ρ(j)ρ(k)]`
(the sum over `k ≥ 1` realized as a `tsum` over `ℕ` shifted by one; junk `0` when not
summable, by the `tsum` convention). -/
noncomputable def bartlettW (X : ℤ → Ω → ℝ) (μ : Measure Ω) (i j : ℕ) : ℝ :=
  ∑' k : ℕ,
    (acf X μ ((k : ℤ) + 1 + (i : ℤ)) + acf X μ ((k : ℤ) + 1 - (i : ℤ))
        - 2 * acf X μ (i : ℤ) * acf X μ ((k : ℤ) + 1)) *
      (acf X μ ((k : ℤ) + 1 + (j : ℤ)) + acf X μ ((k : ℤ) + 1 - (j : ℤ))
        - 2 * acf X μ (j : ℤ) * acf X μ ((k : ℤ) + 1))

/-- **FY Theorem 2.8(iii) — DEBT (ledger (b); B&D 1991 §7.3)**: Bartlett's formula,
in Cramér–Wold form: for every coefficient vector `c` over the lag window `1..M`,
`√T Σ_i c_i (ρ̂(i) − ρ(i)) →d N(0, cᵀ W c)` with `W` from `bartlettW` (FY eq. (2.26)). -/
theorem sampleACF_bartlett_clt_debt [IsProbabilityMeasure μ] {a : ℤ → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} {M : ℕ}
    -- USER-INPUT: IID(0, σ²) innovations; FY Thm 2.8 / eq. (2.24)
    (hε : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    -- USER-INPUT: finite fourth moment; FY Thm 2.8(iii)
    (hε4 : MemLp (ε 0) 4 μ)
    -- USER-INPUT: absolutely summable coefficients; FY Thm 2.8
    (ha : Summable fun k : ℤ => |a k|)
    -- LEAN-ONLY: measurability of the process; implicit in FY
    (hmeas : ∀ t, Measurable (X t))
    -- USER-INPUT: zero-mean two-sided linear representation (FY eq. (2.24), m = 0)
    (hfil : ∀ t : ℤ, Tendsto (fun N : ℕ =>
      eLpNorm (fun ω => X t ω -
        ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a k * ε (t - k) ω) 2 μ) atTop (𝓝 0))
    (c : Fin M → ℝ) (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        Real.sqrt T * ∑ i : Fin M, c i *
          (sampleACF (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ((i : ℕ) + 1)
            - acf X μ (((i : ℕ) : ℤ) + 1))) u)
      atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal
        (∑ i : Fin M, ∑ j : Fin M,
          c i * c j * bartlettW X μ ((i : ℕ) + 1) ((j : ℕ) + 1)))) u)) := by
  sorry

/-- **FY eq. (2.27)** (misprint corrected: the summand is `ρ(t)²`, not `ρ(q)²`): for an
MA(q) process with IID innovations and a lag `j > q`,
`√T ρ̂(j) →d N(0, 1 + 2 Σ_{t=1}^q ρ(t)²)`. In particular for white noise (`q = 0`) the
limit is `N(0,1)`, giving the ±1.96/√T confidence bands. **Proved** from the Bartlett
debt statement: for `j > q` the MA(q) ACF cutoff collapses `w_{jj}` to
`Σ_{|m|≤q} ρ(m)² = 1 + 2Σ_{t=1}^q ρ(t)²`. -/
theorem IsMA.sampleACF_clt [IsProbabilityMeasure μ] {q : ℕ} {a : Fin q → ℝ} {σ2 : ℝ}
    {X ε : ℤ → Ω → ℝ} {j : ℕ}
    (h : IsMA a σ2 X ε μ)
    -- USER-INPUT: IID innovations (upgrades the MA white noise); FY Thm 2.8 context
    (hiid : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    -- USER-INPUT: finite fourth moment; FY Thm 2.8(iii)
    (hε4 : MemLp (ε 0) 4 μ)
    -- LEAN-ONLY: measurability of the process; implicit in FY
    (hmeas : ∀ t, Measurable (X t))
    -- USER-INPUT: the lag exceeds the MA order; FY eq. (2.27)
    (hq : q < j) (u : ℝ) :
    Tendsto (fun T : ℕ => charFun (μ.map fun ω =>
        Real.sqrt T * sampleACF (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) j) u)
      atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal
        (1 + 2 * ∑ t ∈ Finset.Icc 1 q, acf X μ (t : ℤ) ^ 2))) u)) := by
  classical
  -- ## The MA(q) second-order data feeding the Bartlett statement
  have hstat : IsStationary X μ := h.isStationary hmeas
  have hacvf0 : 0 < acvf X μ 0 := by
    rw [h.acvf_zero_eq]
    have : (0 : ℝ) ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    nlinarith
  have hacf0 : acf X μ 0 = 1 := acf_zero (ne_of_gt hacvf0)
  have hacfeven : ∀ m : ℤ, acf X μ (-m) = acf X μ m := fun m => by
    rw [acf, acf, hstat.acvf_even]
  -- the MA(q) ACF cutoff: `ρ(m) = 0` beyond lag `q`
  have hcut : ∀ m : ℤ, ((q : ℤ) < m ∨ m < -(q : ℤ)) → acf X μ m = 0 := by
    intro m hm
    have habs : (q : ℤ) < |m| := by
      rcases hm with hm | hm
      · rw [abs_of_pos (by omega)]; omega
      · rw [abs_of_neg (by omega)]; omega
    have hz : acvf X μ m = 0 := h.cov_eq_zero (by simpa using habs)
    rw [acf, hz, zero_div]
  have hρj : acf X μ (j : ℤ) = 0 := hcut _ (Or.inl (by omega))
  -- ## The Cramér–Wold selector `c` and the two-sided coefficient sequence `a'`
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : Fin j, (i₀ : ℕ) + 1 = j :=
    ⟨⟨j - 1, by omega⟩, show j - 1 + 1 = j from by omega⟩
  obtain ⟨c, hcval⟩ : ∃ c : Fin j → ℝ, ∀ i, c i = if (i : ℕ) + 1 = j then 1 else 0 :=
    ⟨_, fun _ => rfl⟩
  have hci₀ : c i₀ = 1 := by rw [hcval, if_pos hi₀]
  have hcne : ∀ i : Fin j, i ≠ i₀ → c i = 0 := by
    intro i hne
    refine (hcval i).trans (if_neg fun hc' => hne (Fin.ext ?_))
    omega
  obtain ⟨a', ha'val, ha'zero⟩ : ∃ a' : ℤ → ℝ,
      (∀ i : Fin (q + 1), a' ((i : ℕ) : ℤ) = maCoeff a i) ∧
      (∀ k : ℤ, k ∉ Finset.Icc (0 : ℤ) (q : ℤ) → a' k = 0) := by
    refine ⟨fun k => if hk : 0 ≤ k ∧ k.toNat < q + 1 then maCoeff a ⟨k.toNat, hk.2⟩ else 0,
      fun i => ?_, fun k hk => ?_⟩
    · have hk : (0 : ℤ) ≤ ((i : ℕ) : ℤ) ∧ (((i : ℕ) : ℤ)).toNat < q + 1 :=
        ⟨Int.natCast_nonneg _, by simpa using i.isLt⟩
      dsimp only
      rw [dif_pos hk]
      exact congrArg (maCoeff a) (Fin.ext (by simp))
    · simp only [Finset.mem_Icc, not_and, not_le] at hk
      dsimp only
      refine dif_neg fun hc' => ?_
      have := hk hc'.1
      omega
  have ha'sum : Summable fun k : ℤ => |a' k| :=
    summable_of_ne_finset_zero (s := Finset.Icc (0 : ℤ) (q : ℤ))
      fun k hk => by rw [ha'zero k hk, abs_zero]
  -- ## `X` is the (finitely supported) two-sided linear filter of `ε` with weights `a'`
  have hpartial : ∀ (t : ℤ) (N : ℕ), q ≤ N → ∀ ω,
      ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a' k * ε (t - k) ω
        = ∑ i : Fin (q + 1), maCoeff a i * ε (t - ((i : ℕ) : ℤ)) ω := by
    intro t N hN ω
    have hsub : Finset.Icc (0 : ℤ) (q : ℤ) ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
      intro k hk; simp only [Finset.mem_Icc] at *; omega
    rw [← Finset.sum_subset hsub (fun k _ hk => by rw [ha'zero k hk, zero_mul])]
    have hr : ∑ k ∈ Finset.Icc (0 : ℤ) (q : ℤ), a' k * ε (t - k) ω
        = ∑ n ∈ Finset.range (q + 1), a' ((n : ℕ) : ℤ) * ε (t - ((n : ℕ) : ℤ)) ω := by
      refine Finset.sum_nbij' (fun k => k.toNat) (fun n => (n : ℤ)) ?_ ?_ ?_ ?_ ?_
      · intro k hk; simp only [Finset.mem_Icc] at hk; simp only [Finset.mem_range]; omega
      · intro n hn; simp only [Finset.mem_range] at hn; simp only [Finset.mem_Icc]; omega
      · intro k hk; simp only [Finset.mem_Icc] at hk; dsimp only; omega
      · intro n hn; simp only [Finset.mem_range] at hn; dsimp only; omega
      · intro k hk
        simp only [Finset.mem_Icc] at hk
        dsimp only
        rw [show ((k.toNat : ℕ) : ℤ) = k from by omega]
    rw [hr, ← Fin.sum_univ_eq_sum_range
      (fun n => a' ((n : ℕ) : ℤ) * ε (t - ((n : ℕ) : ℤ)) ω) (q + 1)]
    exact Finset.sum_congr rfl fun i _ => by rw [ha'val i]
  have hfil : ∀ t : ℤ, Tendsto (fun N : ℕ =>
      eLpNorm (fun ω => X t ω -
        ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a' k * ε (t - k) ω) 2 μ) atTop (𝓝 0) := by
    intro t
    refine Tendsto.congr' ?_ (tendsto_const_nhds (x := (0 : ENNReal)))
    filter_upwards [eventually_ge_atTop q] with N hN
    have hzero : (fun ω => X t ω -
        ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a' k * ε (t - k) ω) =ᵐ[μ] 0 := by
      filter_upwards [h.rec_sum t] with ω hω
      rw [Pi.zero_apply, hω, hpartial t N hN ω, sub_self]
    rw [eLpNorm_congr_ae hzero, eLpNorm_zero]
  -- ## The Bartlett statement, instantiated at the single lag `j`
  have hbart := sampleACF_bartlett_clt_debt (μ := μ) (a := a') (σ2 := σ2) (X := X) (ε := ε)
    (M := j) hiid hσ hε4 ha'sum hmeas hfil c u
  -- ## `w_{jj}` collapses to `Σ_{|m| ≤ q} ρ(m)² = 1 + 2 Σ_{t=1}^q ρ(t)²`
  have hIcc : ∑ t ∈ Finset.Icc 1 q, acf X μ (t : ℤ) ^ 2
      = ∑ i ∈ Finset.range q, acf X μ ((i : ℤ) + 1) ^ 2 := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
      show q + 1 - 1 = q from by omega]
    exact Finset.sum_congr rfl fun i _ =>
      by rw [show (((1 + i : ℕ)) : ℤ) = (i : ℤ) + 1 from by push_cast; ring]
  have hbw : bartlettW X μ j j = 1 + 2 * ∑ t ∈ Finset.Icc 1 q, acf X μ (t : ℤ) ^ 2 := by
    -- only the `ρ(k+1−j)` slot survives the cutoff
    have hterm : ∀ k : ℕ,
        (acf X μ ((k : ℤ) + 1 + (j : ℤ)) + acf X μ ((k : ℤ) + 1 - (j : ℤ))
            - 2 * acf X μ (j : ℤ) * acf X μ ((k : ℤ) + 1)) *
          (acf X μ ((k : ℤ) + 1 + (j : ℤ)) + acf X μ ((k : ℤ) + 1 - (j : ℤ))
            - 2 * acf X μ (j : ℤ) * acf X μ ((k : ℤ) + 1))
          = acf X μ ((k : ℤ) + 1 - (j : ℤ)) ^ 2 := by
      intro k
      rw [hcut ((k : ℤ) + 1 + (j : ℤ)) (Or.inl (by omega)), hρj]
      ring
    -- the survivor is supported on the window `k ∈ [j−1−q, j−1+q]`
    obtain ⟨d, hd⟩ : ∃ d : ℕ, d = j - 1 - q := ⟨_, rfl⟩
    have hsupp : ∀ k : ℕ, k ∉ Finset.Ico d (d + (2 * q + 1)) →
        acf X μ ((k : ℤ) + 1 - (j : ℤ)) ^ 2 = 0 := by
      intro k hk
      simp only [Finset.mem_Ico, not_and, not_lt] at hk
      have hcase : k < d ∨ d + (2 * q + 1) ≤ k := by
        by_cases hkd : d ≤ k
        · exact Or.inr (hk hkd)
        · exact Or.inl (by omega)
      have : acf X μ ((k : ℤ) + 1 - (j : ℤ)) = 0 := by
        refine hcut _ ?_
        rcases hcase with hc | hc
        · exact Or.inr (by omega)
        · exact Or.inl (by omega)
      rw [this]; ring
    rw [bartlettW, tsum_congr hterm,
      tsum_eq_sum (s := Finset.Ico d (d + (2 * q + 1))) hsupp,
      Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    have hre : ∀ i ∈ Finset.range (2 * q + 1),
        acf X μ ((((d + i : ℕ)) : ℤ) + 1 - (j : ℤ)) ^ 2 = acf X μ ((i : ℤ) - (q : ℤ)) ^ 2 := by
      intro i _
      rw [show (((d + i : ℕ)) : ℤ) + 1 - (j : ℤ) = (i : ℤ) - (q : ℤ) from by omega]
    rw [Finset.sum_congr rfl hre]
    -- split the symmetric window `[−q, q]` at its centre and fold by evenness
    have hlow : ∑ i ∈ Finset.range q, acf X μ ((i : ℤ) - (q : ℤ)) ^ 2
        = ∑ i ∈ Finset.range q, acf X μ ((i : ℤ) + 1) ^ 2 := by
      rw [← Finset.sum_range_reflect (fun i => acf X μ ((i : ℤ) - (q : ℤ)) ^ 2) q]
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [Finset.mem_range] at hi
      rw [show (((q - 1 - i : ℕ)) : ℤ) - (q : ℤ) = -((i : ℤ) + 1) from by omega, hacfeven]
    have hhigh : ∑ i ∈ Finset.Ico (q + 1) (2 * q + 1), acf X μ ((i : ℤ) - (q : ℤ)) ^ 2
        = ∑ i ∈ Finset.range q, acf X μ ((i : ℤ) + 1) ^ 2 := by
      rw [Finset.sum_Ico_eq_sum_range, show 2 * q + 1 - (q + 1) = q from by omega]
      exact Finset.sum_congr rfl fun i _ =>
        by rw [show (((q + 1 + i : ℕ)) : ℤ) - (q : ℤ) = (i : ℤ) + 1 from by push_cast; ring]
    have hmid : acf X μ (((q : ℕ) : ℤ) - (q : ℤ)) ^ 2 = 1 := by
      rw [sub_self, hacf0]; norm_num
    rw [← Finset.sum_range_add_sum_Ico (fun i => acf X μ ((i : ℤ) - (q : ℤ)) ^ 2)
      (show q + 1 ≤ 2 * q + 1 from by omega), Finset.sum_range_succ, hlow, hhigh, hmid, hIcc]
    ring
  -- ## The `c`-collapse of the statement and of Bartlett's variance
  have hvar : (∑ i : Fin j, ∑ i' : Fin j,
        c i * c i' * bartlettW X μ ((i : ℕ) + 1) ((i' : ℕ) + 1))
      = 1 + 2 * ∑ t ∈ Finset.Icc 1 q, acf X μ (t : ℤ) ^ 2 := by
    have hinner : ∀ i : Fin j,
        (∑ i' : Fin j, c i * c i' * bartlettW X μ ((i : ℕ) + 1) ((i' : ℕ) + 1))
          = c i * bartlettW X μ ((i : ℕ) + 1) j := by
      intro i
      rw [Finset.sum_eq_single i₀ (fun i' _ hne => by rw [hcne i' hne]; ring) (by simp),
        hci₀, hi₀]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hinner i),
      Finset.sum_eq_single i₀ (fun i _ hne => by rw [hcne i hne]; ring) (by simp),
      hci₀, hi₀, one_mul, hbw]
  have hmapeq : ∀ (T : ℕ) (ω : Ω),
      Real.sqrt T * ∑ i : Fin j, c i *
          (sampleACF (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) ((i : ℕ) + 1)
            - acf X μ (((i : ℕ) : ℤ) + 1))
        = Real.sqrt T * sampleACF (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) j := by
    intro T ω
    congr 1
    rw [Finset.sum_eq_single i₀ (fun i _ hne => by rw [hcne i hne]; ring) (by simp), hci₀,
      one_mul, hi₀, show (((i₀ : ℕ) : ℤ) + 1) = (j : ℤ) from by omega, hρj, sub_zero]
  rw [← hvar]
  exact Tendsto.congr (fun T => by rw [funext (hmapeq T)]) hbart

end StatLean.TimeSeries
