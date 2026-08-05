import StatLean.TimeSeries.ForMathlib.PosSemidefSequence
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
  sorry

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
  sorry

end StatLean.TimeSeries
