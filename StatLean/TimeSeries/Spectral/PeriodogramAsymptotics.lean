import StatLean.TimeSeries.Spectral.Periodogram
import StatLean.TimeSeries.Spectral.LinearFilter
import StatLean.TimeSeries.ForMathlib.Probability.TriangularCLT
import StatLean.TimeSeries.Models.WhiteNoise

/-!
# Periodogram asymptotics (FY §2.4.2, Theorem 2.14)

For a two-sided linear process `X_t = Σ_{j∈ℤ} a_j ε_{t−j}` with iid `(0, σ²)`
innovations and `Σ|a_j| < ∞`, writing `n = [(T−1)/2]` and, for `1 ≤ k ≤ n`,

* `ξ_{2k−1} = (2/T)^{1/2} σ⁻¹ Σ_{t=1}^T ε_t cos(t ω_k)` (`dftNoiseCos`),
* `ξ_{2k} = (2/T)^{1/2} σ⁻¹ Σ_{t=1}^T ε_t sin(t ω_k)` (`dftNoiseSin`):

**Theorem 2.14.**
(i) every fixed finite linear combination `Σ_j c_j ξ_{k_j}` (distinct indices) is
asymptotically `N(0, Σ_j c_j²)` — proved via the exact discrete trigonometric
orthogonality (variance is exactly `Σ c_j²` up to `O(1/T)`) and the double-array
Lindeberg CLT (`TriangularCLT`);
(ii) `I_T(ω_k) = 2π g(ω_k) (ξ_{2k−1}² + ξ_{2k}²)/2 + R_T(ω_k)` with
`max_{1≤k≤n} E|R_T(ω_k)| → 0` — via the DFT-of-filter factorization
`α_k = a(e^{−iω_k}) α_{k,ε} + Y_T(ω_k)` and the uniform L² edge-effect bound
(FY eq. (2.72), Cauchy–Schwarz against the `ℓ¹` tail of `a`).

Consequence recorded in FY's text (not separately stated here): the normalized
ordinates `I_T(ω_k)/(2π g(ω_k))` are asymptotically iid `Exp(1)` — this is (i) + (ii) +
continuous mapping, deferred until a consumer needs it.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.4.2,
Theorem 2.14 (p. 63); proof §2.7.6 (pp. 83–85), citing Serfling (1980) p. 31 for the
double-array CLT. (`FY §2.4.2 Thm 2.14`.)

**Proof formalization notes.**
* The frequencies use `fourierFreq T k = 2πk/T` and the time index `t = 1, …, T` as in
  `Spectral/DFT.lean` (whose exponential-orthogonality lemmas drive the exact variance
  computation in (i)).
* In (ii) the remainder bound is uniform over `k ≤ n`: stated with an explicit
  vanishing envelope sequence `b : ℕ → ℝ` rather than a `Finset.sup`, avoiding junk
  when the frequency window is empty (`T ≤ 2`).
* The spectral density `g` is `spectralDensityOf X μ` at the circle point
  `(fourierFreq T k : AddCircle (2π))`; summability of the ACVF (needed for `g` to be
  the honest density) is derived from `Σ|a_j| < ∞` via the filter theory
  (`IsFilteredBy.hasSummableACVF` with white-noise input).

**Bibliographic comments.** Theorem 2.14 descends from Brockwell & Davis (1991),
Prop 10.3.1–Thm 10.3.2; the χ²₂-limit picture of periodogram ordinates goes back to
Fisher (1929) and Bartlett (1950).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Real Topology

namespace StatLean.TimeSeries

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The normalized **cosine noise sum** `ξ_{2k−1}` (FY §2.7.6):
`(2/T)^{1/2} σ⁻¹ Σ_{t=1}^T ε_t cos(t ω_k)`; junk when `σ² ≤ 0` or `T = 0`. -/
noncomputable def dftNoiseCos (ε : ℤ → Ω → ℝ) (σ2 : ℝ) (T : ℕ) (k : ℕ) (ω : Ω) : ℝ :=
  Real.sqrt (2 / T) / Real.sqrt σ2 *
    ∑ t ∈ Finset.range T, ε ((t : ℤ) + 1) ω * Real.cos (((t : ℝ) + 1) * fourierFreq T k)

/-- The normalized **sine noise sum** `ξ_{2k}` (FY §2.7.6). -/
noncomputable def dftNoiseSin (ε : ℤ → Ω → ℝ) (σ2 : ℝ) (T : ℕ) (k : ℕ) (ω : Ω) : ℝ :=
  Real.sqrt (2 / T) / Real.sqrt σ2 *
    ∑ t ∈ Finset.range T, ε ((t : ℤ) + 1) ω * Real.sin (((t : ℝ) + 1) * fourierFreq T k)

/-- The interleaved family: `ξ-index 2k−1 ↦ cos` at frequency `k`, `2k ↦ sin` at
frequency `k` (FY's numbering; `j ≥ 1`). -/
noncomputable def dftNoiseXi (ε : ℤ → Ω → ℝ) (σ2 : ℝ) (T : ℕ) (j : ℕ) : Ω → ℝ :=
  if j % 2 = 1 then dftNoiseCos ε σ2 T ((j + 1) / 2) else dftNoiseSin ε σ2 T (j / 2)

/-! ### Discrete trigonometric orthogonality (FY §2.4.1)

The exact variance computation behind Theorem 2.14(i) is the classical orthogonality of
the Fourier trigonometric vectors on the grid `t = 1, …, T`. Everything is derived from
`Spectral/DFT.lean`'s exponential orthogonality by taking real and imaginary parts and
by the product-to-sum identities.
-/

/-- `e^{ir} = cos r + i sin r` in the shape used below. -/
private lemma exp_I_ofReal (r : ℝ) :
    Complex.exp (Complex.I * (r : ℂ))
      = (Real.cos r : ℂ) + (Real.sin r : ℂ) * Complex.I := by
  rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- The full-period exponential sum at a Fourier frequency: `Σ_{t=1}^T e^{i t ω_m}` is
`T` when `T ∣ m` and `0` otherwise. -/
private lemma sum_exp_fourierFreq_eq {T : ℕ} (hT : 0 < T) (m : ℤ) :
    ∑ t ∈ Finset.range T,
        Complex.exp (Complex.I * ((((t : ℝ) + 1) * fourierFreq T m : ℝ) : ℂ))
      = if (T : ℤ) ∣ m then (T : ℂ) else 0 := by
  by_cases hdvd : (T : ℤ) ∣ m
  · rw [if_pos hdvd]
    obtain ⟨q, rfl⟩ := hdvd
    have hTR : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
    have hfr : fourierFreq T ((T : ℤ) * q) = 2 * π * (q : ℝ) := by
      unfold fourierFreq; push_cast; field_simp
    have hterm : ∀ t ∈ Finset.range T,
        Complex.exp (Complex.I * ((((t : ℝ) + 1) * fourierFreq T ((T : ℤ) * q) : ℝ) : ℂ))
          = 1 := by
      intro t _
      rw [hfr]
      have : Complex.I * (((((t : ℝ) + 1) * (2 * π * (q : ℝ))) : ℝ) : ℂ)
          = (((((t : ℕ) : ℤ) + 1) * q : ℤ) : ℂ) * (2 * π * Complex.I) := by
        push_cast; ring
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [Finset.sum_congr rfl hterm]
    simp
  · rw [if_neg hdvd]
    have hfr0 : fourierFreq T (0 : ℤ) = 0 := by unfold fourierFreq; simp
    have hkey := sum_exp_fourierFreq_eq_zero hT (j := (0 : ℤ)) (k := m) (by simpa using hdvd)
    rw [← Fin.sum_univ_eq_sum_range
      (fun t : ℕ => Complex.exp (Complex.I * ((((t : ℝ) + 1) * fourierFreq T m : ℝ) : ℂ))) T]
    rw [← hkey]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hfr0]
    congr 1
    push_cast
    ring

/-- The full-period cosine sum: `T` on the diagonal `T ∣ m`, `0` off it. -/
private lemma sum_cos_fourierFreq {T : ℕ} (hT : 0 < T) (m : ℤ) :
    ∑ t ∈ Finset.range T, Real.cos (((t : ℝ) + 1) * fourierFreq T m)
      = if (T : ℤ) ∣ m then (T : ℝ) else 0 := by
  have h := congrArg Complex.re (sum_exp_fourierFreq_eq hT m)
  rw [Complex.re_sum] at h
  simp only [exp_I_ofReal, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    sub_zero, add_zero] at h
  rw [h]
  by_cases hdvd : (T : ℤ) ∣ m <;> simp [hdvd]

/-- The full-period sine sum always vanishes. -/
private lemma sum_sin_fourierFreq {T : ℕ} (hT : 0 < T) (m : ℤ) :
    ∑ t ∈ Finset.range T, Real.sin (((t : ℝ) + 1) * fourierFreq T m) = 0 := by
  have h := congrArg Complex.im (sum_exp_fourierFreq_eq hT m)
  rw [Complex.im_sum] at h
  simp only [exp_I_ofReal, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    zero_add, add_zero] at h
  rw [h]
  by_cases hdvd : (T : ℤ) ∣ m <;> simp [hdvd]

section Orthogonality

variable {T k l : ℕ}

/-- Additivity of the Fourier frequency in the index. -/
private lemma fourierFreq_sub_mul (T : ℕ) (k l : ℕ) (t : ℕ) :
    ((t : ℝ) + 1) * fourierFreq T (k : ℤ) - ((t : ℝ) + 1) * fourierFreq T (l : ℤ)
      = ((t : ℝ) + 1) * fourierFreq T ((k : ℤ) - (l : ℤ)) := by
  unfold fourierFreq; push_cast; ring

private lemma fourierFreq_add_mul (T : ℕ) (k l : ℕ) (t : ℕ) :
    ((t : ℝ) + 1) * fourierFreq T (k : ℤ) + ((t : ℝ) + 1) * fourierFreq T (l : ℤ)
      = ((t : ℝ) + 1) * fourierFreq T ((k : ℤ) + (l : ℤ)) := by
  unfold fourierFreq; push_cast; ring

/-- On the window `1 ≤ k, l` and `k + l < T`, the sum frequency is never a multiple of
`T`. -/
private lemma not_dvd_add (hk : 1 ≤ k) (hkl : k + l < T) :
    ¬ ((T : ℤ) ∣ ((k : ℤ) + (l : ℤ))) := by
  intro hdvd
  have hpos : (0 : ℤ) < (k : ℤ) + (l : ℤ) := by
    have : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
    have : (0 : ℤ) ≤ (l : ℤ) := Int.natCast_nonneg _
    omega
  have hle := Int.le_of_dvd hpos hdvd
  have : ((k : ℤ) + (l : ℤ)) < (T : ℤ) := by exact_mod_cast hkl
  omega

/-- On the same window, the difference frequency is a multiple of `T` exactly on the
diagonal. -/
private lemma dvd_sub_iff (hk : 1 ≤ k) (hl : 1 ≤ l) (hkl : k + l < T) :
    ((T : ℤ) ∣ ((k : ℤ) - (l : ℤ))) ↔ k = l := by
  constructor
  · intro hdvd
    have hkT : (k : ℤ) < (T : ℤ) := by
      have : k < T := by omega
      exact_mod_cast this
    have hlT : (l : ℤ) < (T : ℤ) := by
      have : l < T := by omega
      exact_mod_cast this
    have hk0 : (0 : ℤ) ≤ (k : ℤ) := Int.natCast_nonneg _
    have hl0 : (0 : ℤ) ≤ (l : ℤ) := Int.natCast_nonneg _
    have habs : |(k : ℤ) - (l : ℤ)| < (T : ℤ) := by rw [abs_lt]; omega
    have := Int.eq_zero_of_abs_lt_dvd hdvd habs
    have : (k : ℤ) = (l : ℤ) := by omega
    exact_mod_cast this
  · rintro rfl; simp

/-- **Cosine–cosine orthogonality**: `Σ_{t=1}^T cos(tω_k) cos(tω_l) = (T/2) δ_{kl}`. -/
private lemma sum_cos_mul_cos (hT : 0 < T) (hk : 1 ≤ k) (hl : 1 ≤ l) (hkl : k + l < T) :
    ∑ t ∈ Finset.range T,
        Real.cos (((t : ℝ) + 1) * fourierFreq T (k : ℤ))
          * Real.cos (((t : ℝ) + 1) * fourierFreq T (l : ℤ))
      = if k = l then (T : ℝ) / 2 else 0 := by
  have hterm : ∀ t : ℕ,
      Real.cos (((t : ℝ) + 1) * fourierFreq T (k : ℤ))
        * Real.cos (((t : ℝ) + 1) * fourierFreq T (l : ℤ))
        = (Real.cos (((t : ℝ) + 1) * fourierFreq T ((k : ℤ) - (l : ℤ)))
            + Real.cos (((t : ℝ) + 1) * fourierFreq T ((k : ℤ) + (l : ℤ)))) / 2 := by
    intro t
    rw [← fourierFreq_sub_mul T k l t, ← fourierFreq_add_mul T k l t, Real.cos_sub,
      Real.cos_add]
    ring
  rw [Finset.sum_congr rfl fun t _ => hterm t, ← Finset.sum_div, Finset.sum_add_distrib,
    sum_cos_fourierFreq hT, sum_cos_fourierFreq hT, if_neg (not_dvd_add hk hkl)]
  by_cases hd : k = l
  · rw [if_pos hd, if_pos ((dvd_sub_iff hk hl hkl).2 hd)]; ring
  · rw [if_neg hd, if_neg (fun h => hd ((dvd_sub_iff hk hl hkl).1 h))]; ring

/-- **Sine–sine orthogonality**: `Σ_{t=1}^T sin(tω_k) sin(tω_l) = (T/2) δ_{kl}`. -/
private lemma sum_sin_mul_sin (hT : 0 < T) (hk : 1 ≤ k) (hl : 1 ≤ l) (hkl : k + l < T) :
    ∑ t ∈ Finset.range T,
        Real.sin (((t : ℝ) + 1) * fourierFreq T (k : ℤ))
          * Real.sin (((t : ℝ) + 1) * fourierFreq T (l : ℤ))
      = if k = l then (T : ℝ) / 2 else 0 := by
  have hterm : ∀ t : ℕ,
      Real.sin (((t : ℝ) + 1) * fourierFreq T (k : ℤ))
        * Real.sin (((t : ℝ) + 1) * fourierFreq T (l : ℤ))
        = (Real.cos (((t : ℝ) + 1) * fourierFreq T ((k : ℤ) - (l : ℤ)))
            - Real.cos (((t : ℝ) + 1) * fourierFreq T ((k : ℤ) + (l : ℤ)))) / 2 := by
    intro t
    rw [← fourierFreq_sub_mul T k l t, ← fourierFreq_add_mul T k l t, Real.cos_sub,
      Real.cos_add]
    ring
  rw [Finset.sum_congr rfl fun t _ => hterm t, ← Finset.sum_div, Finset.sum_sub_distrib,
    sum_cos_fourierFreq hT, sum_cos_fourierFreq hT, if_neg (not_dvd_add hk hkl)]
  by_cases hd : k = l
  · rw [if_pos hd, if_pos ((dvd_sub_iff hk hl hkl).2 hd)]; ring
  · rw [if_neg hd, if_neg (fun h => hd ((dvd_sub_iff hk hl hkl).1 h))]; ring

/-- **Cosine–sine orthogonality**: the mixed sums vanish identically on the window. -/
private lemma sum_cos_mul_sin (hT : 0 < T) :
    ∑ t ∈ Finset.range T,
        Real.cos (((t : ℝ) + 1) * fourierFreq T (k : ℤ))
          * Real.sin (((t : ℝ) + 1) * fourierFreq T (l : ℤ))
      = 0 := by
  have hterm : ∀ t : ℕ,
      Real.cos (((t : ℝ) + 1) * fourierFreq T (k : ℤ))
        * Real.sin (((t : ℝ) + 1) * fourierFreq T (l : ℤ))
        = (Real.sin (((t : ℝ) + 1) * fourierFreq T ((k : ℤ) + (l : ℤ)))
            - Real.sin (((t : ℝ) + 1) * fourierFreq T ((k : ℤ) - (l : ℤ)))) / 2 := by
    intro t
    rw [← fourierFreq_sub_mul T k l t, ← fourierFreq_add_mul T k l t, Real.sin_sub,
      Real.sin_add]
    ring
  rw [Finset.sum_congr rfl fun t _ => hterm t, ← Finset.sum_div, Finset.sum_sub_distrib,
    sum_sin_fourierFreq hT, sum_sin_fourierFreq hT]
  ring

end Orthogonality

/-! ### The `ξ`-family as a weighted sum of the innovations -/

/-- The frequency index carried by the `ξ`-index `j` (`2k−1 ↦ k`, `2k ↦ k`). -/
private def xiFreq (j : ℕ) : ℕ := if j % 2 = 1 then (j + 1) / 2 else j / 2

/-- The trigonometric factor carried by the `ξ`-index `j` at time `t + 1`. -/
private noncomputable def xiTrig (T j t : ℕ) : ℝ :=
  if j % 2 = 1 then Real.cos (((t : ℝ) + 1) * fourierFreq T (xiFreq j : ℤ))
  else Real.sin (((t : ℝ) + 1) * fourierFreq T (xiFreq j : ℤ))

private lemma abs_xiTrig_le_one (T j t : ℕ) : |xiTrig T j t| ≤ 1 := by
  unfold xiTrig
  split_ifs
  · exact Real.abs_cos_le_one _
  · exact Real.abs_sin_le_one _

private lemma one_le_xiFreq {j : ℕ} (hj : 1 ≤ j) : 1 ≤ xiFreq j := by
  unfold xiFreq
  split_ifs with h <;> omega

/-- `ξ`-indices with the same parity and the same frequency coincide. -/
private lemma xiFreq_inj {j j' : ℕ} (hpar : j % 2 = j' % 2) (h : xiFreq j = xiFreq j') :
    j = j' := by
  unfold xiFreq at h
  by_cases hj : j % 2 = 1
  · rw [if_pos hj, if_pos (by omega)] at h; omega
  · rw [if_neg hj, if_neg (by omega)] at h; omega

/-- **The `ξ`-trigonometric Gram matrix** on the window `κ i ≥ 1`, frequencies inside
`[1, (T−1)/2]`: orthogonal with squared norm `T/2`. -/
private lemma sum_xiTrig_mul {T j j' : ℕ} (hT : 0 < T) (hj : 1 ≤ j) (hj' : 1 ≤ j')
    (hw : xiFreq j + xiFreq j' < T) :
    ∑ t ∈ Finset.range T, xiTrig T j t * xiTrig T j' t
      = if j = j' then (T : ℝ) / 2 else 0 := by
  have hf : 1 ≤ xiFreq j := one_le_xiFreq hj
  have hf' : 1 ≤ xiFreq j' := one_le_xiFreq hj'
  unfold xiTrig
  by_cases hp : j % 2 = 1 <;> by_cases hp' : j' % 2 = 1
  · simp only [if_pos hp, if_pos hp']
    rw [sum_cos_mul_cos hT hf hf' hw]
    by_cases hd : xiFreq j = xiFreq j'
    · rw [if_pos hd, if_pos (xiFreq_inj (by omega) hd)]
    · rw [if_neg hd, if_neg (fun h => hd (by rw [h]))]
  · simp only [if_pos hp, if_neg hp']
    rw [sum_cos_mul_sin hT, if_neg (by omega)]
  · simp only [if_neg hp, if_pos hp']
    rw [if_neg (show ¬ j = j' by omega),
      ← sum_cos_mul_sin (T := T) (k := xiFreq j') (l := xiFreq j) hT]
    exact Finset.sum_congr rfl fun t _ => mul_comm _ _
  · simp only [if_neg hp, if_neg hp']
    rw [sum_sin_mul_sin hT hf hf' hw]
    by_cases hd : xiFreq j = xiFreq j'
    · rw [if_pos hd, if_pos (xiFreq_inj (by omega) hd)]
    · rw [if_neg hd, if_neg (fun h => hd (by rw [h]))]

omit [MeasurableSpace Ω] in
/-- The `ξ`-coordinate is the weighted innovation sum `Σ_{t<T} (A_T · trig) ε_{t+1}`. -/
private lemma dftNoiseXi_eq_sum (ε : ℤ → Ω → ℝ) (σ2 : ℝ) (T j : ℕ) (ω : Ω) :
    dftNoiseXi ε σ2 T j ω
      = ∑ t ∈ Finset.range T,
          (Real.sqrt (2 / T) / Real.sqrt σ2 * xiTrig T j t) * ε ((t : ℤ) + 1) ω := by
  unfold dftNoiseXi xiTrig xiFreq
  by_cases h : j % 2 = 1
  · simp only [if_pos h]
    unfold dftNoiseCos
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring
  · simp only [if_neg h]
    unfold dftNoiseSin
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => by ring

/-- The weight of the innovation `ε_{t+1}` in the linear combination `Σ_i c_i ξ_{κ i}`. -/
private noncomputable def xiCombWeight {m : ℕ} (c : Fin m → ℝ) (κ : Fin m → ℕ) (σ2 : ℝ)
    (T t : ℕ) : ℝ :=
  ∑ i, c i * (Real.sqrt (2 / T) / Real.sqrt σ2 * xiTrig T (κ i) t)

omit [MeasurableSpace Ω] in
private lemma sum_c_dftNoiseXi_eq {m : ℕ} (c : Fin m → ℝ) (κ : Fin m → ℕ) (ε : ℤ → Ω → ℝ)
    (σ2 : ℝ) (T : ℕ) (ω : Ω) :
    ∑ i, c i * dftNoiseXi ε σ2 T (κ i) ω
      = ∑ t ∈ Finset.range T, xiCombWeight c κ σ2 T t * ε ((t : ℤ) + 1) ω := by
  simp only [dftNoiseXi_eq_sum, Finset.mul_sum, xiCombWeight, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => by ring

omit [MeasurableSpace Ω] in
/-- **Exact row variance** (FY §2.7.6): on the window where every `ξ`-frequency involved
fits in `[1, (T−1)/2]`, the innovation-weight energy is exactly `σ⁻² Σ c²`, so the row
variances of the array equal `Σ c²` — no error term at all. -/
private lemma sum_xiCombWeight_sq {m : ℕ} (c : Fin m → ℝ) (κ : Fin m → ℕ) {σ2 : ℝ}
    (hσ : 0 < σ2) (hinj : Function.Injective κ) (h1 : ∀ i, 1 ≤ κ i)
    {T : ℕ} (hT : 0 < T) (hwin : ∀ i j, xiFreq (κ i) + xiFreq (κ j) < T) :
    σ2 * ∑ t ∈ Finset.range T, (xiCombWeight c κ σ2 T t) ^ 2 = ∑ i, c i ^ 2 := by
  have hTR : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  have h2T : (0 : ℝ) ≤ 2 / (T : ℝ) := div_nonneg (by norm_num) (Nat.cast_nonneg T)
  have hA2 : (Real.sqrt (2 / T) / Real.sqrt σ2) ^ 2 = 2 / ((T : ℝ) * σ2) := by
    rw [div_pow, Real.sq_sqrt h2T, Real.sq_sqrt hσ.le, div_div]
  -- Expand the square of the weight into the trigonometric Gram matrix.
  have hexp : ∀ t : ℕ, (xiCombWeight c κ σ2 T t) ^ 2
      = ∑ i, ∑ j, (c i * c j * (Real.sqrt (2 / T) / Real.sqrt σ2) ^ 2)
          * (xiTrig T (κ i) t * xiTrig T (κ j) t) := by
    intro t
    rw [xiCombWeight, sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl fun t _ => hexp t]
  -- Swap the time sum inside.
  have hswap : ∑ t ∈ Finset.range T, ∑ i, ∑ j,
        (c i * c j * (Real.sqrt (2 / T) / Real.sqrt σ2) ^ 2)
          * (xiTrig T (κ i) t * xiTrig T (κ j) t)
      = ∑ i, ∑ j, (c i * c j * (Real.sqrt (2 / T) / Real.sqrt σ2) ^ 2)
          * ∑ t ∈ Finset.range T, xiTrig T (κ i) t * xiTrig T (κ j) t := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
  rw [hswap]
  -- Orthogonality collapses the double sum to the diagonal.
  have hdiag : ∀ i j : Fin m, (∑ t ∈ Finset.range T, xiTrig T (κ i) t * xiTrig T (κ j) t)
      = if j = i then (T : ℝ) / 2 else 0 := by
    intro i j
    rw [sum_xiTrig_mul hT (h1 i) (h1 j) (hwin i j)]
    by_cases h : j = i
    · rw [if_pos h, if_pos (by rw [h])]
    · rw [if_neg h, if_neg (fun hc => h (hinj hc).symm)]
  have hrow : ∀ i : Fin m, (∑ j, (c i * c j * (Real.sqrt (2 / T) / Real.sqrt σ2) ^ 2)
        * ∑ t ∈ Finset.range T, xiTrig T (κ i) t * xiTrig T (κ j) t)
      = (c i * c i * (Real.sqrt (2 / T) / Real.sqrt σ2) ^ 2) * ((T : ℝ) / 2) := by
    intro i
    rw [Finset.sum_eq_single i]
    · rw [hdiag i i, if_pos rfl]
    · intro j _ hj; rw [hdiag i j, if_neg hj, mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hA2]
  field_simp

omit [MeasurableSpace Ω] in
/-- The innovation weights are uniformly `O(T^{-1/2})`: this is the negligibility feeding
the Lindeberg condition. -/
private lemma xiCombWeight_sq_le {m : ℕ} (c : Fin m → ℝ) (κ : Fin m → ℕ) {σ2 : ℝ}
    (hσ : 0 < σ2) (T t : ℕ) :
    (xiCombWeight c κ σ2 T t) ^ 2 ≤ 2 / ((T : ℝ) * σ2) * (∑ i, |c i|) ^ 2 := by
  have h2T : (0 : ℝ) ≤ 2 / (T : ℝ) := div_nonneg (by norm_num) (Nat.cast_nonneg T)
  have hA : (0 : ℝ) ≤ Real.sqrt (2 / T) / Real.sqrt σ2 := by positivity
  have hA2 : (Real.sqrt (2 / T) / Real.sqrt σ2) ^ 2 = 2 / ((T : ℝ) * σ2) := by
    rw [div_pow, Real.sq_sqrt h2T, Real.sq_sqrt hσ.le, div_div]
  have habs : |xiCombWeight c κ σ2 T t|
      ≤ (Real.sqrt (2 / T) / Real.sqrt σ2) * ∑ i, |c i| := by
    rw [xiCombWeight, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg hA]
    have h1 := abs_xiTrig_le_one T (κ i) t
    have h2 : (0 : ℝ) ≤ |c i| * (Real.sqrt (2 / T) / Real.sqrt σ2) :=
      mul_nonneg (abs_nonneg _) hA
    nlinarith [mul_nonneg h2 (sub_nonneg.2 h1)]
  calc (xiCombWeight c κ σ2 T t) ^ 2 = |xiCombWeight c κ σ2 T t| ^ 2 := (sq_abs _).symm
    _ ≤ ((Real.sqrt (2 / T) / Real.sqrt σ2) * ∑ i, |c i|) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) habs 2
    _ = 2 / ((T : ℝ) * σ2) * (∑ i, |c i|) ^ 2 := by rw [mul_pow, hA2]

/-! ### Weighted sums of an i.i.d. sequence

The `ξ`-combination is a triangular array of *weighted* copies of one i.i.d. sequence; the
Lindeberg condition then only needs (a) the weights to be individually negligible and
(b) the common law to be square-integrable (the truncated second moment `∫_{K ≤ |Y|} Y²`
vanishes as `K → ∞` by dominated convergence). -/

/-- **CLT for weighted sums of an i.i.d. sequence** (charFun form). The rows are
`X_{n,i} = w_{n,i} Y_i`; the row-variance limit `v` and the individual negligibility of
the weights are the only inputs beyond the sampling law. -/
private lemma tendsto_charFun_weighted_iid [IsProbabilityMeasure μ]
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
        show (K : ℝ) ≤ |Y (↑i : ℕ) ω|
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

/-- **FY Theorem 2.14(i)**: any fixed finite linear combination of distinct
`ξ`-coordinates is asymptotically `N(0, Σ c²)` (charFun form). The index selection
`κsel` picks `m` distinct `ξ`-indices; the indices are fixed while `T → ∞`. -/
theorem dftNoiseXi_clt [IsProbabilityMeasure μ] {σ2 : ℝ} {ε : ℤ → Ω → ℝ}
    -- USER-INPUT: iid(0, σ²) innovations; FY Thm 2.14
    (hε : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    {m : ℕ} (c : Fin m → ℝ)
    -- USER-INPUT: distinct ξ-indices, all ≥ 1; FY Thm 2.14(i)
    (κsel : Fin m → ℕ) (hinj : Function.Injective κsel) (h1 : ∀ i, 1 ≤ κsel i)
    (u : ℝ) :
    Tendsto (fun T : ℕ =>
        charFun (μ.map fun ω => ∑ i, c i * dftNoiseXi ε σ2 T (κsel i) ω) u) atTop
      (𝓝 (charFun (gaussianReal 0 (Real.toNNReal (∑ i, c i ^ 2))) u)) := by
  -- The innovations, reindexed by `ℕ` as `Y j = ε_{j+1}`.
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℕ → Ω → ℝ, Y = fun j : ℕ => ε ((j : ℤ) + 1) := ⟨_, rfl⟩
  have hYi : ∀ j : ℕ, Y j = ε ((j : ℤ) + 1) := fun j => by rw [hYdef]
  have hY0 : Y 0 = ε 1 := by rw [hYdef]; norm_num
  have hmeasY : ∀ j, Measurable (Y j) := fun j => by rw [hYi j]; exact hε.measurable _
  have hindepY : iIndepFun Y μ := by
    rw [hYdef]
    exact iIndepFun.precomp (g := fun j : ℕ => (j : ℤ) + 1)
      (fun a b hab => by exact_mod_cast (add_left_injective (1 : ℤ) hab)) hε.iIndep
  have hidentY : ∀ j, IdentDistrib (Y j) (Y 0) μ μ := by
    intro j; rw [hYi j, hY0]; exact hε.identDistrib _ 1
  have hL2Y : MemLp (Y 0) 2 μ := by
    rw [hY0]; exact (hε.identDistrib 0 1).memLp_snd hε.memLp
  have hmeanY : ∫ ω, Y 0 ω ∂μ = 0 := by
    rw [hY0]; exact ((hε.identDistrib 1 0).integral_eq).trans hε.integral_eq_zero
  have hvarY : variance (Y 0) μ = σ2 := by
    rw [hY0]; exact ((hε.identDistrib 1 0).variance_eq).trans hε.variance_eq
  -- A uniform bound on the `ξ`-frequencies involved (they are fixed while `T → ∞`).
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ i, xiFreq (κsel i) ≤ M :=
    ⟨Finset.univ.sup fun i => xiFreq (κsel i),
      fun i => Finset.le_sup (f := fun i => xiFreq (κsel i)) (Finset.mem_univ i)⟩
  -- Row variances: exactly `Σ c²` once the frequency window fits.
  have hS : Tendsto
      (fun T : ℕ => σ2 * ∑ t : Fin T, (xiCombWeight c κsel σ2 T (t : ℕ)) ^ 2) atTop
      (𝓝 (∑ i, c i ^ 2)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (2 * M)] with T hT'
    have hT : 0 < T := by omega
    have hwin : ∀ i j, xiFreq (κsel i) + xiFreq (κsel j) < T := by
      intro i j; have := hM i; have := hM j; omega
    rw [Fin.sum_univ_eq_sum_range
      (fun t : ℕ => (xiCombWeight c κsel σ2 T t) ^ 2) T]
    exact (sum_xiCombWeight_sq c κsel hσ hinj h1 hT hwin).symm
  -- Weight negligibility: the weights are uniformly `O(T^{-1/2})`.
  have hneg : ∀ cc : ℝ, 0 < cc → ∀ᶠ T in atTop,
      ∀ t : Fin T, (xiCombWeight c κsel σ2 T (t : ℕ)) ^ 2 ≤ cc := by
    intro cc hcc
    have heq : ∀ T : ℕ, 2 / ((T : ℝ) * σ2) * (∑ i, |c i|) ^ 2
        = (2 * (∑ i, |c i|) ^ 2 / σ2) * ((T : ℝ))⁻¹ := by
      intro T
      rcases eq_or_ne ((T : ℝ)) 0 with h | h
      · rw [h]; simp
      · field_simp
    have hinvT : Tendsto (fun T : ℕ => ((T : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hlim : Tendsto (fun T : ℕ => 2 / ((T : ℝ) * σ2) * (∑ i, |c i|) ^ 2) atTop (𝓝 0) := by
      simp only [heq]
      simpa using hinvT.const_mul (2 * (∑ i, |c i|) ^ 2 / σ2)
    filter_upwards [hlim.eventually_le_const hcc] with T hT1 t
    exact le_trans (xiCombWeight_sq_le c κsel hσ T (t : ℕ)) hT1
  have key := tendsto_charFun_weighted_iid (μ := μ) (Y := Y) (kk := fun T : ℕ => T)
    (w := fun T (t : Fin T) => xiCombWeight c κsel σ2 T (t : ℕ)) (σ2 := σ2)
    (v := ∑ i, c i ^ 2) hmeasY hindepY hidentY hL2Y hmeanY hvarY hσ hS hneg u
  refine Tendsto.congr (fun T => ?_) key
  congr 1
  refine congrArg (fun f : Ω → ℝ => μ.map f) ?_
  funext ω
  rw [sum_c_dftNoiseXi_eq c κsel ε σ2 T ω,
    ← Fin.sum_univ_eq_sum_range
      (fun t : ℕ => xiCombWeight c κsel σ2 T t * ε ((t : ℤ) + 1) ω) T]
  exact Finset.sum_congr rfl fun t _ => by rw [hYi (t : ℕ)]

/-- **FY Theorem 2.14(ii)**: for the two-sided linear process, uniformly over the
Fourier frequencies `1 ≤ k ≤ [(T−1)/2]`, the periodogram ordinate is the rescaled
χ²₂-type quadratic form of the noise trigonometric sums up to an `L¹`-negligible
remainder:
`E |I_T(ω_k) − 2π g(ω_k) (ξ_{2k−1}² + ξ_{2k}²)/2| ≤ b_T → 0`. -/
theorem periodogram_eq_scaled_chi2_approx [IsProbabilityMeasure μ] {σ2 : ℝ} {a : ℤ → ℝ}
    {X ε : ℤ → Ω → ℝ}
    -- USER-INPUT: iid(0, σ²) innovations; FY Thm 2.14
    (hε : IsIIDNoise ε σ2 μ) (hσ : 0 < σ2)
    -- USER-INPUT: absolutely summable two-sided coefficients; FY Thm 2.14
    (ha : Summable fun j : ℤ => |a j|)
    (hmeas : ∀ t, Measurable (X t))
    -- USER-INPUT: two-sided linear representation (FY eq. (2.24), zero mean),
    -- definitionally `IsFilteredBy X ε a μ`
    (hfil : IsFilteredBy X ε a μ) :
    ∃ b : ℕ → ℝ, Tendsto b atTop (𝓝 0) ∧
      ∀ T k : ℕ, 1 ≤ k → k ≤ (T - 1) / 2 →
        ∫ ω, |periodogram (fun t : Fin T => X (((t : ℕ) : ℤ) + 1) ω) k
            - 2 * π * spectralDensityOf X μ ((fourierFreq T k : ℝ) : AddCircle (2 * π))
              * ((dftNoiseCos ε σ2 T k ω) ^ 2 + (dftNoiseSin ε σ2 T k ω) ^ 2) / 2|
          ∂μ ≤ b T := by
  sorry

end StatLean.TimeSeries
