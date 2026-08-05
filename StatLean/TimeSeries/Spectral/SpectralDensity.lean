import StatLean.TimeSeries.Spectral.SpectralMeasure
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Spectral densities under absolutely summable autocovariance (FY §2.3.2, Theorem 2.11)

**FY Theorem 2.11**: when `Σ_k |γ(k)| < ∞`, the spectral measure has the continuous
density `g(λ) = (2π)⁻¹ Σ_{k ∈ ℤ} γ(k) e^{−ikλ}` with respect to the mass-`2π` Haar
measure on the circle (FY's unnormalized eq. (2.38); the `1/2π` sits in the density,
never in the forward transform — batch design D7). We define `spectralDensityOf` by the
real part of that series (γ even makes the series real) and prove: nonnegativity,
continuity, the inversion identity `γ(k) = ∫ e^{ikλ} g(λ) dλ`, and that
`(2π • haar).withDensity g` **is** the spectral measure.

**Reference.** J. Fan and Q. Yao, *Nonlinear Time Series*, Springer, 2003, §2.3.2,
Theorem 2.11 and eqs. (2.36)–(2.38) (pp. 52–53); in-text proof p. 52.
(`FY §2.3.2 Thm 2.11`.)

**Proof formalization notes.**
* Uniform convergence of the series (Weierstrass M-test, `Σ|γ| < ∞`) gives continuity
  and justifies term-by-term integration; the pointwise nonnegativity comes from
  Fejér-mean convergence (`fejerSum_re_nonneg` + `Filter.Tendsto.cesaro`-style limit of
  the weighted sums, FY's in-text argument), not from the series' shape.
* The identification with the spectral measure uses the orthonormality of `fourier`
  against `haarAddCircle` (Mathlib's probability Haar; the `2π` mass normalization
  converts FY's `∫_{−π}^{π}` to `2π • haar`).

**Bibliographic comments.** The `ℓ¹`-inversion pair goes back to Wiener's *Generalized
harmonic analysis*; FY's Theorem 2.11 statement follows Brockwell & Davis (1991),
Cor. 4.3.2.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Real ENNReal

namespace StatLean.TimeSeries

private instance : Fact (0 < 2 * π) := ⟨by positivity⟩

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The **spectral density series** of a process (FY eq. (2.38)):
`g(λ) = (2π)⁻¹ Σ_{k ∈ ℤ} γ(k) · Re(e^{ikλ})` (the series is real for even `γ`; junk
when not summable, by the `tsum` convention). -/
noncomputable def spectralDensityOf (X : ℤ → Ω → ℝ) (μ : Measure Ω)
    (l : AddCircle (2 * π)) : ℝ :=
  (2 * π)⁻¹ * ∑' k : ℤ, acvf X μ k * (fourier k l).re

/-- Summability package for FY Theorem 2.11: `Σ_{k ∈ ℤ} |γ(k)| < ∞` (equivalently the
book's one-sided `Σ_{k ≥ 1}`, by evenness). -/
def HasSummableACVF (X : ℤ → Ω → ℝ) (μ : Measure Ω) : Prop :=
  Summable fun k : ℤ => |acvf X μ k|

/-- The characters have unit modulus. -/
private lemma norm_fourier_eq_one (k : ℤ) (l : AddCircle (2 * π)) :
    ‖fourier (T := 2 * π) k l‖ = 1 := by
  rw [fourier_apply]; exact Circle.norm_coe _

/-- Hence their real parts are bounded by one. -/
private lemma abs_re_fourier_le_one (k : ℤ) (l : AddCircle (2 * π)) :
    |(fourier (T := 2 * π) k l).re| ≤ 1 := by
  rw [← norm_fourier_eq_one k l]; exact Complex.abs_re_le_norm _

/-- The summands of the spectral-density series are dominated by `|γ(k)|`. -/
private lemma abs_acvf_mul_re_le [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ} (k : ℤ)
    (l : AddCircle (2 * π)) :
    |acvf X μ k * (fourier (T := 2 * π) k l).re| ≤ |acvf X μ k| := by
  rw [abs_mul]
  calc |acvf X μ k| * |(fourier (T := 2 * π) k l).re|
      ≤ |acvf X μ k| * 1 :=
        mul_le_mul_of_nonneg_left (abs_re_fourier_le_one k l) (abs_nonneg _)
    _ = |acvf X μ k| := mul_one _

/-- The spectral density series is continuous under summable ACVF. -/
theorem continuous_spectralDensityOf [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hsum : HasSummableACVF X μ) :
    Continuous (spectralDensityOf X μ) := by
  have hser : Continuous fun l : AddCircle (2 * π) =>
      ∑' k : ℤ, acvf X μ k * (fourier (T := 2 * π) k l).re := by
    refine continuous_tsum (u := fun k : ℤ => |acvf X μ k|)
      (fun k => continuous_const.mul
        (Complex.continuous_re.comp (map_continuous (fourier (T := 2 * π) k))))
      hsum fun k l => ?_
    rw [Real.norm_eq_abs]
    exact abs_acvf_mul_re_le k l
  exact continuous_const.mul hser

/-- On the circle, `e^{ijλ}` at a real representative `ω`. -/
private lemma fourier_coe_eq' (j : ℤ) (ω : ℝ) :
    fourier (T := 2 * π) j (↑ω : AddCircle (2 * π))
      = Complex.exp (Complex.I * (ω : ℂ) * (j : ℂ)) := by
  rw [fourier_coe_apply]
  congr 1
  have hπ : ((π : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

/-- The real part of the Fejér–Cesàro sum, expressed through the circle characters. -/
private lemma fejerSum_re_eq (γ : ℤ → ℝ) (n : ℕ) (ω : ℝ) :
    (fejerSum γ n ω).re = (2 * π * n)⁻¹ *
      ∑ m ∈ Finset.Icc (-(n : ℤ) + 1) ((n : ℤ) - 1),
        ((((n : ℤ) - |m| : ℤ) : ℝ) *
          (γ m * (fourier (T := 2 * π) m (↑ω : AddCircle (2 * π))).re)) := by
  rw [fejerSum_eq_weighted, Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  have hterm : ((((n : ℤ) - |m|) : ℤ) : ℂ) * (γ m : ℂ) *
        Complex.exp (-(Complex.I * (ω : ℂ) * (m : ℂ)))
      = ((((((n : ℤ) - |m| : ℤ) : ℝ) * γ m : ℝ)) : ℂ) *
        Complex.exp (-(Complex.I * (ω : ℂ) * (m : ℂ))) := by
    obtain ⟨A, hA⟩ : ∃ A : ℤ, |m| = A := ⟨_, rfl⟩
    rw [hA]
    push_cast
    ring
  have hconj : Complex.exp (-(Complex.I * (ω : ℂ) * (m : ℂ)))
      = (starRingEnd ℂ) (Complex.exp (Complex.I * (ω : ℂ) * (m : ℂ))) := by
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]
  have hre : (Complex.exp (-(Complex.I * (ω : ℂ) * (m : ℂ)))).re
      = (fourier (T := 2 * π) m (↑ω : AddCircle (2 * π))).re := by
    rw [hconj, Complex.conj_re, fourier_coe_eq']
  rw [hterm, Complex.re_ofReal_mul, hre]
  ring

/-- **Fejér-mean limit** (FY p. 52): for an `ℓ¹` sequence whose Fejér-weighted
truncations are nonnegative, the full sum is nonnegative. The truncations converge to
the sum by dominated convergence for series (the weights are in `[0, 1]` and tend to
`1` pointwise). -/
private lemma tsum_nonneg_of_fejer {a : ℤ → ℝ} (hsum : Summable fun m => |a m|)
    (hnn : ∀ n : ℕ, 0 < n →
      0 ≤ ∑ m ∈ Finset.Icc (-(n : ℤ) + 1) ((n : ℤ) - 1),
        (1 - |(m : ℝ)| / (n : ℝ)) * a m) :
    0 ≤ ∑' m : ℤ, a m := by
  have hiff : ∀ (n : ℕ) (m : ℤ),
      |m| < (n : ℤ) ↔ m ∈ Finset.Icc (-(n : ℤ) + 1) ((n : ℤ) - 1) := by
    intro n m
    simp only [Finset.mem_Icc, abs_lt]
    omega
  have hfeq : ∀ n : ℕ,
      (∑' m : ℤ, (if |m| < (n : ℤ) then (1 - |(m : ℝ)| / (n : ℝ)) * a m else 0))
        = ∑ m ∈ Finset.Icc (-(n : ℤ) + 1) ((n : ℤ) - 1),
            (1 - |(m : ℝ)| / (n : ℝ)) * a m := by
    intro n
    rw [tsum_eq_sum (s := Finset.Icc (-(n : ℤ) + 1) ((n : ℤ) - 1))
      fun b hb => if_neg fun h => hb ((hiff n b).mp h)]
    exact Finset.sum_congr rfl fun m hm => if_pos ((hiff n m).mpr hm)
  have hlim : Tendsto (fun n : ℕ => ∑' m : ℤ,
      (if |m| < (n : ℤ) then (1 - |(m : ℝ)| / (n : ℝ)) * a m else 0)) atTop
      (nhds (∑' m : ℤ, a m)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun m => |a m|) hsum ?_ ?_
    · intro m
      have hev : (fun n : ℕ =>
            (if |m| < (n : ℤ) then (1 - |(m : ℝ)| / (n : ℝ)) * a m else 0))
          =ᶠ[atTop] fun n : ℕ => (1 - |(m : ℝ)| / (n : ℝ)) * a m := by
        filter_upwards [eventually_ge_atTop (|m|.toNat + 1)] with n hn
        refine if_pos ?_
        have htn : (|m|.toNat : ℤ) = |m| := Int.toNat_of_nonneg (abs_nonneg m)
        omega
      refine Tendsto.congr' hev.symm ?_
      have h0 : Tendsto (fun n : ℕ => |(m : ℝ)| / (n : ℝ)) atTop (nhds 0) :=
        tendsto_const_div_atTop_nhds_zero_nat _
      have h1 : Tendsto (fun n : ℕ => (1 : ℝ) - |(m : ℝ)| / (n : ℝ)) atTop
          (nhds ((1 : ℝ) - 0)) := tendsto_const_nhds.sub h0
      simpa using h1.mul_const (a m)
    · refine Filter.Eventually.of_forall fun n m => ?_
      rw [Real.norm_eq_abs]
      split_ifs with h
      · rw [abs_mul]
        refine mul_le_of_le_one_left (abs_nonneg _) ?_
        have hn0 : (0 : ℝ) < (n : ℝ) := by
          have : (0 : ℤ) < (n : ℤ) := lt_of_le_of_lt (abs_nonneg m) h
          exact_mod_cast this
        have hle : |(m : ℝ)| / (n : ℝ) ≤ 1 := by
          rw [div_le_one hn0]
          have : ((|m| : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ) := by exact_mod_cast h.le
          simpa using this
        have hge : (0 : ℝ) ≤ |(m : ℝ)| / (n : ℝ) := div_nonneg (abs_nonneg _) hn0.le
        rw [abs_le]
        constructor <;> linarith
      · simpa using abs_nonneg (a m)
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [hfeq n]
  exact hnn n hn

/-- **Nonnegativity** (FY Thm 2.11, in-text proof): under stationarity and summable
ACVF, the spectral density series is pointwise nonnegative (Fejér-mean argument). -/
theorem spectralDensityOf_nonneg [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hstat : IsStationary X μ) (hsum : HasSummableACVF X μ) (l : AddCircle (2 * π)) :
    0 ≤ spectralDensityOf X μ l := by
  induction l using QuotientAddGroup.induction_on with
  | _ ω =>
  rw [spectralDensityOf]
  refine mul_nonneg (by positivity) ?_
  refine tsum_nonneg_of_fejer (a := fun m : ℤ =>
    acvf X μ m * (fourier (T := 2 * π) m (↑ω : AddCircle (2 * π))).re) ?_ ?_
  · exact Summable.of_nonneg_of_le (fun m => abs_nonneg _)
      (fun m => abs_acvf_mul_re_le m _) hsum
  · intro n hn
    have h1 := fejerSum_re_nonneg (acvf X μ) hstat.acvf_posSemidef hstat.acvf_even n ω
    rw [fejerSum_re_eq] at h1
    obtain ⟨S, hSdef⟩ : ∃ S : ℝ, ∑ m ∈ Finset.Icc (-(n : ℤ) + 1) ((n : ℤ) - 1),
        ((((n : ℤ) - |m| : ℤ) : ℝ) *
          (acvf X μ m * (fourier (T := 2 * π) m (↑ω : AddCircle (2 * π))).re)) = S := ⟨_, rfl⟩
    rw [hSdef] at h1
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have h2 : (0 : ℝ) < 2 * π * (n : ℝ) := by positivity
    have hS : 0 ≤ S := by
      have hsplit : S = (2 * π * (n : ℝ)) * ((2 * π * (n : ℝ))⁻¹ * S) := by field_simp
      rw [hsplit]
      exact mul_nonneg h2.le h1
    have hconv : ∑ m ∈ Finset.Icc (-(n : ℤ) + 1) ((n : ℤ) - 1),
        (1 - |(m : ℝ)| / (n : ℝ)) *
          (acvf X μ m * (fourier (T := 2 * π) m (↑ω : AddCircle (2 * π))).re)
        = (n : ℝ)⁻¹ * S := by
      rw [← hSdef, Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      push_cast
      field_simp
    rw [hconv]
    exact mul_nonneg (by positivity) hS

/-- **FY Theorem 2.11**: under stationarity and summable ACVF, the measure with density
`spectralDensityOf` against the mass-`2π` Haar measure is the spectral measure of the
process (existence-with-density form; inversion `γ(k) = ∫ e^{ikλ} g dλ` is the
coefficient clause of `IsSpectralMeasure`). -/
theorem isSpectralMeasure_withDensity [IsProbabilityMeasure μ] {X : ℤ → Ω → ℝ}
    (hstat : IsStationary X μ) (hsum : HasSummableACVF X μ) :
    IsSpectralMeasure X μ
      ((ENNReal.ofReal (2 * π) •
          (AddCircle.haarAddCircle : Measure (AddCircle (2 * π)))).withDensity
        fun l => ENNReal.ofReal (spectralDensityOf X μ l)) := by
  sorry

/-- Causal stationary ARMA processes satisfy the summable-ACVF hypothesis
(FY Prop 2.2(i) feeding §2.3; exponential decay ⇒ `ℓ¹`). -/
theorem IsARMA.hasSummableACVF [IsProbabilityMeasure μ] {p q : ℕ} {b : Fin p → ℝ}
    {a : Fin q → ℝ} {σ2 : ℝ} {X ε : ℤ → Ω → ℝ}
    (h : IsARMA b a σ2 X ε μ)
    (hC : ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧
      ∀ k : ℤ, |acvf X μ k| ≤ C * r ^ k.natAbs) :
    HasSummableACVF X μ := by
  obtain ⟨C, -, r, hr0, hr1, hbd⟩ := hC
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) hbd ?_
  refine Summable.mul_left C ?_
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using summable_geometric_of_lt_one hr0 hr1
  · simpa using summable_geometric_of_lt_one hr0 hr1

end StatLean.TimeSeries
