import StatLean.Minimaxity.ForMathlib.TotalVariation
import StatLean.Minimaxity.ForMathlib.KLDivergence

/-!
# Pinsker–Csiszár–Kullback inequality — Lemma 15.2 (Wainwright §15.1.3)

The total variation distance is controlled by the Kullback–Leibler divergence:
`‖ℙ − ℚ‖_TV ≤ √(½ D(ℚ ‖ ℙ))`  (Eq. (15.8)).

Wainwright outlines the proof in Exercise 15.6: reduce to the Bernoulli case via the partition
`A = {p ≥ q}` and Jensen's inequality. We state it with the `ℝ≥0∞` square root (`rpow (1/2)`),
so the bound is vacuously true when the KL divergence is infinite.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Lemma 15.2.
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {α : Type*} {mα : MeasurableSpace α}

/-- **Scalar Bernoulli–Pinsker inequality** (Wainwright Exercise 15.6, pointwise step):
for `a, b ∈ (0, 1)`,
`2 (a − b)² ≤ a log(a/b) + (1 − a) log((1 − a)/(1 − b)) = D(Bern(a) ‖ Bern(b))`.

This is the elementary one-variable calculus fact underlying Pinsker's inequality:
the function `F(a) = a log(a/b) + (1 − a) log((1 − a)/(1 − b)) − 2 (a − b)²` satisfies
`F(b) = F'(b) = 0` and `F''(a) = 1/(a(1 − a)) − 4 ≥ 0` (since `a(1 − a) ≤ 1/4`), hence is
convex with minimum `0` at `a = b`. -/
private lemma bernoulli_pinsker_scalar {a b : ℝ} (_ha0 : 0 < a) (_ha1 : a < 1)
    (_hb0 : 0 < b) (_hb1 : b < 1) :
    2 * (a - b) ^ 2 ≤ a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b)) := by
  sorry -- TODO(mmx, Wainwright Ex 15.6): convexity of
        -- F(a) = a·log(a/b)+(1−a)·log((1−a)/(1−b)) − 2(a−b)²; F(b)=F'(b)=0,
        -- F''(a) = 1/(a(1−a)) − 4 ≥ 0. One-variable calculus (`deriv`/`StrictMonoOn`).

/-- **Data-processing core of Pinsker's inequality** (Wainwright Exercise 15.6).

The KL divergence dominates `2 · ‖ℙ − ℚ‖²_TV`. By the data-processing inequality for KL under
the binary partition `A = {q ≤ p}` (densities `p = dℙ/dξ`, `q = dℚ/dξ` against `ξ = ℙ + ℚ`),
`D(ℚ ‖ ℙ) ≥ D(Bern(ℚ A) ‖ Bern(ℙ A))`, and on the optimal set `A` the total variation equals
`ℙ A − ℚ A`. Combined with the scalar Bernoulli–Pinsker inequality
`bernoulli_pinsker_scalar` this gives the bound. -/
private lemma klDiv_ge_two_mul_tvDist_sq (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ENNReal.ofReal (2 * (tvDist μ ν).toReal ^ 2) ≤ klDiv ν μ := by
  sorry -- TODO(mmx, Wainwright Ex 15.6): KL data-processing under the 2-cell partition
        -- A = {q ≤ p} (klDiv monotone under the indicator pushforward), the optimal-set
        -- identity tvDist = ℙ A − ℚ A (cf. `tvDist_eq_lintegral_tsub`), then
        -- `bernoulli_pinsker_scalar` with a = (ν A).toReal, b = (μ A).toReal.

/-- **Bernoulli crux of Pinsker's inequality** (Wainwright Exercise 15.6).

With densities `p = dℙ/dξ`, `q = dℚ/dξ` against `ξ = ℙ + ℚ`, the half-`L¹` form of total variation
is bounded by the KL divergence through the data-processing reduction to the Bernoulli partition
`A = {p ≥ q}` and the pointwise inequality
`2 (δ_p − δ_q)² ≤ δ_p log(δ_p/δ_q) + (1 − δ_p) log((1 − δ_p)/(1 − δ_q))` followed by Jensen.
This is the genuine analytic core; the public theorem `pinsker_tv_le_kl` follows by the density
form `tvDist_eq_half_lintegral`. -/
private lemma pinsker_half_lintegral_le (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    2⁻¹ * ∫⁻ x, ENNReal.ofReal
          |(μ.rnDeriv (μ + ν) x).toReal - (ν.rnDeriv (μ + ν) x).toReal| ∂(μ + ν)
      ≤ (2⁻¹ * klDiv ν μ) ^ (1 / 2 : ℝ) := by
  rw [← tvDist_eq_half_lintegral]
  by_cases hkl : klDiv ν μ = ⊤
  · rw [hkl, ENNReal.mul_top (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top),
        ENNReal.top_rpow_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    exact le_top
  · have htv1 : tvDist μ ν ≤ 1 := tvDist_le_one μ ν
    have htvne : tvDist μ ν ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top htv1
    set t : ℝ := (tvDist μ ν).toReal with ht
    set k : ℝ := (klDiv ν μ).toReal with hk
    have ht_nn : 0 ≤ t := ENNReal.toReal_nonneg
    have hk_nn : 0 ≤ k := ENNReal.toReal_nonneg
    have htv_eq : tvDist μ ν = ENNReal.ofReal t := (ENNReal.ofReal_toReal htvne).symm
    have hkl_eq : klDiv ν μ = ENNReal.ofReal k := (ENNReal.ofReal_toReal hkl).symm
    -- Core scalar bound `2 t² ≤ k` from the data-processing lemma.
    have hcore : 2 * t ^ 2 ≤ k := by
      have h := klDiv_ge_two_mul_tvDist_sq μ ν
      rw [← ht, hkl_eq] at h
      exact (ENNReal.ofReal_le_ofReal_iff hk_nn).mp h
    -- Assemble in `ℝ≥0∞`.
    rw [htv_eq, hkl_eq,
        show (2:ℝ≥0∞)⁻¹ * ENNReal.ofReal k = ENNReal.ofReal (k / 2) from by
          rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2), ENNReal.ofReal_ofNat,
              div_eq_mul_inv, mul_comm],
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num : (0:ℝ) ≤ 1 / 2),
        ← Real.sqrt_eq_rpow]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [show t = Real.sqrt (t ^ 2) from (Real.sqrt_sq ht_nn).symm]
    exact Real.sqrt_le_sqrt (by linarith)

/-- **Pinsker–Csiszár–Kullback inequality** (Wainwright Lemma 15.2, Eq. (15.8)):
`‖ℙ − ℚ‖_TV ≤ √(½ D(ℚ ‖ ℙ))`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Lemma 15.2. -/
theorem pinsker_tv_le_kl (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    tvDist μ ν ≤ (2⁻¹ * klDiv ν μ) ^ (1 / 2 : ℝ) := by
  rw [tvDist_eq_half_lintegral]
  exact pinsker_half_lintegral_le μ ν

end StatLean.Minimaxity
