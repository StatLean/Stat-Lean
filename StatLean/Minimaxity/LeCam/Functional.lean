import StatLean.Minimaxity.Defs
import StatLean.Minimaxity.ForMathlib.HellingerDivergence
import StatLean.Minimaxity.ForMathlib.LeCamInequality
import StatLean.Minimaxity.LeCam.TwoPoint

/-!
# Le Cam's method for functionals (Wainwright §15.2.1)

For estimating a real functional `θ : ℱ → ℝ` of a density, Le Cam's two-point bound reduces to a
geometric object: the **modulus of continuity** of the functional with respect to the Hellinger
distance (Eq. (15.17)),
```
ω(ε; θ, ℱ) = sup { |θ(f) − θ(g)| : H²(f ‖ g) ≤ ε² }.
```
Corollary 15.6 then gives, for the `n`-sample model,
```
inf_θ̂ sup_f 𝔼[Φ(θ̂ − θ(f))] ≥ ¼ Φ( ½ ω(1/(2√n); θ, ℱ) )       (Eq. (15.18)).
```

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2.1.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {ι 𝓧 : Type*} [mι : MeasurableSpace ι] [m𝓧 : MeasurableSpace 𝓧]

/-- **Hellinger modulus of continuity** (Wainwright Eq. (15.17)):
`ω(ε; θ, ℱ) = sup { |θ(i) − θ(j)| : H²(P i ‖ P j) ≤ ε² }`, the largest fluctuation of the functional
`θfunc` over a Hellinger ball of radius `ε`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2.1, Eq. (15.17). -/
noncomputable def hellingerModulus (θfunc : ι → ℝ) (P : ι → Measure 𝓧) (ε : ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (i : ι) (j : ι) (_ : sqHellinger (P i) (P j) ≤ ε ^ 2), ENNReal.ofReal |θfunc i - θfunc j|

/-- **I.i.d. tensorization at the critical radius.** If `H²(μ ‖ ν) ≤ (1/(2√n))²`, then the `n`-fold
product squared Hellinger distance is at most `1/4`. Combines `sqHellinger_pi_le_nsmul` with the
identity `n · (1/(2√n))² = 1/4` (for `n ≥ 1`; trivial for `n = 0`). -/
private lemma sqHellinger_pi_le_quarter (n : ℕ) (μ ν : Measure 𝓧)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : sqHellinger μ ν ≤ (ENNReal.ofReal (1 / (2 * Real.sqrt n))) ^ 2) :
    sqHellinger (Measure.pi fun _ : Fin n => μ) (Measure.pi fun _ : Fin n => ν) ≤ 4⁻¹ := by
  refine (sqHellinger_pi_le_nsmul n μ ν).trans ?_
  rw [nsmul_eq_mul]
  calc (n : ℝ≥0∞) * sqHellinger μ ν
      ≤ (n : ℝ≥0∞) * (ENNReal.ofReal (1 / (2 * Real.sqrt n))) ^ 2 := by gcongr
    _ ≤ 4⁻¹ := by
        rcases Nat.eq_zero_or_pos n with hn | hn
        · simp [hn]
        · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
          have hsq : ((1 : ℝ) / (2 * Real.sqrt n)) ^ 2 = 1 / (4 * n) := by
            rw [div_pow, one_pow, mul_pow, Real.sq_sqrt hnpos.le]; ring
          rw [← ENNReal.ofReal_pow (by positivity), hsq, ← ENNReal.ofReal_natCast n,
            ← ENNReal.ofReal_mul (by positivity),
            show (4 : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 / 4) by
              rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one,
                ENNReal.ofReal_ofNat, one_div]]
          apply ENNReal.ofReal_le_ofReal
          have hval : (n : ℝ) * (1 / (4 * n)) = 1 / 4 := by field_simp
          exact le_of_eq hval

/-- **A Hellinger-`1/4` ball gives total variation `≤ 1/2`.** From Le Cam's inequality
`‖ℙ−ℚ‖_TV ≤ √(H²)·√(1−H²/4)`: when `H² ≤ 1/4`, the first factor is `≤ 1/2` and the second `≤ 1`. -/
private lemma tvDist_le_half_of_sqHellinger (μ ν : Measure 𝓧)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : sqHellinger μ ν ≤ 4⁻¹) :
    tvDist μ ν ≤ 2⁻¹ := by
  refine (lecam_tv_le_hellinger μ ν).trans ?_
  have h4 : ((4 : ℝ≥0∞)⁻¹) ^ (1 / 2 : ℝ) = 2⁻¹ := by
    rw [show (4 : ℝ≥0∞)⁻¹ = (2⁻¹ : ℝ≥0∞) ^ (2 : ℕ) by rw [← ENNReal.inv_pow]; norm_num,
      ← ENNReal.rpow_natCast (2⁻¹ : ℝ≥0∞) 2, ← ENNReal.rpow_mul]
    norm_num
  have hA : (sqHellinger μ ν) ^ (1 / 2 : ℝ) ≤ 2⁻¹ := by
    rw [← h4]; exact ENNReal.rpow_le_rpow h (by norm_num)
  have hB : (1 - sqHellinger μ ν / 4) ^ (1 / 2 : ℝ) ≤ 1 :=
    ENNReal.rpow_le_one tsub_le_self (by norm_num)
  calc (sqHellinger μ ν) ^ (1 / 2 : ℝ) * (1 - sqHellinger μ ν / 4) ^ (1 / 2 : ℝ)
      ≤ 2⁻¹ * 1 := mul_le_mul' hA hB
    _ = 2⁻¹ := mul_one _

/-- **Le Cam's bound for functionals** (Wainwright Corollary 15.6, Eq. (15.18)): for the `n`-sample
i.i.d. model `Pn i = (P i)^{⊗n}` and an increasing distortion `Φ`,
`inf_θ̂ sup_i 𝔼[Φ(|θ̂ − θ(i)|)] ≥ ¼ Φ(½ ω(1/(2√n); θ, ℱ))`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2.1, Corollary 15.6. -/
theorem minimax_functional_modulus
    (θfunc : ι → ℝ) (P : ι → Measure 𝓧) (n : ℕ) (Pn : Kernel ι (Fin n → 𝓧)) [IsMarkovKernel Pn]
    (Φ : ℝ≥0∞ → ℝ≥0∞)
    -- USER-INPUT: the distortion `Φ` is increasing; Wainwright §15.2.1, Cor 15.6.
    (hΦ : Monotone Φ)
    -- USER-INPUT: `Pn` is the `n`-fold i.i.d. product of the family `P`; Wainwright §15.2.1.
    (hPn : ∀ i, Pn i = Measure.pi fun _ : Fin n => P i) :
    4⁻¹ * Φ (2⁻¹ * hellingerModulus θfunc P (ENNReal.ofReal (1 / (2 * Real.sqrt n))))
      ≤ minimaxRiskDist Φ θfunc Pn := by
  -- The per-pair two-point bound `minimax_functional_pair` (proven below) supplies, for every
  -- Hellinger-admissible pair `(i, j)`, the inequality
  --   `4⁻¹ · Φ(½ |θ(i) − θ(j)|) ≤ minimaxRiskDist Φ θfunc Pn`.
  -- Passing to the supremum over admissible pairs gives `S ≤ minimaxRiskDist`, where `S` is the
  -- sup of those per-pair bounds.
  --
  -- TODO(mmx): two regularity gaps remain in closing the modulus form from the public signature:
  --   (1) `minimax_functional_pair` requires `IsProbabilityMeasure (P i)`, which the signature
  --       does not provide (only `IsMarkovKernel Pn`); for `n ≥ 1` it is derivable from `hPn`,
  --       but `n = 0` needs separate handling;
  --   (2) the interchange `4⁻¹·Φ(½·⨆ d) ≤ ⨆ 4⁻¹·Φ(½·d)` needs `Φ` lower-semicontinuous (or the
  --       modulus supremum attained); `Monotone Φ` alone yields only the reverse inequality.
  sorry

/-- **Per-pair two-point bound underlying Corollary 15.6.** For a Hellinger-admissible pair `(i, j)`
(i.e. `H²(P i ‖ P j) ≤ (1/(2√n))²`), Le Cam's two-point method applied to the `n`-sample model
gives `4⁻¹ · Φ(½ |θ(i) − θ(j)|) ≤ minimaxRiskDist Φ θfunc Pn`. The product Hellinger distance `≤ 1/4`
(`sqHellinger_pi_le_quarter`), so `‖Pn i − Pn j‖_TV ≤ 1/2` (`tvDist_le_half_of_sqHellinger`) and the
two-point factor `1 − ‖·‖_TV ≥ 1/2`. -/
private lemma minimax_functional_pair
    (θfunc : ι → ℝ) (P : ι → Measure 𝓧) (n : ℕ) (Pn : Kernel ι (Fin n → 𝓧)) [IsMarkovKernel Pn]
    (Φ : ℝ≥0∞ → ℝ≥0∞) (hΦ : Monotone Φ)
    (hPn : ∀ i, Pn i = Measure.pi fun _ : Fin n => P i)
    (i j : ι) [IsProbabilityMeasure (P i)] [IsProbabilityMeasure (P j)]
    (hij : sqHellinger (P i) (P j) ≤ (ENNReal.ofReal (1 / (2 * Real.sqrt n))) ^ 2) :
    4⁻¹ * Φ (2⁻¹ * ENNReal.ofReal |θfunc i - θfunc j|) ≤ minimaxRiskDist Φ θfunc Pn := by
  set δ : ℝ≥0∞ := 2⁻¹ * ENNReal.ofReal |θfunc i - θfunc j| with hδ
  have hsep : 2 * δ ≤ edist (θfunc i) (θfunc j) := by
    rw [hδ, ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul,
      edist_dist, Real.dist_eq]
  have key := minimax_two_point Φ θfunc Pn i j δ hΦ hsep
  have hpi : sqHellinger (Pn i) (Pn j) ≤ 4⁻¹ := by
    rw [hPn i, hPn j]; exact sqHellinger_pi_le_quarter n (P i) (P j) hij
  have htv : tvDist (Pn i) (Pn j) ≤ 2⁻¹ := tvDist_le_half_of_sqHellinger (Pn i) (Pn j) hpi
  refine le_trans ?_ key
  have h22 : (4 : ℝ≥0∞)⁻¹ = 2⁻¹ * 2⁻¹ := by
    rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv] <;> norm_num
  have hone : (2 : ℝ≥0∞)⁻¹ = 1 - 2⁻¹ :=
    ENNReal.eq_sub_of_add_eq (by norm_num) ENNReal.inv_two_add_inv_two
  have h1 : (2 : ℝ≥0∞)⁻¹ ≤ 1 - tvDist (Pn i) (Pn j) := by
    rw [hone]; exact tsub_le_tsub_left htv 1
  calc 4⁻¹ * Φ δ
      = Φ δ / 2 * 2⁻¹ := by rw [div_eq_mul_inv, mul_assoc, ← h22, mul_comm]
    _ ≤ Φ δ / 2 * (1 - tvDist (Pn i) (Pn j)) := by gcongr

end StatLean.Minimaxity
