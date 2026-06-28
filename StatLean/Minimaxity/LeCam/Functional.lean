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

/-- **Lower-semicontinuous functions push a supremum inward.** For lsc `Φ : ℝ≥0∞ → ℝ≥0∞` and a
*nonempty* family `g`, `Φ(⨆ i, g i) ≤ ⨆ i, Φ(g i)`. (Monotone `Φ` gives the reverse inequality
`⨆ Φ ≤ Φ(⨆)` unconditionally; lower semicontinuity is exactly what upgrades it the other way.)

The proof is the standard one: if the claim failed, `R := ⨆ Φ(g i) < Φ(⨆ g)`, so `⨆ g` lies in the
open set `{x | R < Φ x}` (lsc); but `⨆ g ∈ closure (range g)` (`IsLUB.mem_closure`), so that open
neighbourhood meets `range g` at some `g i`, forcing `R < Φ(g i) ≤ R`, a contradiction. -/
private lemma map_iSup_le_of_lsc {κ : Type*} [Nonempty κ] {Φ : ℝ≥0∞ → ℝ≥0∞}
    (hlsc : LowerSemicontinuous Φ) (g : κ → ℝ≥0∞) :
    Φ (⨆ i, g i) ≤ ⨆ i, Φ (g i) := by
  by_contra hcon
  push_neg at hcon
  have hopen : IsOpen (Φ ⁻¹' Set.Ioi (⨆ i, Φ (g i))) :=
    (lowerSemicontinuous_iff_isOpen_preimage.mp hlsc) _
  have hmem : (⨆ i, g i) ∈ Φ ⁻¹' Set.Ioi (⨆ i, Φ (g i)) := hcon
  have hclos : (⨆ i, g i) ∈ closure (Set.range g) :=
    isLUB_iSup.mem_closure (Set.range_nonempty g)
  rw [mem_closure_iff_nhds] at hclos
  obtain ⟨y, hy1, hy2⟩ := hclos _ (hopen.mem_nhds hmem)
  obtain ⟨i, rfl⟩ := hy2
  rw [Set.mem_preimage, Set.mem_Ioi] at hy1
  exact absurd (le_iSup (fun i => Φ (g i)) i) (not_le.mpr hy1)

/-- **Lsc supremum interchange over a nonempty set of admissible pairs.** Specialises
`map_iSup_le_of_lsc` to the doubly-indexed-with-predicate supremum that defines the modulus, by
reindexing through the subtype `{q : κ × κ // p q.1 q.2}` (nonempty thanks to the witness
`(i₀, j₀)`). -/
private lemma map_biSup_le_of_lsc {κ : Type*} {Φ : ℝ≥0∞ → ℝ≥0∞}
    (hlsc : LowerSemicontinuous Φ) (p : κ → κ → Prop) (v : κ → κ → ℝ≥0∞)
    {i₀ j₀ : κ} (h₀ : p i₀ j₀) :
    Φ (⨆ i, ⨆ j, ⨆ (_ : p i j), v i j)
      ≤ ⨆ i, ⨆ j, ⨆ (_ : p i j), Φ (v i j) := by
  haveI : Nonempty {q : κ × κ // p q.1 q.2} := ⟨⟨(i₀, j₀), h₀⟩⟩
  have hL : (⨆ i, ⨆ j, ⨆ (_ : p i j), v i j)
      = ⨆ q : {q : κ × κ // p q.1 q.2}, v q.1.1 q.1.2 := by
    apply le_antisymm
    · exact iSup_le fun i => iSup_le fun j => iSup_le fun hij =>
        le_iSup (fun q : {q : κ × κ // p q.1 q.2} => v q.1.1 q.1.2) ⟨(i, j), hij⟩
    · exact iSup_le fun q =>
        le_iSup_of_le q.1.1 (le_iSup_of_le q.1.2 (le_iSup_of_le q.2 le_rfl))
  rw [hL]
  refine le_trans
    (map_iSup_le_of_lsc hlsc (fun q : {q : κ × κ // p q.1 q.2} => v q.1.1 q.1.2)) ?_
  exact iSup_le fun q =>
    le_iSup_of_le q.1.1 (le_iSup_of_le q.1.2 (le_iSup_of_le q.2 le_rfl))

/-- **Le Cam's bound for functionals** (Wainwright Corollary 15.6, Eq. (15.18)): for the `n`-sample
i.i.d. model `Pn i = (P i)^{⊗n}` and an increasing distortion `Φ`,
`inf_θ̂ sup_i 𝔼[Φ(|θ̂ − θ(i)|)] ≥ ¼ Φ(½ ω(1/(2√n); θ, ℱ))`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.2.1, Corollary 15.6. -/
theorem minimax_functional_modulus
    -- LEAN-ONLY: the index set is nonempty. On an empty `ι` both `hellingerModulus` and
    -- `minimaxRiskDist` collapse to `0`, so the conclusion would read `4⁻¹·Φ 0 ≤ 0`, which fails
    -- for any `Φ` with `Φ 0 ≠ 0` (e.g. a positive constant — still monotone and lsc); the modulus
    -- supremum is genuinely empty there. Vacuous for every concrete family `𝒫 ≠ ∅`.
    [Nonempty ι]
    (θfunc : ι → ℝ) (P : ι → Measure 𝓧)
    -- USER-INPUT: the class `𝒫 = {P i}` consists of probability measures (densities); the per-pair
    -- Le Cam bound and the i.i.d. Hellinger tensorization are stated for probability measures.
    -- Wainwright §15.2.1. (Not derivable from `IsMarkovKernel Pn` + `hPn` alone: extracting a
    -- factor's mass from `Measure.pi` needs `SigmaFinite (P i)`, which is unavailable here.)
    [∀ i, IsProbabilityMeasure (P i)]
    (n : ℕ) (Pn : Kernel ι (Fin n → 𝓧)) [IsMarkovKernel Pn]
    (Φ : ℝ≥0∞ → ℝ≥0∞)
    -- USER-INPUT: the distortion `Φ` is increasing; Wainwright §15.2.1, Cor 15.6.
    (hΦ : Monotone Φ)
    -- LEAN-ONLY: `Φ` is lower-semicontinuous (needed for the `Φ(½·⨆d) ≤ ⨆Φ(½·d)` modulus-sup
    -- interchange that `Monotone Φ` alone cannot give); satisfied by the examples' `Φ = (·)²`.
    (hΦlsc : LowerSemicontinuous Φ)
    -- USER-INPUT: `Pn` is the `n`-fold i.i.d. product of the family `P`; Wainwright §15.2.1.
    (hPn : ∀ i, Pn i = Measure.pi fun _ : Fin n => P i) :
    4⁻¹ * Φ (2⁻¹ * hellingerModulus θfunc P (ENNReal.ofReal (1 / (2 * Real.sqrt n))))
      ≤ minimaxRiskDist Φ θfunc Pn := by
  set ε : ℝ≥0∞ := ENNReal.ofReal (1 / (2 * Real.sqrt n)) with hε
  -- The per-pair two-point bound (`minimax_functional_pair`) for every Hellinger-admissible pair.
  have hpair : ∀ i j, sqHellinger (P i) (P j) ≤ ε ^ 2 →
      4⁻¹ * Φ (2⁻¹ * ENNReal.ofReal |θfunc i - θfunc j|) ≤ minimaxRiskDist Φ θfunc Pn :=
    fun i j hij => minimax_functional_pair θfunc P n Pn Φ hΦ hPn i j hij
  -- The diagonal `(i₀, i₀)` is always admissible (`H²(P i₀ ‖ P i₀) = 0`), so the modulus supremum
  -- is over a nonempty index — this is what powers the lsc interchange below.
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hself : sqHellinger (P i₀) (P i₀) = 0 := by simp [sqHellinger]
  have hdiag : sqHellinger (P i₀) (P i₀) ≤ ε ^ 2 := by rw [hself]; exact zero_le _
  -- Distribute `2⁻¹` through the modulus supremum.
  have hM : 2⁻¹ * hellingerModulus θfunc P ε
      = ⨆ i, ⨆ j, ⨆ (_ : sqHellinger (P i) (P j) ≤ ε ^ 2),
          2⁻¹ * ENNReal.ofReal |θfunc i - θfunc j| := by
    simp only [hellingerModulus, ENNReal.mul_iSup]
  -- The lsc interchange `Φ(½·⨆ d) ≤ ⨆ Φ(½·d)`.
  have hinter : Φ (2⁻¹ * hellingerModulus θfunc P ε)
      ≤ ⨆ i, ⨆ j, ⨆ (_ : sqHellinger (P i) (P j) ≤ ε ^ 2),
          Φ (2⁻¹ * ENNReal.ofReal |θfunc i - θfunc j|) := by
    rw [hM]
    exact map_biSup_le_of_lsc hΦlsc _ _ hdiag
  calc 4⁻¹ * Φ (2⁻¹ * hellingerModulus θfunc P ε)
      ≤ 4⁻¹ * ⨆ i, ⨆ j, ⨆ (_ : sqHellinger (P i) (P j) ≤ ε ^ 2),
          Φ (2⁻¹ * ENNReal.ofReal |θfunc i - θfunc j|) := mul_le_mul_left' hinter _
    _ = ⨆ i, ⨆ j, ⨆ (_ : sqHellinger (P i) (P j) ≤ ε ^ 2),
          4⁻¹ * Φ (2⁻¹ * ENNReal.ofReal |θfunc i - θfunc j|) := by
        simp only [ENNReal.mul_iSup]
    _ ≤ minimaxRiskDist Φ θfunc Pn := by
        refine iSup_le fun i => iSup_le fun j => iSup_le fun hij => ?_
        exact hpair i j hij

end StatLean.Minimaxity
