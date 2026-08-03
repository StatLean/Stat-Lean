import StatLean.HypothesisTesting.Bootstrap.Edgeworth

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology RealInnerProductSpace FourierTransform

namespace StatLean.HypothesisTesting
namespace Edgeworth

local notation "E₂" => EuclideanSpace ℝ (Fin 2)

/-- The linear part of the change of centring, on the sample side. -/
noncomputable def centringMap (δ : ℝ) (w : E₂) : E₂ := WithLp.toLp 2 ![w 0, w 1 + 2 * δ * w 0]

/-- The transpose of `centringMap`, on the frequency side. -/
noncomputable def centringAdj (δ : ℝ) (t : E₂) : E₂ := WithLp.toLp 2 ![t 0 + 2 * δ * t 1, t 1]

lemma centringMap_zero (δ : ℝ) (w : E₂) : centringMap δ w 0 = w 0 := rfl
lemma centringMap_one (δ : ℝ) (w : E₂) : centringMap δ w 1 = w 1 + 2 * δ * w 0 := rfl
lemma centringAdj_zero (δ : ℝ) (t : E₂) : centringAdj δ t 0 = t 0 + 2 * δ * t 1 := rfl
lemma centringAdj_one (δ : ℝ) (t : E₂) : centringAdj δ t 1 = t 1 := rfl

lemma inner_two (w t : E₂) : (⟪w, t⟫ : ℝ) = w 0 * t 0 + w 1 * t 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  change t 0 * w 0 + t 1 * w 1 = w 0 * t 0 + w 1 * t 1
  ring

/-- **`centringAdj` is the transpose of `centringMap`.** -/
lemma inner_centringMap (δ : ℝ) (w t : E₂) :
    (⟪centringMap δ w, t⟫ : ℝ) = ⟪w, centringAdj δ t⟫ := by
  rw [inner_two, inner_two, centringMap_zero, centringMap_one, centringAdj_zero,
    centringAdj_one]
  ring

lemma measurable_centringMap (δ : ℝ) : Measurable (centringMap δ) := by
  have hvec : Measurable fun w : E₂ => (![w 0, w 1 + 2 * δ * w 0] : Fin 2 → ℝ) := by
    refine measurable_pi_lambda _ fun i => ?_
    fin_cases i
    · change Measurable fun w : E₂ => w 0
      fun_prop
    · change Measurable fun w : E₂ => w 1 + 2 * δ * w 0
      fun_prop
  have htoLp : Measurable (WithLp.toLp 2 : (Fin 2 → ℝ) → E₂) := by fun_prop
  exact htoLp.comp hvec

lemma centringMap_smul (δ r : ℝ) (w : E₂) : centringMap δ (r • w) = r • centringMap δ w := by
  ext i
  fin_cases i <;> simp [centringMap_zero, centringMap_one] <;> ring

lemma centringMap_sum {ι : Type*} (δ : ℝ) (s : Finset ι) (f : ι → E₂) :
    centringMap δ (∑ i ∈ s, f i) = ∑ i ∈ s, centringMap δ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => ext i; fin_cases i <;> simp [centringMap_zero, centringMap_one]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      ext i
      fin_cases i <;> simp [centringMap_zero, centringMap_one] <;> ring

/-- **The change of centring is an affine map of the pair, with unipotent linear part.** -/
lemma pairAt_eq_centringMap (c v c' v' x : ℝ) :
    pairAt c v x
      = centringMap (c' - c) (pairAt c' v' x)
        + (WithLp.toLp 2 ![c' - c, v' + (c' - c) ^ 2 - v] : E₂) := by
  ext i
  fin_cases i <;>
    simp [pairAt_zero, pairAt_one, centringMap_zero, centringMap_one] <;> ring

private lemma inv_sqrt_mul_natCast (n : ℕ) :
    (Real.sqrt (n : ℝ))⁻¹ * (n : ℝ) = Real.sqrt (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hs : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 h0
    have key : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = (n : ℝ) := Real.mul_self_sqrt h0.le
    field_simp
    linarith [key]

/-- **The two roots differ by the same affine map, with the translation scaled by `√n`.** -/
lemma vecRoot_pairAt_eq (c v c' v' : ℝ) (g : ℝ → ℝ) {n : ℕ} (y : Fin n → ℝ) :
    ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, pairAt c v (g (y i)) : E₂)
      = centringMap (c' - c) ((Real.sqrt (n : ℝ))⁻¹ • ∑ i, pairAt c' v' (g (y i)))
        + Real.sqrt (n : ℝ) • (WithLp.toLp 2 ![c' - c, v' + (c' - c) ^ 2 - v] : E₂) := by
  set κ : E₂ := WithLp.toLp 2 ![c' - c, v' + (c' - c) ^ 2 - v] with hκ
  have hpt : ∀ i : Fin n,
      pairAt c v (g (y i)) = centringMap (c' - c) (pairAt c' v' (g (y i))) + κ :=
    fun i => pairAt_eq_centringMap c v c' v' (g (y i))
  have hs : (∑ i, pairAt c v (g (y i)) : E₂)
      = (∑ i, centringMap (c' - c) (pairAt c' v' (g (y i)))) + (n : ℕ) • κ := by
    simp only [hpt]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [hs, ← centringMap_sum, smul_add, centringMap_smul]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul ℝ n κ, smul_smul, inv_sqrt_mul_natCast]

/-- **The law of the root at one centring is the affine image of the law at the other.** -/
lemma vecRootLaw_pairAt_map (F : Measure ℝ) (g : ℝ → ℝ) (hg : Measurable g)
    (c v c' v' : ℝ) (n : ℕ) :
    vecRootLaw F (fun x => pairAt c v (g x)) n
      = (vecRootLaw F (fun x => pairAt c' v' (g x)) n).map
          (fun w : E₂ => centringMap (c' - c) w
            + Real.sqrt (n : ℝ) • (WithLp.toLp 2 ![c' - c, v' + (c' - c) ^ 2 - v] : E₂)) := by
  have hZ' : Measurable fun x : ℝ => pairAt c' v' (g x) := (measurable_pairAt c' v').comp hg
  have haff : Measurable fun w : E₂ => centringMap (c' - c) w
      + Real.sqrt (n : ℝ) • (WithLp.toLp 2 ![c' - c, v' + (c' - c) ^ 2 - v] : E₂) :=
    (measurable_centringMap _).add_const _
  rw [vecRootLaw, vecRootLaw, Measure.map_map haff (measurable_vecRoot hZ' n)]
  congr 1
  funext y
  exact vecRoot_pairAt_eq c v c' v' g y

/-- **ITEM 3 OF THE WAVE-49 RESIDUE — THE AFFINE TRANSFER.**  A bound on the modulus of the
transform of the root at one centring is a bound at the other, at the transposed frequency and
with no loss whatever: the translation contributes a unimodular factor. -/
theorem norm_charFun_vecRootLaw_pairAt_transfer (F : Measure ℝ) [IsProbabilityMeasure F]
    (g : ℝ → ℝ) (hg : Measurable g) (c v c' v' : ℝ) (n : ℕ) (t : E₂) :
    ‖charFun (vecRootLaw F (fun x => pairAt c v (g x)) n) t‖
      = ‖charFun (vecRootLaw F (fun x => pairAt c' v' (g x)) n) (centringAdj (c' - c) t)‖ := by
  set κ : E₂ := WithLp.toLp 2 ![c' - c, v' + (c' - c) ^ 2 - v] with hκ
  set a : E₂ := Real.sqrt (n : ℝ) • κ with ha
  have hZ' : Measurable fun x : ℝ => pairAt c' v' (g x) := (measurable_pairAt c' v').comp hg
  have haff : Measurable fun w : E₂ => centringMap (c' - c) w + a :=
    (measurable_centringMap _).add_const _
  rw [vecRootLaw_pairAt_map F g hg c v c' v' n, ← ha, charFun_apply, charFun_apply,
    integral_map haff.aemeasurable (by fun_prop)]
  have hpt : ∀ w : E₂,
      Complex.exp (((⟪centringMap (c' - c) w + a, t⟫ : ℝ) : ℂ) * Complex.I)
        = Complex.exp (((⟪a, t⟫ : ℝ) : ℂ) * Complex.I)
          * Complex.exp (((⟪w, centringAdj (c' - c) t⟫ : ℝ) : ℂ) * Complex.I) := by
    intro w
    rw [← Complex.exp_add, inner_add_left, inner_centringMap]
    congr 1
    push_cast
    ring
  simp only [hpt]
  have hout : (∫ w : E₂, Complex.exp (((⟪a, t⟫ : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((⟪w, centringAdj (c' - c) t⟫ : ℝ) : ℂ) * Complex.I)
        ∂(vecRootLaw F (fun x => pairAt c' v' (g x)) n))
      = Complex.exp (((⟪a, t⟫ : ℝ) : ℂ) * Complex.I)
        * ∫ w : E₂, Complex.exp (((⟪w, centringAdj (c' - c) t⟫ : ℝ) : ℂ) * Complex.I)
          ∂(vecRootLaw F (fun x => pairAt c' v' (g x)) n) :=
    integral_const_mul _ _
  rw [hout, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

lemma centringAdj_eq_add (δ : ℝ) (t : E₂) :
    centringAdj δ t = t + (2 * δ * t 1) • coordDir 0 := by
  ext i
  fin_cases i <;>
    simp [centringAdj_zero, centringAdj_one, coordDir, EuclideanSpace.single_apply]

lemma centringAdj_centringAdj (δ : ℝ) (t : E₂) : centringAdj (-δ) (centringAdj δ t) = t := by
  ext i
  fin_cases i <;> simp [centringAdj_zero, centringAdj_one] <;> ring

/-- **The change of centring distorts no radius by more than `1 + 2|δ|`.** -/
lemma norm_centringAdj_le (δ : ℝ) (t : E₂) : ‖centringAdj δ t‖ ≤ (1 + 2 * |δ|) * ‖t‖ := by
  have hcd : ‖(coordDir 0 : E₂)‖ = 1 := by
    rw [coordDir, EuclideanSpace.norm_single]
    simp
  rw [centringAdj_eq_add]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖(2 * δ * t 1) • (coordDir 0 : E₂)‖ = 2 * |δ| * |t 1| := by
    rw [norm_smul, Real.norm_eq_abs, hcd, mul_one, abs_mul, abs_mul]
    norm_num
  have h2 : |t 1| ≤ ‖t‖ := (abs_coord_le_norm t).2
  rw [h1]
  nlinarith [abs_nonneg δ, norm_nonneg t]

/-- The inverse distortion, by the same constant. -/
lemma norm_le_norm_centringAdj (δ : ℝ) (t : E₂) :
    ‖t‖ ≤ (1 + 2 * |δ|) * ‖centringAdj δ t‖ := by
  have h := norm_centringAdj_le (-δ) (centringAdj δ t)
  rwa [centringAdj_centringAdj, abs_neg] at h

/-- **ITEM 3 OF THE WAVE-49 RESIDUE, AT THE TWO CONCRETE PAIRS.**  Every transform bound on the
root of the *un*-re-centred truncated pair `studentPair F ∘ T` — the certificate, the Gaussian
bulk majorant and the Cramér tail all carry that law — is a transform bound on the root of the
re-centred pair `Zₙ = studentPair (F.map T) ∘ T`, at the transposed frequency. -/
theorem norm_charFun_vecRootLaw_recentred_transfer (F : Measure ℝ) [IsProbabilityMeasure F]
    (τ : ℝ) (n : ℕ) (t : E₂) :
    ‖charFun (vecRootLaw F
        (fun y => studentPair F (truncAt (∫ s, s ∂F) τ y)) n) t‖
      = ‖charFun (vecRootLaw F
          (fun y => studentPair (F.map (truncAt (∫ s, s ∂F) τ))
            (truncAt (∫ s, s ∂F) τ y)) n)
          (centringAdj ((∫ s, s ∂(F.map (truncAt (∫ s, s ∂F) τ))) - ∫ s, s ∂F) t)‖ := by
  simp only [studentPair_eq_pairAt]
  exact norm_charFun_vecRootLaw_pairAt_transfer F (truncAt (∫ s, s ∂F) τ)
    (measurable_truncAt _ _) _ _ _ _ n t

/-- **The distortion of the transfer is `1 + O(n^{-3/2})` at `τ = √n`,** so no radius, band or
ledger exponent of the chain moves.  This is the quantitative half of item 3. -/
theorem norm_centringAdj_recentred_le (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF1 : Integrable (fun x : ℝ => x) F)
    (hF4 : Integrable (fun x : ℝ => (x - ∫ s, s ∂F) ^ 4 ) F) {τ : ℝ} (hτ : 0 < τ) (t : E₂) :
    ‖centringAdj ((∫ s, s ∂(F.map (truncAt (∫ s, s ∂F) τ))) - ∫ s, s ∂F) t‖
      ≤ (1 + 2 * ((∫ x, (x - ∫ s, s ∂F) ^ 4 ∂F) / τ ^ 3)) * ‖t‖ := by
  refine (norm_centringAdj_le _ t).trans ?_
  have h := abs_integral_truncAt_sub_le F hF1 hF4 hτ
  have h0 : (0 : ℝ) ≤ ‖t‖ := norm_nonneg t
  nlinarith [h, h0]

end Edgeworth
end StatLean.HypothesisTesting
