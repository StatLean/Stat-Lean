import StatLean.ConcentrationInequalities.Symmetrization.Empirical
import Mathlib.MeasureTheory.Integral.Layercake

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace StatLean.HypothesisTesting

open StatLean.ConcentrationInequalities

variable {n : ℕ}

/-- The `σ`-prefix of size `j`: the indices whose `σ`-rank is `< j`. -/
private def dkwPre (σ : Equiv.Perm (Fin n)) (j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ((σ.symm i : ℕ) < j))

/-- The `±1` walk along the `σ`-order, stopped after `j` steps. -/
private def dkwWalk (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ dkwPre σ j, s i

/-- The running maximum of `|dkwWalk|` over the `n + 1` prefixes. -/
private noncomputable def dkwMax (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) : ℝ :=
  ⨆ j : Fin (n + 1), |dkwWalk σ s (j : ℕ)|

private lemma dkwPre_mono (σ : Equiv.Perm (Fin n)) {j j' : ℕ} (h : j ≤ j') :
    dkwPre σ j ⊆ dkwPre σ j' := by
  intro i hi
  simp only [dkwPre, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact lt_of_lt_of_le hi h

private lemma dkwPre_zero (σ : Equiv.Perm (Fin n)) : dkwPre σ 0 = ∅ := by
  simp [dkwPre]

private lemma dkwPre_full (σ : Equiv.Perm (Fin n)) : dkwPre σ n = Finset.univ := by
  ext i
  simp only [dkwPre, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact (σ.symm i).isLt

private lemma dkwWalk_zero (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) :
    dkwWalk σ s 0 = 0 := by
  simp [dkwWalk, dkwPre_zero]

private lemma measurable_dkwWalk (σ : Equiv.Perm (Fin n)) (j : ℕ) :
    Measurable (fun s : Fin n → ℝ => dkwWalk σ s j) :=
  Finset.measurable_sum _ fun i _ => measurable_pi_apply i

private lemma measurable_dkwMax (σ : Equiv.Perm (Fin n)) :
    Measurable (dkwMax σ) :=
  Measurable.iSup fun j => (measurable_dkwWalk σ (j : ℕ)).abs

private lemma dkwWalk_le_dkwMax (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) {j : ℕ}
    (hj : j ≤ n) : |dkwWalk σ s j| ≤ dkwMax σ s := by
  refine le_ciSup (f := fun j : Fin (n + 1) => |dkwWalk σ s (j : ℕ)|) ?_ ⟨j, by omega⟩
  exact (Set.finite_range _).bddAbove

private lemma dkwMax_nonneg (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) :
    0 ≤ dkwMax σ s :=
  le_trans (abs_nonneg _) (dkwWalk_le_dkwMax σ s (Nat.zero_le n))

private lemma exists_dkwMax_eq (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) :
    ∃ j : Fin (n + 1), dkwMax σ s = |dkwWalk σ s (j : ℕ)| := by
  obtain ⟨j0, hj0⟩ := Finite.exists_max (fun j : Fin (n + 1) => |dkwWalk σ s (j : ℕ)|)
  refine ⟨j0, le_antisymm (ciSup_le hj0) ?_⟩
  exact dkwWalk_le_dkwMax σ s (Nat.lt_succ_iff.mp j0.isLt)

/-! ### The reflected sign pattern -/

private noncomputable def dkwSign (σ : Equiv.Perm (Fin n)) (j : ℕ) : Fin n → ℝ :=
  fun i => if i ∈ dkwPre σ j then 1 else -1

private lemma dkwSign_pm (σ : Equiv.Perm (Fin n)) (j : ℕ) (i : Fin n) :
    dkwSign σ j i = 1 ∨ dkwSign σ j i = -1 := by
  unfold dkwSign; split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma dkwWalk_refl_le (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) {j l : ℕ}
    (hl : l ≤ j) :
    dkwWalk σ (fun i => dkwSign σ j i * s i) l = dkwWalk σ s l := by
  refine Finset.sum_congr rfl fun i hi => ?_
  have : i ∈ dkwPre σ j := dkwPre_mono σ hl hi
  simp [dkwSign, this]

private lemma dkwWalk_refl_full (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ) (j : ℕ) :
    dkwWalk σ (fun i => dkwSign σ j i * s i) n
      = 2 * dkwWalk σ s j - dkwWalk σ s n := by
  have hj : dkwPre σ j ⊆ dkwPre σ n := by rw [dkwPre_full]; exact Finset.subset_univ _
  have hsplit : ∑ i ∈ dkwPre σ n, dkwSign σ j i * s i
      = ∑ i ∈ dkwPre σ n \ dkwPre σ j, dkwSign σ j i * s i
        + ∑ i ∈ dkwPre σ j, dkwSign σ j i * s i :=
    (Finset.sum_sdiff hj).symm
  have h1 : ∑ i ∈ dkwPre σ j, dkwSign σ j i * s i = dkwWalk σ s j :=
    Finset.sum_congr rfl fun i hi => by simp [dkwSign, hi]
  have hsub : dkwWalk σ s n - dkwWalk σ s j = ∑ i ∈ dkwPre σ n \ dkwPre σ j, s i := by
    simp only [dkwWalk]
    exact (Finset.sum_sdiff_eq_sub hj).symm
  have h2 : ∑ i ∈ dkwPre σ n \ dkwPre σ j, dkwSign σ j i * s i
      = -(dkwWalk σ s n - dkwWalk σ s j) := by
    rw [hsub, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i hi => ?_
    have : i ∉ dkwPre σ j := (Finset.mem_sdiff.mp hi).2
    simp [dkwSign, this]
  simp only [dkwWalk] at hsplit h1 h2 ⊢
  rw [hsplit, h1, h2]
  ring



namespace Levy

variable (σ : Equiv.Perm (Fin n))

/-- The first-passage level sets of the walk. -/
private def dkwPass (a : ℝ) (j : ℕ) : Set (Fin n → ℝ) :=
  {s | ∀ l < j, |dkwWalk σ s l| < a} ∩ {s | a ≤ |dkwWalk σ s j|}

private lemma measurableSet_dkwPass (a : ℝ) (j : ℕ) :
    MeasurableSet (dkwPass σ a j) := by
  have h1 : {s : Fin n → ℝ | ∀ l < j, |dkwWalk σ s l| < a}
      = ⋂ l ∈ (Set.Iio j : Set ℕ), {s : Fin n → ℝ | |dkwWalk σ s l| < a} := by
    ext s; simp [Set.mem_iInter]
  rw [dkwPass, h1]
  refine MeasurableSet.inter (MeasurableSet.biInter (Set.to_countable _) fun l _ => ?_) ?_
  · exact measurableSet_lt (measurable_dkwWalk σ l).abs measurable_const
  · exact measurableSet_le measurable_const (measurable_dkwWalk σ j).abs

private lemma dkwPass_disjoint (a : ℝ) :
    (Finset.range (n + 1) : Finset ℕ).toSet.PairwiseDisjoint (dkwPass σ a) := by
  intro j _ j' _ hne
  refine Set.disjoint_left.mpr fun s hs hs' => ?_
  rcases lt_or_gt_of_ne hne with h | h
  · exact absurd hs.2 (not_le.mpr (hs'.1 j h))
  · exact absurd hs'.2 (not_le.mpr (hs.1 j' h))

private lemma dkwMax_subset_iUnion {a : ℝ} :
    {s : Fin n → ℝ | a ≤ dkwMax σ s} ⊆ ⋃ j ∈ Finset.range (n + 1), dkwPass σ a j := by
  intro s hs
  obtain ⟨j0, hj0⟩ := exists_dkwMax_eq σ s
  have hex : ∃ l, a ≤ |dkwWalk σ s l| := ⟨(j0 : ℕ), hj0 ▸ hs⟩
  classical
  set j := Nat.find hex with hjdef
  have hjspec : a ≤ |dkwWalk σ s j| := Nat.find_spec hex
  have hjle : j ≤ n := le_trans (Nat.find_le (hj0 ▸ hs)) (Nat.lt_succ_iff.mp j0.isLt)
  refine Set.mem_biUnion (Finset.mem_range.mpr (by omega)) ⟨fun l hl => ?_, hjspec⟩
  exact not_le.mp (Nat.find_min hex hl)

private lemma signVec_dkwPass_le (a : ℝ) (ha : 0 < a) (j : ℕ) :
    signVec n (dkwPass σ a j)
      ≤ 2 * signVec n (dkwPass σ a j ∩ {s | a ≤ |dkwWalk σ s n|}) := by
  classical
  set R : (Fin n → ℝ) → (Fin n → ℝ) := fun s i => dkwSign σ j i * s i with hR
  have hRmeas : Measurable R :=
    measurable_pi_lambda _ fun i => (measurable_pi_apply i).const_mul _
  have hmap : (signVec n).map R = signVec n := signVec_map_mul_pm (dkwSign_pm σ j)
  set B : Set (Fin n → ℝ) := {s | a ≤ |dkwWalk σ s n|} with hB
  have hBmeas : MeasurableSet B := measurableSet_le measurable_const (measurable_dkwWalk σ n).abs
  have hSmeas : MeasurableSet (dkwPass σ a j ∩ B) :=
    (measurableSet_dkwPass σ a j).inter hBmeas
  -- the reflection preserves the measure of the target set
  have hpre : signVec n (R ⁻¹' (dkwPass σ a j ∩ B)) = signVec n (dkwPass σ a j ∩ B) := by
    conv_rhs => rw [← hmap]
    rw [Measure.map_apply hRmeas hSmeas]
  -- coverage
  have hcover : dkwPass σ a j ⊆ (dkwPass σ a j ∩ B) ∪ (R ⁻¹' (dkwPass σ a j ∩ B)) := by
    intro s hs
    by_cases hb : a ≤ |dkwWalk σ s n|
    · exact Or.inl ⟨hs, hb⟩
    · push_neg at hb
      refine Or.inr ⟨⟨fun l hl => ?_, ?_⟩, ?_⟩
      · change |dkwWalk σ (fun i => dkwSign σ j i * s i) l| < a
        rw [dkwWalk_refl_le σ s (le_of_lt hl)]; exact hs.1 l hl
      · change a ≤ |dkwWalk σ (fun i => dkwSign σ j i * s i) j|
        rw [dkwWalk_refl_le σ s (le_refl j)]; exact hs.2
      · change a ≤ |dkwWalk σ (fun i => dkwSign σ j i * s i) n|
        rw [dkwWalk_refl_full σ s j]
        have h1 : a ≤ |dkwWalk σ s j| := hs.2
        have h2 : |2 * dkwWalk σ s j - dkwWalk σ s n|
            ≥ 2 * |dkwWalk σ s j| - |dkwWalk σ s n| := by
          have := abs_sub_abs_le_abs_sub (2 * dkwWalk σ s j) (dkwWalk σ s n)
          rw [abs_mul] at this
          simp only [abs_two] at this
          linarith
        linarith
  calc signVec n (dkwPass σ a j)
      ≤ signVec n ((dkwPass σ a j ∩ B) ∪ (R ⁻¹' (dkwPass σ a j ∩ B))) := measure_mono hcover
    _ ≤ signVec n (dkwPass σ a j ∩ B) + signVec n (R ⁻¹' (dkwPass σ a j ∩ B)) :=
        measure_union_le _ _
    _ = 2 * signVec n (dkwPass σ a j ∩ B) := by rw [hpre]; ring

/-- **Lévy's maximal inequality for the `±1` walk.** -/
private lemma dkw_levy {a : ℝ} (ha : 0 < a) :
    signVec n {s | a ≤ dkwMax σ s} ≤ 2 * signVec n {s | a ≤ |dkwWalk σ s n|} := by
  classical
  set B : Set (Fin n → ℝ) := {s | a ≤ |dkwWalk σ s n|} with hB
  have hBmeas : MeasurableSet B := measurableSet_le measurable_const (measurable_dkwWalk σ n).abs
  have hdisj : (Finset.range (n + 1) : Finset ℕ).toSet.PairwiseDisjoint
      (fun j => dkwPass σ a j ∩ B) := fun j hj j' hj' hne =>
    Disjoint.mono Set.inter_subset_left Set.inter_subset_left
      (dkwPass_disjoint σ a hj hj' hne)
  calc signVec n {s : Fin n → ℝ | a ≤ dkwMax σ s}
      ≤ signVec n (⋃ j ∈ Finset.range (n + 1), dkwPass σ a j) :=
        measure_mono (dkwMax_subset_iUnion σ)
    _ ≤ ∑ j ∈ Finset.range (n + 1), signVec n (dkwPass σ a j) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range (n + 1), 2 * signVec n (dkwPass σ a j ∩ B) :=
        Finset.sum_le_sum fun j _ => signVec_dkwPass_le σ a ha j
    _ = 2 * ∑ j ∈ Finset.range (n + 1), signVec n (dkwPass σ a j ∩ B) := by
        rw [Finset.mul_sum]
    _ = 2 * signVec n (⋃ j ∈ Finset.range (n + 1), (dkwPass σ a j ∩ B)) := by
        rw [measure_biUnion_finset hdisj
          (fun j _ => (measurableSet_dkwPass σ a j).inter hBmeas)]
    _ ≤ 2 * signVec n B := by
        refine mul_le_mul_left' (measure_mono ?_) 2
        exact Set.iUnion₂_subset fun j _ => Set.inter_subset_right

end Levy


section Moments

variable (σ : Equiv.Perm (Fin n))

private lemma signVec_ae_abs_le : ∀ᵐ s ∂signVec n, ∀ i, |s i| ≤ 1 := by
  filter_upwards [signVec_ae_pm n] with s hs i
  rcases hs i with h | h <;> simp [h]

private lemma dkwWalk_abs_le {s : Fin n → ℝ} (hs : ∀ i, |s i| ≤ 1) (j : ℕ) :
    |dkwWalk σ s j| ≤ n := by
  calc |dkwWalk σ s j| ≤ ∑ i ∈ dkwPre σ j, |s i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ dkwPre σ j, (1 : ℝ) := Finset.sum_le_sum fun i _ => hs i
    _ = ((dkwPre σ j).card : ℝ) := by simp
    _ ≤ (n : ℝ) := by
        have := Finset.card_le_univ (dkwPre σ j)
        simp only [Finset.card_univ, Fintype.card_fin] at this
        exact_mod_cast this

private lemma dkwMax_abs_le {s : Fin n → ℝ} (hs : ∀ i, |s i| ≤ 1) :
    dkwMax σ s ≤ n := by
  obtain ⟨j, hj⟩ := exists_dkwMax_eq σ s
  rw [hj]; exact dkwWalk_abs_le σ hs _

private lemma integrable_dkwMax : Integrable (dkwMax σ) (signVec n) := by
  refine Integrable.mono' (integrable_const (n : ℝ))
    (measurable_dkwMax σ).aestronglyMeasurable ?_
  filter_upwards [signVec_ae_abs_le (n := n)] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (dkwMax_nonneg σ s)]
  exact dkwMax_abs_le σ hs

private lemma integrable_dkwWalk (j : ℕ) :
    Integrable (fun s => dkwWalk σ s j) (signVec n) := by
  refine Integrable.mono' (integrable_const (n : ℝ))
    (measurable_dkwWalk σ j).aestronglyMeasurable ?_
  filter_upwards [signVec_ae_abs_le (n := n)] with s hs
  rw [Real.norm_eq_abs]
  exact dkwWalk_abs_le σ hs j

private lemma integrable_dkwWalk_sq (j : ℕ) :
    Integrable (fun s => dkwWalk σ s j ^ 2) (signVec n) := by
  refine Integrable.mono' (integrable_const ((n : ℝ) ^ 2))
    ((measurable_dkwWalk σ j).pow_const 2).aestronglyMeasurable ?_
  filter_upwards [signVec_ae_abs_le (n := n)] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h1 : |dkwWalk σ s j| ≤ (n : ℝ) := dkwWalk_abs_le σ hs j
  have h0 : (0 : ℝ) ≤ |dkwWalk σ s j| := abs_nonneg _
  have h2 : dkwWalk σ s j ^ 2 = |dkwWalk σ s j| ^ 2 := (sq_abs _).symm
  rw [h2]
  nlinarith

/-! Coordinate moments of the sign vector. -/

private lemma integral_coord (i : Fin n) {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ s, f (s i) ∂signVec n = ∫ x, f x ∂radLaw := by
  have hmp := measurePreserving_eval_signVec n i
  conv_rhs => rw [← hmp.map_eq]
  rw [integral_map (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable]

private lemma integrable_coord (i : Fin n) :
    Integrable (fun s : Fin n → ℝ => s i) (signVec n) := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (measurable_pi_apply i).aestronglyMeasurable ?_
  filter_upwards [signVec_ae_abs_le (n := n)] with s hs
  rw [Real.norm_eq_abs]; exact hs i

private lemma integrable_coord_mul (i j : Fin n) :
    Integrable (fun s : Fin n → ℝ => s i * s j) (signVec n) := by
  refine Integrable.mono' (integrable_const (1 : ℝ))
    (((measurable_pi_apply i).mul (measurable_pi_apply j))).aestronglyMeasurable ?_
  filter_upwards [signVec_ae_abs_le (n := n)] with s hs
  rw [Real.norm_eq_abs, abs_mul]
  have h1 := hs i
  have h2 := hs j
  nlinarith [abs_nonneg (s i), abs_nonneg (s j)]

private lemma integral_coord_id (i : Fin n) : ∫ s : Fin n → ℝ, s i ∂signVec n = 0 := by
  have h := integral_coord (n := n) i (f := fun x => x) measurable_id
  rw [h]; exact radLaw_integral_id

private lemma integral_coord_sq (i : Fin n) :
    ∫ s : Fin n → ℝ, s i * s i ∂signVec n = 1 := by
  have h := integral_coord (n := n) i (f := fun x => x * x)
    (measurable_id.mul measurable_id)
  rw [h, radLaw_integral]; norm_num

private lemma integral_coord_cross {i j : Fin n} (hij : i ≠ j) :
    ∫ s : Fin n → ℝ, s i * s j ∂signVec n = 0 := by
  have hind : IndepFun (fun s : Fin n → ℝ => s i) (fun s : Fin n → ℝ => s j) (signVec n) :=
    (iIndepFun_eval_signVec n).indepFun hij
  rw [hind.integral_fun_mul_eq_mul_integral (measurable_pi_apply i).aestronglyMeasurable
    (measurable_pi_apply j).aestronglyMeasurable]
  change (∫ s : Fin n → ℝ, s i ∂signVec n) * (∫ s : Fin n → ℝ, s j ∂signVec n) = 0
  rw [integral_coord_id, zero_mul]

private lemma integral_dkwWalk_sq_full :
    ∫ s, dkwWalk σ s n ^ 2 ∂signVec n = n := by
  classical
  have hW : (fun s : Fin n → ℝ => dkwWalk σ s n ^ 2)
      = fun s : Fin n → ℝ => ∑ i, ∑ j, s i * s j := by
    funext s
    simp only [dkwWalk, dkwPre_full]
    rw [sq, Finset.sum_mul_sum]
  rw [hW]
  rw [integral_finset_sum _ (fun i _ =>
    integrable_finset_sum _ (fun j _ => integrable_coord_mul i j))]
  have hrow : ∀ i : Fin n, ∫ s : Fin n → ℝ, ∑ j, s i * s j ∂signVec n = 1 := by
    intro i
    rw [integral_finset_sum _ (fun j _ => integrable_coord_mul i j)]
    rw [Finset.sum_eq_single i (fun j _ hji => integral_coord_cross (Ne.symm hji))
      (fun h => absurd (Finset.mem_univ i) h)]
    exact integral_coord_sq i
  rw [Finset.sum_congr rfl (fun i _ => hrow i)]
  simp

private lemma integral_abs_dkwWalk_le (hn : 0 < n) :
    ∫ s, |dkwWalk σ s n| ∂signVec n ≤ Real.sqrt n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hss : Real.sqrt n * Real.sqrt n = (n : ℝ) := Real.mul_self_sqrt hnR.le
  have hpt : ∀ s : Fin n → ℝ,
      |dkwWalk σ s n| ≤ (dkwWalk σ s n ^ 2 + (n : ℝ)) / (2 * Real.sqrt n) := by
    intro s
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (|dkwWalk σ s n| - Real.sqrt n), sq_abs (dkwWalk σ s n)]
  have hint2 : Integrable (fun s : Fin n → ℝ =>
      (dkwWalk σ s n ^ 2 + (n : ℝ)) / (2 * Real.sqrt n)) (signVec n) :=
    ((integrable_dkwWalk_sq σ n).add (integrable_const _)).div_const _
  calc ∫ s, |dkwWalk σ s n| ∂signVec n
      ≤ ∫ s, (dkwWalk σ s n ^ 2 + (n : ℝ)) / (2 * Real.sqrt n) ∂signVec n :=
        integral_mono ((integrable_dkwWalk σ n).abs) hint2 hpt
    _ = ((∫ s, dkwWalk σ s n ^ 2 ∂signVec n) + (n : ℝ)) / (2 * Real.sqrt n) := by
        rw [integral_div, integral_add (integrable_dkwWalk_sq σ n) (integrable_const _)]
        simp
    _ = Real.sqrt n := by
        rw [integral_dkwWalk_sq_full σ]
        field_simp
        nlinarith [hss]

/-- **The `L¹` maximal bound**: `E max_j |S_j| ≤ 2 √n`. -/
private lemma integral_dkwMax_le (hn : 0 < n) :
    ∫ s, dkwMax σ s ∂signVec n ≤ 2 * Real.sqrt n := by
  have hAbsInt : Integrable (fun s => |dkwWalk σ s n|) (signVec n) :=
    (integrable_dkwWalk σ n).abs
  -- layer cake in `ℝ≥0∞`
  have hlc1 : ∫⁻ s, ENNReal.ofReal (dkwMax σ s) ∂signVec n
      = ∫⁻ t in Set.Ioi (0 : ℝ), signVec n {s | t ≤ dkwMax σ s} :=
    lintegral_eq_lintegral_meas_le _
      (Filter.Eventually.of_forall (dkwMax_nonneg σ)) (measurable_dkwMax σ).aemeasurable
  have hlc2 : ∫⁻ s, ENNReal.ofReal |dkwWalk σ s n| ∂signVec n
      = ∫⁻ t in Set.Ioi (0 : ℝ), signVec n {s | t ≤ |dkwWalk σ s n|} :=
    lintegral_eq_lintegral_meas_le _
      (Filter.Eventually.of_forall fun s => abs_nonneg _)
      (measurable_dkwWalk σ n).abs.aemeasurable
  have hmono : ∫⁻ t in Set.Ioi (0 : ℝ), signVec n {s | t ≤ dkwMax σ s}
      ≤ ∫⁻ t in Set.Ioi (0 : ℝ), 2 * signVec n {s | t ≤ |dkwWalk σ s n|} := by
    refine lintegral_mono_ae ?_
    filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (0 : ℝ)))] with t ht
    exact Levy.dkw_levy σ ht
  have hconst : ∫⁻ t in Set.Ioi (0 : ℝ), 2 * signVec n {s | t ≤ |dkwWalk σ s n|}
      = 2 * ∫⁻ t in Set.Ioi (0 : ℝ), signVec n {s | t ≤ |dkwWalk σ s n|} :=
    lintegral_const_mul' _ _ (by simp)
  have hkey : ∫⁻ s, ENNReal.ofReal (dkwMax σ s) ∂signVec n
      ≤ 2 * ∫⁻ s, ENNReal.ofReal |dkwWalk σ s n| ∂signVec n := by
    rw [hlc1, hlc2]; exact hmono.trans_eq hconst
  -- transfer to the Bochner integral
  have hfin : ∫⁻ s, ENNReal.ofReal |dkwWalk σ s n| ∂signVec n ≠ ⊤ := by
    have h := hAbsInt.hasFiniteIntegral
    have heq : ∀ s : Fin n → ℝ, ENNReal.ofReal |dkwWalk σ s n| = ‖|dkwWalk σ s n|‖ₑ :=
      fun s => (Real.enorm_eq_ofReal (abs_nonneg _)).symm
    simp_rw [heq]
    exact h.ne
  have he1 : ∫ s, dkwMax σ s ∂signVec n
      = (∫⁻ s, ENNReal.ofReal (dkwMax σ s) ∂signVec n).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (dkwMax_nonneg σ))
      (measurable_dkwMax σ).aestronglyMeasurable
  have he2 : ∫ s, |dkwWalk σ s n| ∂signVec n
      = (∫⁻ s, ENNReal.ofReal |dkwWalk σ s n| ∂signVec n).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun s => abs_nonneg _)
      (measurable_dkwWalk σ n).abs.aestronglyMeasurable
  calc ∫ s, dkwMax σ s ∂signVec n
      = (∫⁻ s, ENNReal.ofReal (dkwMax σ s) ∂signVec n).toReal := he1
    _ ≤ (2 * ∫⁻ s, ENNReal.ofReal |dkwWalk σ s n| ∂signVec n).toReal := by
        exact ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hfin) hkey
    _ = 2 * ∫ s, |dkwWalk σ s n| ∂signVec n := by
        rw [he2, ENNReal.toReal_mul]; norm_num
    _ ≤ 2 * Real.sqrt n := by
        have := integral_abs_dkwWalk_le σ hn
        linarith

end Moments


end StatLean.HypothesisTesting
