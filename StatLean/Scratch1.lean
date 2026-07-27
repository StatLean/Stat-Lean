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

end StatLean.HypothesisTesting
