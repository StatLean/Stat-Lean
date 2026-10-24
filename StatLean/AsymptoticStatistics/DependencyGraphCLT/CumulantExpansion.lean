/-
Copyright (c) 2026 Benjamin O. Harrison, Gustavo Canavire Bacarreza, David Jacho-Chavez and
Fernando Rios-Avila.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Jacho-Chávez
-/
import StatLean.AsymptoticStatistics.ForMathlib.Probability.CumulantCharFun

/-!
# The multilinear expansion of a cumulant of a sum

Let $S = \sum_{a \in t} Z_a$ be a finite sum of almost surely bounded real random variables.
This file proves Janson's identity (4.2),
$$ \kappa_j(S) \;=\; \sum_{a_1 \in t} \cdots \sum_{a_j \in t}
     \kappa(Z_{a_1}, \dots, Z_{a_j}), $$
which expands the $j$-th cumulant of the sum into $|t|^j$ mixed cumulants by multilinearity,
simultaneously in every slot. The summands are assumed almost surely bounded, so every
integrability side condition holds.

**Reference.** S. Janson, "Normal convergence by higher semiinvariants with applications to
sums of dependent random variables and random graphs", *Ann. Probab.* **16** (1988), 305–312,
display (4.2) in the proof of Lemma 4.

**Proof formalization notes.** The mixed cumulant is linear in one slot over a finite sum
(`Cumulant.mixedCumulant_update_sum`), via the partition (Möbius) formula. The expansion is
proved by induction on the set `u` of slots already expanded: `Cumulant.mixFam` carries the
whole sum in the slots of `u` and a selected summand in the others, and each induction step
splits a sum over `Fintype.piFinset` at one coordinate (`Cumulant.sum_piFinset_split`).

## Main results

* `Cumulant.sum_piFinset_split`: splitting a sum over `Fintype.piFinset` at one coordinate.
* `Cumulant.mixedCumulant_update_sum`: linearity of a mixed cumulant in one slot over a finite sum.
* `Cumulant.mixFam`, `Cumulant.mixedCumulant_mixFam_eq`: the slot-by-slot induction.
* `Cumulant.cumulant_sum_eq`: the expansion (4.2).
-/

open Finset MeasureTheory ProbabilityTheory

namespace StatLean.AsymptoticStatistics.Cumulant

/-! ### Sums over `Fintype.piFinset` -/

section PiFinset

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {α : Type*}

/-- Splitting a sum over `Fintype.piFinset T` according to the value of one coordinate. -/
lemma sum_piFinset_split {M : Type*} [AddCommMonoid M] (T : ι → Finset α) (i₀ : ι)
    (F : (ι → α) → M) :
    ∑ φ ∈ Fintype.piFinset T, F φ
      = ∑ a ∈ T i₀, ∑ φ ∈ Fintype.piFinset (Function.update T i₀ {a}), F φ := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun φ : ι → α => φ i₀) (t := T i₀)
      (fun φ hφ => (Fintype.mem_piFinset.mp hφ) i₀) F]
  exact Finset.sum_congr rfl fun a ha => by
    rw [Fintype.piFinset_update_singleton_eq_filter_piFinset_eq T i₀ ha]

end PiFinset

/-! ### One-slot linearity for a finite sum -/

section UpdateSum

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [DecidableEq ι] {α : Type*}

/-- Linearity of a mixed cumulant in one argument, for a finite sum. -/
theorem mixedCumulant_update_sum (μ : Measure Ω) (X : ι → Ω → ℝ) {i₀ : ι} {s : Finset ι}
    (hi : i₀ ∈ s) (t : Finset α) (Z : α → Ω → ℝ)
    (hint : ∀ (B : Finset ι) (a : α), a ∈ t →
      Integrable (fun ω => Z a ω * ∏ i ∈ B.erase i₀, X i ω) μ) :
    mixedCumulant μ (Function.update X i₀ (fun ω => ∑ a ∈ t, Z a ω)) s
      = ∑ a ∈ t, mixedCumulant μ (Function.update X i₀ (Z a)) s := by
  classical
  simp only [mixedCumulant, mobius]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π _ => ?_
  have hi₀P : i₀ ∈ π.part i₀ := (Finpartition.mem_part_self π).mpr hi
  have hsum : jointMoment μ (Function.update X i₀ (fun ω => ∑ a ∈ t, Z a ω)) (π.part i₀)
      = ∑ a ∈ t, jointMoment μ (Function.update X i₀ (Z a)) (π.part i₀) := by
    rw [jointMoment_update_of_mem μ X i₀ _ hi₀P]
    have hcongr : (fun ω => (∑ a ∈ t, Z a ω) * ∏ i ∈ (π.part i₀).erase i₀, X i ω)
        = fun ω => ∑ a ∈ t, Z a ω * ∏ i ∈ (π.part i₀).erase i₀, X i ω := by
      funext ω; rw [Finset.sum_mul]
    rw [hcongr, integral_finsetSum t (fun a ha => hint (π.part i₀) a ha)]
    exact Finset.sum_congr rfl fun a _ => (jointMoment_update_of_mem μ X i₀ (Z a) hi₀P).symm
  rw [prod_parts_update μ X hi π, hsum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [prod_parts_update μ X hi π]

end UpdateSum

/-! ### The simultaneous expansion -/

section Expansion

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [DecidableEq ι] [Fintype ι]
  {α : Type*}

/-- The intermediate family of the expansion, with the whole sum `∑_{a ∈ t} Z a` in the slots in
`u` and the summand selected by `base` in the other slots. -/
noncomputable def mixFam (Z : α → Ω → ℝ) (t : Finset α) (u : Finset ι) (base : ι → α) :
    ι → Ω → ℝ :=
  fun i => if i ∈ u then (fun ω => ∑ a ∈ t, Z a ω) else Z (base i)

omit [Fintype ι] in
lemma measurable_mixFam {Z : α → Ω → ℝ} (hZm : ∀ a, Measurable (Z a)) (t : Finset α)
    (u : Finset ι) (base : ι → α) (i : ι) : Measurable (mixFam Z t u base i) := by
  by_cases hiu : i ∈ u
  · have h : mixFam Z t u base i = fun ω => ∑ a ∈ t, Z a ω := by simp [mixFam, hiu]
    rw [h]
    exact Finset.measurable_sum _ fun a _ => hZm a
  · have h : mixFam Z t u base i = Z (base i) := by simp [mixFam, hiu]
    rw [h]
    exact hZm _

omit [Fintype ι] in
lemma abs_mixFam_le {μ : Measure Ω} {Z : α → Ω → ℝ} {t : Finset α} {A : ℝ} (hA : 0 ≤ A)
    (hZb : ∀ a ∈ t, ∀ᵐ ω ∂μ, |Z a ω| ≤ A) {base : ι → α} (hbase : ∀ i, base i ∈ t)
    (u : Finset ι) (i : ι) :
    ∀ᵐ ω ∂μ, |mixFam Z t u base i ω| ≤ ((#t : ℝ) + 1) * A := by
  have hall : ∀ᵐ ω ∂μ, ∀ a ∈ (↑t : Set α), |Z a ω| ≤ A :=
    (ae_ball_iff (Set.to_countable (↑t : Set α))).mpr (fun a ha => hZb a ha)
  have hexp : ((#t : ℝ) + 1) * A = (#t : ℝ) * A + A := by ring
  have hnn : (0 : ℝ) ≤ (#t : ℝ) * A := mul_nonneg (Nat.cast_nonneg _) hA
  filter_upwards [hall] with ω hω
  by_cases hiu : i ∈ u
  · have h : mixFam Z t u base i = fun ω => ∑ a ∈ t, Z a ω := by simp [mixFam, hiu]
    rw [h]
    have : |∑ a ∈ t, Z a ω| ≤ (#t : ℝ) * A := by
      calc |∑ a ∈ t, Z a ω| ≤ ∑ a ∈ t, |Z a ω| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _a ∈ t, A := Finset.sum_le_sum (fun a ha => hω a (by simpa using ha))
        _ = (#t : ℝ) * A := by rw [Finset.sum_const, nsmul_eq_mul]
    linarith
  · have h : mixFam Z t u base i = Z (base i) := by simp [mixFam, hiu]
    rw [h]
    have : |Z (base i) ω| ≤ A := hω _ (by simpa using hbase i)
    linarith

omit [Fintype ι] in
lemma integrable_prod_mixFam [Finite ι] {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : α → Ω → ℝ}
    {t : Finset α} {A : ℝ} (hA : 0 ≤ A) (hZm : ∀ a, Measurable (Z a))
    (hZb : ∀ a ∈ t, ∀ᵐ ω ∂μ, |Z a ω| ≤ A) {base : ι → α} (hbase : ∀ i, base i ∈ t)
    (u : Finset ι) {a : α} (ha : a ∈ t) (B : Finset ι) :
    Integrable (fun ω => Z a ω * ∏ i ∈ B, mixFam Z t u base i ω) μ := by
  have hC : (0 : ℝ) ≤ ((#t : ℝ) + 1) * A :=
    mul_nonneg (by positivity) hA
  refine Integrable.of_bound ?_ (A * (((#t : ℝ) + 1) * A) ^ #B) ?_
  · exact ((hZm a).mul (Finset.measurable_prod _ fun i _ =>
      measurable_mixFam hZm t u base i)).aestronglyMeasurable
  · have hallb : ∀ᵐ ω ∂μ, ∀ i : ι, |mixFam Z t u base i ω| ≤ ((#t : ℝ) + 1) * A :=
      ae_all_iff.mpr (fun i => abs_mixFam_le hA hZb hbase u i)
    filter_upwards [hZb a ha, hallb] with ω h1 h2
    rw [Real.norm_eq_abs, abs_mul, Finset.abs_prod]
    refine mul_le_mul h1 ?_ (Finset.prod_nonneg fun _ _ => abs_nonneg _) hA
    calc ∏ i ∈ B, |mixFam Z t u base i ω| ≤ ∏ _i ∈ B, (((#t : ℝ) + 1) * A) :=
          Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun i _ => h2 i)
      _ = (((#t : ℝ) + 1) * A) ^ #B := by rw [Finset.prod_const]

/-- The expansion with the slots in `u` summed, by induction on `u`. -/
theorem mixedCumulant_mixFam_eq {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : α → Ω → ℝ}
    {t : Finset α} {A : ℝ} (hA : 0 ≤ A) (hZm : ∀ a, Measurable (Z a))
    (hZb : ∀ a ∈ t, ∀ᵐ ω ∂μ, |Z a ω| ≤ A) (s : Finset ι) :
    ∀ u : Finset ι, u ⊆ s → ∀ base : ι → α, (∀ i, base i ∈ t) →
      mixedCumulant μ (mixFam Z t u base) s
        = ∑ φ ∈ Fintype.piFinset (fun i => if i ∈ u then t else {base i}),
            mixedCumulant μ (fun i => Z (φ i)) s := by
  classical
  intro u
  induction u using Finset.induction_on with
  | empty =>
      intro _ base _
      have hT : (fun i => if i ∈ (∅ : Finset ι) then t else ({base i} : Finset α))
          = fun i => ({base i} : Finset α) := by
        funext i; simp
      rw [hT, Fintype.piFinset_singleton, Finset.sum_singleton]
      have hf : mixFam Z t (∅ : Finset ι) base = fun i => Z (base i) := by
        funext i; simp [mixFam]
      rw [hf]
  | insert i₀ u hi₀u ih =>
      intro hsub base hbase
      have hi₀s : i₀ ∈ s := hsub (Finset.mem_insert_self i₀ u)
      have husub : u ⊆ s := fun x hx => hsub (Finset.mem_insert_of_mem hx)
      have hfam : mixFam Z t (insert i₀ u) base
          = Function.update (mixFam Z t u base) i₀ (fun ω => ∑ a ∈ t, Z a ω) := by
        funext i
        rcases eq_or_ne i i₀ with rfl | hne
        · simp [mixFam]
        · rw [Function.update_of_ne hne]
          simp [mixFam, Finset.mem_insert, hne]
      have hstep : ∀ a : α, Function.update (mixFam Z t u base) i₀ (Z a)
          = mixFam Z t u (Function.update base i₀ a) := by
        intro a
        funext i
        rcases eq_or_ne i i₀ with rfl | hne
        · simp [mixFam, hi₀u]
        · rw [Function.update_of_ne hne]
          simp [mixFam, Function.update_of_ne hne]
      rw [hfam, mixedCumulant_update_sum μ _ hi₀s t Z
        (fun B a ha => integrable_prod_mixFam hA hZm hZb hbase u ha (B.erase i₀))]
      have hbase' : ∀ a ∈ t, ∀ i, (Function.update base i₀ a) i ∈ t := by
        intro a ha i
        rcases eq_or_ne i i₀ with rfl | hne
        · simpa using ha
        · simpa [Function.update_of_ne hne] using hbase i
      rw [Finset.sum_congr rfl (fun a ha => by
        rw [hstep a, ih husub (Function.update base i₀ a) (hbase' a ha)])]
      have hT : ∀ a : α,
          (fun i => if i ∈ u then t else ({Function.update base i₀ a i} : Finset α))
            = Function.update
                (fun i => if i ∈ insert i₀ u then t else ({base i} : Finset α)) i₀ {a} := by
        intro a
        funext i
        rcases eq_or_ne i i₀ with rfl | hne
        · simp [hi₀u]
        · rw [Function.update_of_ne hne, Function.update_of_ne hne]
          simp [Finset.mem_insert, hne]
      simp only [hT]
      rw [sum_piFinset_split (fun i => if i ∈ insert i₀ u then t else ({base i} : Finset α)) i₀
        (fun φ => mixedCumulant μ (fun i => Z (φ i)) s)]
      refine Finset.sum_congr ?_ (fun a _ => rfl)
      simp

/-- **Janson (1988), (4.2).** The `j`-th cumulant of a finite sum expands into `N^j` mixed
cumulants: `κ_j (∑_{a ∈ t} Z a) = ∑_{φ : Fin j → t} κ (Z_{φ 1}, …, Z_{φ j})`. -/
theorem cumulant_sum_eq {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : α → Ω → ℝ} {t : Finset α} {A : ℝ} (hA : 0 ≤ A) (hZm : ∀ a, Measurable (Z a))
    (hZb : ∀ a ∈ t, ∀ᵐ ω ∂μ, |Z a ω| ≤ A) (j : ℕ) :
    cumulant (fun ω => ∑ a ∈ t, Z a ω) j μ
      = ∑ φ ∈ Fintype.piFinset (fun _ : Fin j => t),
          mixedCumulant μ (fun k => Z (φ k)) (univ : Finset (Fin j)) := by
  classical
  have main : ∀ base : Fin j → α, (∀ i, base i ∈ t) →
      cumulant (fun ω => ∑ a ∈ t, Z a ω) j μ
        = ∑ φ ∈ Fintype.piFinset (fun _ : Fin j => t),
            mixedCumulant μ (fun k => Z (φ k)) (univ : Finset (Fin j)) := by
    intro base hbase
    have key := mixedCumulant_mixFam_eq (ι := Fin j) hA hZm hZb (univ : Finset (Fin j))
      univ (subset_refl _) base hbase
    have h1 : mixFam Z t (univ : Finset (Fin j)) base
        = fun _ : Fin j => (fun ω => ∑ a ∈ t, Z a ω) := by
      funext i; simp [mixFam]
    have h2 : (fun i : Fin j => if i ∈ (univ : Finset (Fin j)) then t else ({base i} : Finset α))
        = fun _ => t := by
      funext i; simp
    rw [h2] at key
    rw [cumulant, ← h1, key]
  rcases isEmpty_or_nonempty (Fin j) with _ | hne
  · exact main (fun i => isEmptyElim i) (fun i => isEmptyElim i)
  · rcases t.eq_empty_or_nonempty with rfl | ⟨d, hd⟩
    · obtain ⟨i0⟩ := hne
      have hjpos : 0 < j := Nat.lt_of_le_of_lt (Nat.zero_le _) i0.isLt
      have hsum0 : ∑ φ ∈ Fintype.piFinset (fun _ : Fin j => (∅ : Finset α)),
          mixedCumulant μ (fun k => Z (φ k)) (univ : Finset (Fin j)) = 0 :=
        Finset.sum_eq_zero fun φ hφ => absurd (Fintype.mem_piFinset.mp hφ i0) (by simp)
      rw [hsum0]
      have h0 : (fun ω => ∑ a ∈ (∅ : Finset α), Z a ω) = fun _ : Ω => (0 : ℝ) := by
        funext ω; simp
      rw [h0, cumulant_const 0 hjpos]
      simp
    · exact main (fun _ => d) (fun _ => hd)

end Expansion

end StatLean.AsymptoticStatistics.Cumulant
