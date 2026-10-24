/-
Copyright (c) 2026 Benjamin O. Harrison, Gustavo Canavire Bacarreza, David Jacho-Chavez and
Fernando Rios-Avila.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Jacho-Chávez
-/
/-
Notice required by Section 4 of the Apache License, Version 2.0.

The definition `mixedCumulant` below is derived from a file of CausalSmith, the Causalean library
of Jiyuan Tan (https://github.com/Jiyuan-Tan/CausalSmith), Copyright (c) 2026 Jiyuan Tan, licensed
under the Apache License, Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0); see LICENSE.
Original path: Causalean/Stat/MomentProblems/Cumulant.lean (leanprover/lean4:v4.33.0).

What is taken from the original is the form of one definition, the set-partition (Möbius)
formula for a joint cumulant, which the original writes for two variables at bidegree `(p, q)` as

    jointCumulant μ X Y p q :=
      ∑ π : Finpartition (Finset.univ : Finset (Fin (p + q))),
        (-1) ^ (π.parts.card - 1) * (π.parts.card - 1)! * ∏ B ∈ π.parts, ∫ …

The definition has been modified: here it is stated, through `mobius`, for a finite family
`X : ι → Ω → ℝ` indexed by a `Finset ι`, as Janson's definition of the mixed semiinvariants
(1988, p. 306) requires. No declaration name, statement or proof of the original is reproduced,
and none of its lemmas is used. The rest of the file, namely the partition lemmas, the
moment-cumulant inversion, the vanishing under independent splitting, additivity, scaling, the
bound of Janson (4.4) for bounded variables and the examples, is original.
-/
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Partition.Finpartition
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration

/-!
# Cumulants (semiinvariants), univariate and mixed over a finite family

This file defines joint cumulants by the set-partition (Möbius) formula, which requires only
finite moments, and develops the part of their theory used by Janson (1988), "Normal
convergence by higher semiinvariants with applications to sums of dependent random variables
and random graphs", *Ann. Probab.* 16(1), 305–312. This includes the moment–cumulant
inversion, additivity over independent summands, homogeneity, translation invariance,
vanishing on independently split families, and a bound for bounded variables.

## Main results

* `Cumulant.mixedCumulant`, `Cumulant.cumulant`: the mixed cumulant `κ (X_i : i ∈ s)` and the
  univariate cumulant `κ_j (X)`.
* `Cumulant.cumulant_two_eq_variance`: `κ_2` is the variance.
* `Cumulant.partSum_mixedCumulant`: the moment–cumulant inversion.
* `Cumulant.cumulant_add_of_indepFun`, `Cumulant.cumulant_const_smul`: Janson (2.2) and (2.3).
* `Cumulant.mixedCumulant_eq_zero_of_indepFun`: Janson, Lemma 3.
* `Cumulant.abs_mixedCumulant_le`: Janson (4.4) for uniformly bounded variables.
-/

open Finset MeasureTheory ProbabilityTheory

namespace StatLean.AsymptoticStatistics

namespace Cumulant

/-! ### Section 1.  Sums over `Finpartition`

Combinatorics of set partitions, based on the bijection `sum_filter_mem_parts`.
-/

section Partitions

variable {ι : Type*} [DecidableEq ι] {M : Type*} [AddCommMonoid M]

/-- The partition of `s` obtained from a partition `σ` of `s \ D` by adding the nonempty block
`D ⊆ s`. -/
def addBlock {s D : Finset ι} (hDs : D ⊆ s) (hD : D.Nonempty) (σ : Finpartition (s \ D)) :
    Finpartition s :=
  σ.extend (by simpa [Finset.bot_eq_empty, ← Finset.nonempty_iff_ne_empty] using hD)
    Finset.sdiff_disjoint (by rw [Finset.sup_eq_union]; exact Finset.sdiff_union_of_subset hDs)

@[simp]
lemma addBlock_parts {s D : Finset ι} (hDs : D ⊆ s) (hD : D.Nonempty)
    (σ : Finpartition (s \ D)) : (addBlock hDs hD σ).parts = insert D σ.parts :=
  Finpartition.extend_parts _ _ _ _

/-- A block of a partition of `s \ D` is never `D` itself, because it is nonempty and avoids
`D`. -/
lemma notMem_parts_of_nonempty {s D : Finset ι} (hD : D.Nonempty)
    (σ : Finpartition (s \ D)) : D ∉ σ.parts := by
  intro hmem
  obtain ⟨i, hi⟩ := hD
  have := σ.subset hmem hi
  simp only [Finset.mem_sdiff] at this
  exact this.2 hi

/-- Restricting a partition of `s` to the complement of one of its blocks gives the partition
with that block removed. -/
lemma parts_restrict_sdiff {s D : Finset ι} {π : Finpartition s} (hD : D ∈ π.parts) :
    (π.restrict (Finset.sdiff_subset (s := s) (t := D))).parts = π.parts.erase D := by
  have hkey : ∀ C ∈ π.parts, C ≠ D → C ⊓ (s \ D) = C := by
    intro C hC hCD
    rw [Finset.inf_eq_inter]
    have hsub : C ⊆ s := π.subset hC
    have hdisj : Disjoint C D := π.disjoint hC hD hCD
    ext i
    simp only [Finset.mem_inter, Finset.mem_sdiff]
    exact ⟨fun h => h.1, fun hi => ⟨hi, hsub hi, fun hiD => (Finset.disjoint_left.mp hdisj hi) hiD⟩⟩
  have hkeyD : D ⊓ (s \ D) = ∅ := by
    rw [Finset.inf_eq_inter]
    ext i
    simp
  rw [Finpartition.parts_restrict]
  ext C
  simp only [Finset.mem_erase, Finset.mem_image, Finset.bot_eq_empty]
  constructor
  · rintro ⟨hCne, A, hA, rfl⟩
    by_cases hAD : A = D
    · subst hAD
      exact absurd hkeyD hCne
    · rw [hkey A hA hAD]
      exact ⟨hAD, hA⟩
  · rintro ⟨hCD, hC⟩
    exact ⟨(π.nonempty_of_mem_parts hC).ne_empty, C, hC, hkey C hC hCD⟩

/-- For a nonempty `D ⊆ s`, the partitions of `s` that have `D` as a block are the
partitions of `s \ D` with `D` adjoined. -/
lemma sum_filter_mem_parts {s D : Finset ι} (hDs : D ⊆ s) (hD : D.Nonempty)
    (G : Finpartition s → M) :
    ∑ π ∈ univ.filter (fun π : Finpartition s => D ∈ π.parts), G π
      = ∑ σ : Finpartition (s \ D), G (addBlock hDs hD σ) := by
  refine Finset.sum_bij' (fun π _ => π.restrict (Finset.sdiff_subset))
    (fun σ _ => addBlock hDs hD σ) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_ ?_
  · intro σ _
    simp
  · intro π hπ
    rw [Finset.mem_filter] at hπ
    refine Finpartition.ext ?_
    rw [addBlock_parts, parts_restrict_sdiff hπ.2, Finset.insert_erase hπ.2]
  · intro σ _
    refine Finpartition.ext ?_
    rw [parts_restrict_sdiff (by simp : D ∈ (addBlock hDs hD σ).parts), addBlock_parts,
      Finset.erase_insert (notMem_parts_of_nonempty hD σ)]
  · intro π hπ
    rw [Finset.mem_filter] at hπ
    congr 1
    refine Finpartition.ext ?_
    rw [addBlock_parts, parts_restrict_sdiff hπ.2, Finset.insert_erase hπ.2]

/-- `partSum f s = ∑_{π ∈ P(s)} ∏_{B ∈ π} f B`. With `m` the joint moments and `κ` the
cumulants, the moment–cumulant relation is `partSum κ = m`. -/
noncomputable def partSum (f : Finset ι → ℝ) (s : Finset ι) : ℝ :=
  ∑ π : Finpartition s, ∏ B ∈ π.parts, f B

/-- `partSum` restricted to the partitions of `s` with exactly `k` blocks. -/
noncomputable def partSumCard (f : Finset ι → ℝ) (s : Finset ι) (k : ℕ) : ℝ :=
  ∑ π ∈ univ.filter (fun π : Finpartition s => #π.parts = k), ∏ B ∈ π.parts, f B

@[simp]
lemma partSum_empty (f : Finset ι → ℝ) : partSum f ∅ = 1 := by
  have huniq : ∀ π : Finpartition (∅ : Finset ι), π.parts = ∅ := fun π =>
    Finpartition.parts_eq_empty_iff.mpr Finset.bot_eq_empty.symm
  have hsub : Subsingleton (Finpartition (∅ : Finset ι)) :=
    ⟨fun π ρ => Finpartition.ext ((huniq π).trans (huniq ρ).symm)⟩
  obtain ⟨π₀⟩ : Nonempty (Finpartition (∅ : Finset ι)) := inferInstance
  have hcard : (univ : Finset (Finpartition (∅ : Finset ι))).card = 1 := by
    rw [Finset.card_univ]
    exact Fintype.card_eq_one_iff.mpr ⟨π₀, fun y => Subsingleton.elim y π₀⟩
  simp only [partSum]
  rw [Finset.sum_congr rfl (fun π _ => by rw [huniq π, Finset.prod_empty]), Finset.sum_const,
    hcard, one_smul]

/-- The partitions of `s` having exactly one block are the single partition `{s}`. -/
lemma parts_eq_singleton_of_card_eq_one {s : Finset ι} {π : Finpartition s}
    (h : #π.parts = 1) : π.parts = {s} := by
  obtain ⟨B, hB⟩ := Finset.card_eq_one.mp h
  have hsup : π.parts.sup id = s := π.sup_parts
  rw [hB, Finset.sup_singleton, id_eq] at hsup
  rw [hB, hsup]

lemma partSumCard_one {f : Finset ι → ℝ} {s : Finset ι} (hs : s.Nonempty) :
    partSumCard f s 1 = f s := by
  classical
  have hne : s ≠ ⊥ := by rw [Finset.bot_eq_empty]; exact hs.ne_empty
  have hmem : ∀ π : Finpartition s, #π.parts = 1 ↔ π = Finpartition.indiscrete hne := by
    intro π
    constructor
    · intro h
      exact Finpartition.ext (by
        rw [parts_eq_singleton_of_card_eq_one h, Finpartition.indiscrete_parts])
    · rintro rfl
      simp [Finpartition.indiscrete_parts]
  have hfil : univ.filter (fun π : Finpartition s => #π.parts = 1)
      = {Finpartition.indiscrete hne} := by
    ext π
    simp [hmem π]
  rw [partSumCard, hfil, Finset.sum_singleton, Finpartition.indiscrete_parts,
    Finset.prod_singleton]

lemma partSumCard_eq_zero_of_card_lt {f : Finset ι → ℝ} {s : Finset ι} {k : ℕ} (h : #s < k) :
    partSumCard f s k = 0 := by
  refine Finset.sum_eq_zero fun π hπ => ?_
  rw [Finset.mem_filter] at hπ
  exact absurd (hπ.2 ▸ π.card_parts_le_card) (not_le.mpr h)

lemma partSumCard_zero_of_nonempty {f : Finset ι → ℝ} {s : Finset ι} (hs : s.Nonempty) :
    partSumCard f s 0 = 0 := by
  refine Finset.sum_eq_zero fun π hπ => ?_
  rw [Finset.mem_filter] at hπ
  have hpe : π.parts = ∅ := Finset.card_eq_zero.mp hπ.2
  rw [Finpartition.parts_eq_empty_iff, Finset.bot_eq_empty] at hpe
  exact absurd hpe hs.ne_empty

/-- Grading a partition sum by the number of blocks. -/
lemma sum_weighted_eq_sum_partSumCard (f : Finset ι → ℝ) (s : Finset ι) (F : ℕ → ℝ) :
    ∑ π : Finpartition s, F (#π.parts) * ∏ B ∈ π.parts, f B
      = ∑ k ∈ Finset.range (#s + 1), F k * partSumCard f s k := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun π : Finpartition s => #π.parts) (t := Finset.range (#s + 1))
    (fun π _ => Finset.mem_range.mpr (Nat.lt_succ_of_le π.card_parts_le_card)) _]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [partSumCard, Finset.mul_sum]
  exact Finset.sum_congr rfl fun π hπ => by rw [(Finset.mem_filter.mp hπ).2]

/-- **Block recursion.** Splitting a partition of `s` at the block containing `i₀`. -/
lemma partSum_recursion (f : Finset ι → ℝ) {s : Finset ι} {i₀ : ι} (hi : i₀ ∈ s) :
    partSum f s = ∑ D ∈ s.powerset.filter (fun D => i₀ ∈ D), f D * partSum f (s \ D) := by
  classical
  rw [partSum, ← Finset.sum_fiberwise_of_maps_to
    (g := fun π : Finpartition s => π.part i₀) (t := s.powerset.filter (fun D => i₀ ∈ D))
    (fun π _ => Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (π.part_subset i₀),
      (Finpartition.mem_part_self π).mpr hi⟩) _]
  refine Finset.sum_congr rfl fun D hD => ?_
  rw [Finset.mem_filter, Finset.mem_powerset] at hD
  obtain ⟨hDs, hi₀D⟩ := hD
  have hDne : D.Nonempty := ⟨i₀, hi₀D⟩
  have hfilter : univ.filter (fun π : Finpartition s => π.part i₀ = D)
      = univ.filter (fun π : Finpartition s => D ∈ π.parts) := by
    ext π
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h ▸ (Finpartition.part_mem π).mpr hi,
      fun h => Finpartition.part_eq_of_mem π h hi₀D⟩
  rw [hfilter, sum_filter_mem_parts hDs hDne, partSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [addBlock_parts, Finset.prod_insert (notMem_parts_of_nonempty hDne σ)]

/-- `partSum` determines its argument on nonempty subsets of `s`. -/
theorem eq_of_partSum_eq_of_subset {f g : Finset ι → ℝ} {s : Finset ι}
    (h : ∀ u : Finset ι, u ⊆ s → partSum f u = partSum g u) :
    ∀ t : Finset ι, t ⊆ s → t.Nonempty → f t = g t := by
  classical
  intro t
  induction t using Finset.strongInduction with
  | _ t ih =>
    intro hts ht
    obtain ⟨i₀, hi₀⟩ := ht
    have hsplit : ∀ u : Finset ι → ℝ,
        partSum u t = u t * partSum u ∅ +
          ∑ D ∈ (t.powerset.filter (fun D => i₀ ∈ D)).erase t, u D * partSum u (t \ D) := by
      intro u
      rw [partSum_recursion u hi₀, ← Finset.add_sum_erase _ _
        (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (subset_refl t), hi₀⟩), Finset.sdiff_self]
    have hrest : ∀ D ∈ (t.powerset.filter (fun D => i₀ ∈ D)).erase t, f D = g D := by
      intro D hD
      rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_powerset] at hD
      exact ih D (Finset.ssubset_iff_subset_ne.mpr ⟨hD.2.1, hD.1⟩)
        (hD.2.1.trans hts) ⟨i₀, hD.2.2⟩
    have hkey := h t hts
    rw [hsplit f, hsplit g, partSum_empty, partSum_empty, mul_one, mul_one,
      Finset.sum_congr rfl (fun D hD => by
        rw [hrest D hD, h (t \ D) (Finset.sdiff_subset.trans hts)])] at hkey
    exact add_right_cancel hkey

/-- `partSum` determines its argument on nonempty sets. -/
theorem eq_of_partSum_eq {f g : Finset ι → ℝ} (h : ∀ t : Finset ι, partSum f t = partSum g t)
    {t : Finset ι} (ht : t.Nonempty) : f t = g t :=
  eq_of_partSum_eq_of_subset (s := t) (fun u _ => h u) t (subset_refl t) ht

/-- Exactly one block of a partition of `s` contains a given `i₀ ∈ s`. -/
lemma card_filter_notMem_parts {s : Finset ι} {i₀ : ι} (hi : i₀ ∈ s) (π : Finpartition s) :
    #(π.parts.filter (fun E => i₀ ∉ E)) = #π.parts - 1 := by
  classical
  have hpos : π.parts.filter (fun E => i₀ ∈ E) = {π.part i₀} := by
    ext B
    simp only [Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun h => (Finpartition.part_eq_of_mem π h.1 h.2).symm,
      fun h => h ▸ ⟨(Finpartition.part_mem π).mpr hi, (Finpartition.mem_part_self π).mpr hi⟩⟩
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := π.parts) (p := fun E => i₀ ∈ E)
  rw [hpos, Finset.card_singleton] at hsplit
  omega

/-- One term of the marked-block identity. The subsets `D ∋ i₀` of `s` other than `s` itself are
in bijection with the nonempty blocks `E = s \ D` avoiding `i₀`, and a `k`-block partition of
`D` with `E` adjoined is a `(k+1)`-block partition of `s` having `E` as a block. -/
lemma mul_partSumCard_eq_sum {f : Finset ι → ℝ} {s E : Finset ι} (hEs : E ⊆ s)
    (hEne : E.Nonempty) (k : ℕ) :
    f E * partSumCard f (s \ E) k
      = ∑ π ∈ univ.filter (fun π : Finpartition s => #π.parts = k + 1),
          if E ∈ π.parts then ∏ B ∈ π.parts, f B else 0 := by
  classical
  have hbij := sum_filter_mem_parts (D := E) hEs hEne
    (G := fun π => if #π.parts = k + 1 then ∏ B ∈ π.parts, f B else 0)
  have hR : ∑ π ∈ univ.filter (fun π : Finpartition s => #π.parts = k + 1),
      (if E ∈ π.parts then ∏ B ∈ π.parts, f B else 0)
      = ∑ π ∈ univ.filter (fun π : Finpartition s => E ∈ π.parts),
          (if #π.parts = k + 1 then ∏ B ∈ π.parts, f B else 0) := by
    rw [Finset.sum_filter, Finset.sum_filter]
    exact Finset.sum_congr rfl (fun π _ => by simp only [← ite_and, and_comm])
  rw [hR, hbij, partSumCard, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [addBlock, Finpartition.card_extend]
  by_cases hk : #σ.parts = k
  · subst hk
    simp [Finset.prod_insert (notMem_parts_of_nonempty hEne σ)]
  · simp [hk]

/-- The subsets `D ∋ i₀` of `s` other than `s` itself whose complement is a block of `π` are in
bijection, by `D ↦ s \ D`, with the blocks of `π` avoiding `i₀`. -/
lemma card_filter_sdiff_mem_parts {s : Finset ι} {i₀ : ι} (hi : i₀ ∈ s) (π : Finpartition s) :
    #(((s.powerset.filter (fun D => i₀ ∈ D)).erase s).filter (fun D => (s \ D) ∈ π.parts))
      = #π.parts - 1 := by
  classical
  rw [← card_filter_notMem_parts hi π]
  refine Finset.card_nbij' (fun D => s \ D) (fun E => s \ E) ?_ ?_ ?_ ?_
  · intro D hD
    simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_filter,
      Finset.mem_powerset] at hD ⊢
    exact ⟨hD.2, fun hcon => (Finset.mem_sdiff.mp hcon).2 hD.1.2.2⟩
  · intro E hE
    simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_filter,
      Finset.mem_powerset] at hE ⊢
    obtain ⟨hEmem, hEi⟩ := hE
    have hEsub : E ⊆ s := π.subset hEmem
    have hEne : E.Nonempty := π.nonempty_of_mem_parts hEmem
    refine ⟨⟨?_, Finset.sdiff_subset, Finset.mem_sdiff.mpr ⟨hi, hEi⟩⟩, ?_⟩
    · intro hcon
      obtain ⟨j, hj⟩ := hEne
      have hjmem := hcon ▸ (hEsub hj)
      exact (Finset.mem_sdiff.mp hjmem).2 hj
    · rwa [Finset.sdiff_sdiff_eq_self hEsub]
  · intro D hD
    simp only [Finset.mem_coe, Finset.mem_erase, Finset.mem_filter,
      Finset.mem_powerset] at hD
    exact Finset.sdiff_sdiff_eq_self hD.1.2.1
  · intro E hE
    simp only [Finset.mem_coe, Finset.mem_filter] at hE
    exact Finset.sdiff_sdiff_eq_self (π.subset hE.1)

/-- **Marked-block identity.** Summing `partSumCard f D k * f (s \ D)` over the subsets `D`
containing `i₀` counts each `k`-block partition of `s` once and each `(k+1)`-block partition
once for every block that avoids `i₀`. -/
lemma sum_marked_block (f : Finset ι → ℝ) (hf : f ∅ = 1) {s : Finset ι} {i₀ : ι} (hi : i₀ ∈ s)
    (k : ℕ) :
    ∑ D ∈ s.powerset.filter (fun D => i₀ ∈ D), partSumCard f D k * f (s \ D)
      = partSumCard f s k + k * partSumCard f s (k + 1) := by
  classical
  rw [← Finset.add_sum_erase _ _
    (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (subset_refl s), hi⟩), Finset.sdiff_self, hf,
    mul_one]
  congr 1
  have hstep : ∀ D ∈ (s.powerset.filter (fun D => i₀ ∈ D)).erase s,
      partSumCard f D k * f (s \ D)
        = ∑ π ∈ univ.filter (fun π : Finpartition s => #π.parts = k + 1),
            if (s \ D) ∈ π.parts then ∏ B ∈ π.parts, f B else 0 := by
    intro D hD
    rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_powerset] at hD
    obtain ⟨hDne, hDs, _⟩ := hD
    have hEne : (s \ D).Nonempty := by
      rw [Finset.sdiff_nonempty]
      exact fun hcon => hDne (Finset.Subset.antisymm hDs hcon)
    have hkey := mul_partSumCard_eq_sum (f := f) (s := s) (E := s \ D) Finset.sdiff_subset hEne k
    rw [Finset.sdiff_sdiff_eq_self hDs] at hkey
    rw [← hkey, mul_comm]
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm, partSumCard, Finset.mul_sum]
  refine Finset.sum_congr rfl fun π hπ => ?_
  rw [Finset.mem_filter] at hπ
  rw [← Finset.sum_filter, Finset.sum_const, card_filter_sdiff_mem_parts hi π, hπ.2,
    Nat.add_sub_cancel, nsmul_eq_mul]

/-! ### Section 2.  The Möbius transform and its inversion

`mobius f` is the set-partition formula with the weights `(-1)^(k-1) (k-1)!`, and `partSum`
inverts it. For `f` the joint moments, this is the moment–cumulant relation.
-/

/-- The weight `(-1)^(k-1) (k-1)!` that the set-partition formula attaches to a partition with
`k` blocks. -/
noncomputable def mobiusWeight (k : ℕ) : ℝ := (-1) ^ (k - 1) * (Nat.factorial (k - 1) : ℝ)

@[simp]
lemma mobiusWeight_zero : mobiusWeight 0 = 1 := by norm_num [mobiusWeight]

@[simp]
lemma mobiusWeight_one : mobiusWeight 1 = 1 := by norm_num [mobiusWeight]

/-- `k * w k = - w (k+1)` for `k ≥ 1`. -/
lemma nat_mul_mobiusWeight {k : ℕ} (hk : 1 ≤ k) :
    (k : ℝ) * mobiusWeight k = - mobiusWeight (k + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [mobiusWeight, Nat.add_sub_cancel, Nat.factorial_succ, pow_succ]
  push_cast
  ring

/-- The telescoping identity behind the inversion, for an arbitrary sequence. -/
lemma sum_mobiusWeight_telescope (a : ℕ → ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), mobiusWeight k * a k)
        + ∑ k ∈ Finset.range (n + 1), ((k : ℝ) * mobiusWeight k) * a (k + 1)
      = mobiusWeight 0 * a 0 + mobiusWeight 1 * a 1 - mobiusWeight (n + 1) * a (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : (((n + 1 : ℕ) : ℝ)) * mobiusWeight (n + 1) = - mobiusWeight (n + 1 + 1) :=
      nat_mul_mobiusWeight (by omega)
    rw [Finset.sum_range_succ (n := n + 1), Finset.sum_range_succ (n := n + 1), hstep]
    linarith [ih]

/-- The Möbius transform `mobius f s = ∑_{π ∈ P(s)} (-1)^(|π|-1) (|π|-1)! ∏_{B ∈ π} f B`. -/
noncomputable def mobius (f : Finset ι → ℝ) (s : Finset ι) : ℝ :=
  ∑ π : Finpartition s, mobiusWeight #π.parts * ∏ B ∈ π.parts, f B

/-- Grading `mobius` by block count. -/
lemma mobius_eq_sum_range (f : Finset ι → ℝ) (s : Finset ι) {n : ℕ} (hn : #s ≤ n) :
    mobius f s = ∑ k ∈ Finset.range (n + 1), mobiusWeight k * partSumCard f s k := by
  classical
  have hsub : Finset.range (#s + 1) ⊆ Finset.range (n + 1) :=
    Finset.range_subset_range.mpr (Nat.succ_le_succ hn)
  have hzero : ∀ k ∈ Finset.range (n + 1), k ∉ Finset.range (#s + 1) →
      mobiusWeight k * partSumCard f s k = 0 := by
    intro k _ hk
    rw [Finset.mem_range, not_lt] at hk
    rw [partSumCard_eq_zero_of_card_lt (f := f) hk, mul_zero]
  rw [mobius, sum_weighted_eq_sum_partSumCard f s mobiusWeight]
  exact Finset.sum_subset hsub hzero

/-- Expanding `mobius f D` by block count, applying the marked-block identity to each grade and
telescoping with `k * w k = - w (k+1)`. -/
lemma sum_mobius_mul (f : Finset ι → ℝ) (hf : f ∅ = 1) {s : Finset ι} {i₀ : ι} (hi : i₀ ∈ s) :
    ∑ D ∈ s.powerset.filter (fun D => i₀ ∈ D), mobius f D * f (s \ D) = f s := by
  classical
  have hs : s.Nonempty := ⟨i₀, hi⟩
  have hexp : ∀ D ∈ s.powerset.filter (fun D => i₀ ∈ D),
      mobius f D * f (s \ D)
        = ∑ k ∈ Finset.range (#s + 1), mobiusWeight k * (partSumCard f D k * f (s \ D)) := by
    intro D hD
    rw [Finset.mem_filter, Finset.mem_powerset] at hD
    rw [mobius_eq_sum_range f D (Finset.card_le_card hD.1), Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
  have hmark : ∀ k ∈ Finset.range (#s + 1),
      (∑ D ∈ s.powerset.filter (fun D => i₀ ∈ D),
          mobiusWeight k * (partSumCard f D k * f (s \ D)))
        = mobiusWeight k * partSumCard f s k
            + ((k : ℝ) * mobiusWeight k) * partSumCard f s (k + 1) := by
    intro k _
    rw [← Finset.mul_sum, sum_marked_block f hf hi k]
    ring
  rw [Finset.sum_congr rfl hmark, Finset.sum_add_distrib,
    sum_mobiusWeight_telescope (fun k => partSumCard f s k) #s,
    partSumCard_zero_of_nonempty hs, partSumCard_one hs,
    partSumCard_eq_zero_of_card_lt (k := #s + 1) (by omega), mobiusWeight_one]
  ring

/-- **Moment–cumulant inversion**, measure-free form: `partSum` inverts `mobius`. -/
theorem partSum_mobius (f : Finset ι → ℝ) (hf : f ∅ = 1) (s : Finset ι) :
    partSum (mobius f) s = f s := by
  classical
  induction s using Finset.strongInduction with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · rw [partSum_empty, hf]
    obtain ⟨i₀, hi₀⟩ := hs
    rw [partSum_recursion _ hi₀]
    have hIH : ∀ D ∈ s.powerset.filter (fun D => i₀ ∈ D),
        mobius f D * partSum (mobius f) (s \ D) = mobius f D * f (s \ D) := by
      intro D hD
      rw [Finset.mem_filter, Finset.mem_powerset] at hD
      have hsub : s \ D ⊂ s :=
        (Finset.ssubset_iff_of_subset Finset.sdiff_subset).mpr ⟨i₀, hi₀, by simp [hD.2]⟩
      rw [ih _ hsub]
    rw [Finset.sum_congr rfl hIH]
    exact sum_mobius_mul f hf hi₀

/-! #### Subset convolution

`partSum` turns pointwise addition into subset convolution; this underlies the additivity of
cumulants over independent summands (Janson (2.2)).
-/

/-- The powerset of a subset, as a filter of the ambient powerset. -/
lemma powerset_eq_filter (s t : Finset ι) (hts : t ⊆ s) :
    t.powerset = s.powerset.filter (fun D => D ⊆ t) := by
  ext D
  simp only [Finset.mem_powerset, Finset.mem_filter]
  exact ⟨fun h => ⟨h.trans hts, h⟩, fun h => h.2⟩

/-- Reindexing the supersets of `D` inside `s` by their difference with `D`. -/
lemma sum_filter_superset {s D : Finset ι} (hDs : D ⊆ s) (F : Finset ι → ℝ) :
    ∑ A ∈ s.powerset.filter (fun A => D ⊆ A), F (A \ D) = ∑ E ∈ (s \ D).powerset, F E := by
  classical
  have hsd : ∀ E ∈ (s \ D).powerset, (D ∪ E) \ D = E := fun E hE => by
    rw [Finset.union_sdiff_left, (Finset.disjoint_of_subset_left (Finset.mem_powerset.mp hE)
      Finset.sdiff_disjoint).sdiff_eq_left]
  rw [← Finset.Icc_eq_filter_powerset, Finset.Icc_eq_image_powerset hDs, Finset.sum_image (by
    intro E hE E' hE' h
    rw [← hsd E hE, ← hsd E' hE']
    exact congrArg (· \ D) h)]
  exact Finset.sum_congr rfl fun E hE => by rw [hsd E hE]

/-- Summing over `D ⊆ A ⊆ s` is the same as summing over disjoint pairs `(D, E)` with
`D ∪ E ⊆ s`. -/
lemma sum_powerset_powerset (s : Finset ι) (H : Finset ι → Finset ι → ℝ) :
    ∑ A ∈ s.powerset, ∑ D ∈ A.powerset, H D (A \ D)
      = ∑ D ∈ s.powerset, ∑ E ∈ (s \ D).powerset, H D E := by
  classical
  have hL : ∀ A ∈ s.powerset, ∑ D ∈ A.powerset, H D (A \ D)
      = ∑ D ∈ s.powerset, if D ⊆ A then H D (A \ D) else 0 := by
    intro A hA
    rw [powerset_eq_filter s A (Finset.mem_powerset.mp hA), Finset.sum_filter]
  rw [Finset.sum_congr rfl hL, Finset.sum_comm]
  refine Finset.sum_congr rfl fun D hD => ?_
  rw [← Finset.sum_filter, sum_filter_superset (Finset.mem_powerset.mp hD)]

/-- Summing over disjoint pairs is symmetric in the two components. -/
lemma sum_powerset_comm (s : Finset ι) (K : Finset ι → Finset ι → ℝ) :
    ∑ A ∈ s.powerset, ∑ D ∈ (s \ A).powerset, K A D
      = ∑ D ∈ s.powerset, ∑ A ∈ (s \ D).powerset, K A D := by
  classical
  have hrw : ∀ (B : Finset ι), B ⊆ s → ∀ (L : Finset ι → ℝ),
      ∑ C ∈ (s \ B).powerset, L C = ∑ C ∈ s.powerset, if Disjoint C B then L C else 0 := by
    intro B _ L
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext C
    simp only [Finset.mem_powerset, Finset.mem_filter, Finset.subset_sdiff]
  rw [Finset.sum_congr rfl (fun A hA => hrw A (Finset.mem_powerset.mp hA) (fun D => K A D)),
    Finset.sum_comm,
    Finset.sum_congr rfl (fun D hD => hrw D (Finset.mem_powerset.mp hD) (fun A => K A D))]
  refine Finset.sum_congr rfl fun D _ => Finset.sum_congr rfl fun A _ => ?_
  by_cases h : Disjoint A D
  · simp only [ite_eq_left h, ite_eq_left h.symm]
  · simp only [ite_eq_right h, ite_eq_right (fun hc : Disjoint D A => h hc.symm)]

/-- The block recursion for a subset convolution, in which the block of `i₀` lies either in
the first factor or in the second. -/
lemma conv_recursion (f g : Finset ι → ℝ) {s : Finset ι} {i₀ : ι} (hi : i₀ ∈ s) :
    ∑ A ∈ s.powerset, partSum f A * partSum g (s \ A)
      = ∑ D ∈ s.powerset.filter (fun D => i₀ ∈ D),
          (f D + g D) * ∑ A ∈ (s \ D).powerset, partSum f A * partSum g ((s \ D) \ A) := by
  classical
  -- the `i₀ ∈ A` half, handled by `sum_powerset_powerset`
  have hfirst : (∑ A ∈ s.powerset.filter (fun A => i₀ ∈ A),
        partSum f A * partSum g (s \ A))
      = ∑ D ∈ s.powerset.filter (fun D => i₀ ∈ D),
          f D * ∑ A ∈ (s \ D).powerset, partSum f A * partSum g ((s \ D) \ A) := by
    have hexp : ∀ A ∈ s.powerset,
        (∑ D ∈ A.powerset, if i₀ ∈ D then f D * partSum f (A \ D) * partSum g (s \ (D ∪ (A \ D)))
            else 0)
          = if i₀ ∈ A then partSum f A * partSum g (s \ A) else 0 := by
      intro A hA
      rw [Finset.mem_powerset] at hA
      by_cases hiA : i₀ ∈ A
      · simp only [ite_eq_left hiA]
        rw [← Finset.sum_filter, partSum_recursion f hiA, Finset.sum_mul]
        refine Finset.sum_congr ?_ fun D hD => ?_
        · rw [powerset_eq_filter s A hA]
        · rw [Finset.mem_filter, Finset.mem_powerset] at hD
          rw [Finset.union_sdiff_of_subset hD.1]
      · simp only [ite_eq_right hiA]
        refine Finset.sum_eq_zero fun D hD => ?_
        rw [Finset.mem_powerset] at hD
        exact ite_eq_right fun hc => hiA (hD hc)
    rw [Finset.sum_filter, ← Finset.sum_congr rfl hexp,
      sum_powerset_powerset s (fun D E => if i₀ ∈ D then
        f D * partSum f E * partSum g (s \ (D ∪ E)) else 0),
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun D hD => ?_
    rw [Finset.mem_powerset] at hD
    by_cases hiD : i₀ ∈ D
    · simp only [ite_eq_left hiD]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun E _ => ?_
      rw [← Finset.sup_eq_union, ← sdiff_sdiff_left]
      ring
    · simp only [ite_eq_right hiD]
      exact Finset.sum_const_zero
  -- the `i₀ ∉ A` half, handled by `sum_powerset_comm`
  have hsecond : (∑ A ∈ s.powerset.filter (fun A => ¬ i₀ ∈ A),
        partSum f A * partSum g (s \ A))
      = ∑ D ∈ s.powerset.filter (fun D => i₀ ∈ D),
          g D * ∑ A ∈ (s \ D).powerset, partSum f A * partSum g ((s \ D) \ A) := by
    have hexp : ∀ A ∈ s.powerset,
        (∑ D ∈ (s \ A).powerset, if i₀ ∈ D then partSum f A * (g D * partSum g ((s \ A) \ D))
            else 0)
          = if i₀ ∉ A then partSum f A * partSum g (s \ A) else 0 := by
      intro A hA
      rw [Finset.mem_powerset] at hA
      by_cases hiA : i₀ ∈ A
      · simp only [ite_eq_right (not_not_intro hiA)]
        refine Finset.sum_eq_zero fun D hD => ?_
        rw [Finset.mem_powerset] at hD
        exact ite_eq_right fun hc => (Finset.mem_sdiff.mp (hD hc)).2 hiA
      · simp only [ite_eq_left hiA]
        rw [← Finset.sum_filter]
        have hiSA : i₀ ∈ s \ A := Finset.mem_sdiff.mpr ⟨hi, hiA⟩
        rw [partSum_recursion g hiSA, Finset.mul_sum]
    rw [Finset.sum_filter, ← Finset.sum_congr rfl hexp,
      sum_powerset_comm s (fun A D => if i₀ ∈ D then
        partSum f A * (g D * partSum g ((s \ A) \ D)) else 0),
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun D hD => ?_
    rw [Finset.mem_powerset] at hD
    by_cases hiD : i₀ ∈ D
    · simp only [ite_eq_left hiD]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun A _ => ?_
      rw [sdiff_sdiff_left, sdiff_sdiff_left, sup_comm]
      ring
    · simp only [ite_eq_right hiD]
      exact Finset.sum_const_zero
  rw [← Finset.sum_filter_add_sum_filter_not s.powerset (fun A => i₀ ∈ A)
      (fun A => partSum f A * partSum g (s \ A)), hfirst, hsecond, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun D _ => by ring

/-- `partSum` turns pointwise addition into subset convolution. -/
theorem partSum_add (f g : Finset ι → ℝ) (s : Finset ι) :
    partSum (fun B => f B + g B) s = ∑ A ∈ s.powerset, partSum f A * partSum g (s \ A) := by
  classical
  induction s using Finset.strongInduction with
  | _ s ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simp
    obtain ⟨i₀, hi₀⟩ := hs
    rw [partSum_recursion _ hi₀, conv_recursion f g hi₀]
    refine Finset.sum_congr rfl fun D hD => ?_
    rw [Finset.mem_filter, Finset.mem_powerset] at hD
    have hDne : D.Nonempty := ⟨i₀, hD.2⟩
    have hsub : s \ D ⊂ s :=
      (Finset.ssubset_iff_of_subset Finset.sdiff_subset).mpr ⟨i₀, hi₀, by simp [hD.2]⟩
    rw [ih _ hsub]

/-- The recursive form of the Möbius transform, obtained by separating the term `D = s` in
`sum_mobius_mul`. -/
lemma mobius_eq_sub (f : Finset ι → ℝ) (hf : f ∅ = 1) {s : Finset ι} {i₀ : ι} (hi : i₀ ∈ s) :
    mobius f s
      = f s - ∑ D ∈ (s.powerset.filter (fun D => i₀ ∈ D)).erase s, mobius f D * f (s \ D) := by
  classical
  have hkey := sum_mobius_mul f hf hi
  rw [← Finset.add_sum_erase _ _
    (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (subset_refl s), hi⟩), Finset.sdiff_self, hf,
    mul_one] at hkey
  linarith [hkey]

@[simp]
lemma mobius_empty (f : Finset ι → ℝ) : mobius f ∅ = 1 := by
  have huniq : ∀ π : Finpartition (∅ : Finset ι), π.parts = ∅ := fun π =>
    Finpartition.parts_eq_empty_iff.mpr Finset.bot_eq_empty.symm
  have hsub : Subsingleton (Finpartition (∅ : Finset ι)) :=
    ⟨fun π ρ => Finpartition.ext ((huniq π).trans (huniq ρ).symm)⟩
  obtain ⟨π₀⟩ : Nonempty (Finpartition (∅ : Finset ι)) := inferInstance
  have hcard : (univ : Finset (Finpartition (∅ : Finset ι))).card = 1 := by
    rw [Finset.card_univ]
    exact Fintype.card_eq_one_iff.mpr ⟨π₀, fun y => Subsingleton.elim y π₀⟩
  simp only [mobius]
  rw [Finset.sum_congr rfl (fun π _ => by rw [huniq π, Finset.prod_empty, Finset.card_empty,
      mobiusWeight_zero, mul_one]), Finset.sum_const, hcard, one_smul]

@[simp]
lemma mobius_singleton (f : Finset ι → ℝ) (i : ι) : mobius f {i} = f {i} := by
  classical
  rw [mobius_eq_sum_range f {i} (le_of_eq (Finset.card_singleton i))]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    partSumCard_zero_of_nonempty ⟨i, Finset.mem_singleton_self i⟩,
    partSumCard_one ⟨i, Finset.mem_singleton_self i⟩, mobiusWeight_one]
  ring

/-- If `h` is the subset convolution of `f` and `g`, then `mobius h = mobius f + mobius g`. -/
theorem mobius_add_of_conv {f g h : Finset ι → ℝ} (hf : f ∅ = 1) (hg : g ∅ = 1)
    (hconv : ∀ t : Finset ι, h t = ∑ A ∈ t.powerset, f A * g (t \ A))
    {s : Finset ι} (hs : s.Nonempty) :
    mobius h s = mobius f s + mobius g s := by
  classical
  have hh : h ∅ = 1 := by rw [hconv ∅]; simp [hf, hg]
  refine eq_of_partSum_eq (f := mobius h) (g := fun B => mobius f B + mobius g B) ?_ hs
  intro t
  rw [partSum_mobius h hh t, partSum_add, hconv t]
  exact Finset.sum_congr rfl fun A _ => by
    rw [partSum_mobius f hf A, partSum_mobius g hg (t \ A)]

/-- If the joint moments factor across a splitting of `s` into two disjoint parts, then the
Möbius transform vanishes at `s` whenever `s` meets both parts. -/
theorem mobius_eq_zero_of_split {f : Finset ι → ℝ} (hf : f ∅ = 1) {s a b : Finset ι}
    (hab : Disjoint a b) (hcover : s ⊆ a ∪ b)
    (hsplit : ∀ t : Finset ι, t ⊆ s → f t = f (t ∩ a) * f (t ∩ b))
    (hsa : ¬ s ⊆ a) (hsb : ¬ s ⊆ b) :
    mobius f s = 0 := by
  classical
  set h : Finset ι → ℝ := fun B => if B ⊆ a ∨ B ⊆ b then mobius f B else 0 with hhdef
  -- the induction step, used with `(a, b)` and with `(b, a)`
  have step : ∀ (c d : Finset ι), Disjoint c d →
      (∀ t : Finset ι, t ⊆ s → f t = f (t ∩ c) * f (t ∩ d)) →
      (∀ B : Finset ι, h B = if B ⊆ c then mobius f B else
        if B ⊆ d then mobius f B else 0) →
      ∀ t : Finset ι, t ⊆ s → ∀ i₀ ∈ t, i₀ ∈ c →
        (∀ u : Finset ι, u ⊂ t → u ⊆ s → partSum h u = f u) → partSum h t = f t := by
    intro c d hcd hsp hh t hts i₀ hi₀t hi₀c ih
    have hi₀d : i₀ ∉ d := fun hcon => (Finset.disjoint_left.mp hcd hi₀c) hcon
    rw [partSum_recursion h hi₀t]
    -- the terms with `D ⊄ c` vanish
    have hterm : ∀ D ∈ t.powerset.filter (fun D => i₀ ∈ D),
        h D * partSum h (t \ D)
          = if D ⊆ c then mobius f D * f ((t ∩ c) \ D) * f (t ∩ d) else 0 := by
      intro D hD
      rw [Finset.mem_filter, Finset.mem_powerset] at hD
      by_cases hDc : D ⊆ c
      · have hDne : D.Nonempty := ⟨i₀, hD.2⟩
        have hsub : t \ D ⊂ t :=
          (Finset.ssubset_iff_of_subset Finset.sdiff_subset).mpr ⟨i₀, hi₀t, by simp [hD.2]⟩
        rw [hh D, ite_eq_left hDc, ite_eq_left hDc, ih _ hsub (Finset.sdiff_subset.trans hts),
          hsp (t \ D) (Finset.sdiff_subset.trans hts)]
        have h1 : (t \ D) ∩ c = (t ∩ c) \ D := by
          ext i; simp only [Finset.mem_inter, Finset.mem_sdiff]; tauto
        have h2 : (t \ D) ∩ d = t ∩ d := by
          ext i
          simp only [Finset.mem_inter, Finset.mem_sdiff]
          exact ⟨fun hi => ⟨hi.1.1, hi.2⟩, fun hi =>
            ⟨⟨hi.1, fun hiD => (Finset.disjoint_left.mp hcd (hDc hiD)) hi.2⟩, hi.2⟩⟩
        rw [h1, h2, mul_assoc]
      · have hDd : ¬ D ⊆ d := fun hcon => hi₀d (hcon hD.2)
        rw [hh D, ite_eq_right hDc, ite_eq_right hDd, ite_eq_right hDc, zero_mul]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter]
    -- the remaining index set consists of the subsets of `t ∩ c` containing `i₀`
    have hidx : (t.powerset.filter (fun D => i₀ ∈ D)).filter (fun D => D ⊆ c)
        = (t ∩ c).powerset.filter (fun D => i₀ ∈ D) := by
      ext D
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_inter_iff]
      tauto
    rw [hidx, ← Finset.sum_mul, sum_mobius_mul f hf (Finset.mem_inter.mpr ⟨hi₀t, hi₀c⟩),
      ← hsp t hts]
  have key : ∀ t : Finset ι, t ⊆ s → partSum h t = f t := by
    intro t
    induction t using Finset.strongInduction with
    | _ t ih =>
      intro hts
      rcases t.eq_empty_or_nonempty with rfl | hne
      · rw [partSum_empty, hf]
      obtain ⟨i₀, hi₀⟩ := hne
      rcases Finset.mem_union.mp (hcover (hts hi₀)) with hi₁ | hi₂
      · exact step a b hab hsplit (fun B => by
          simp only [hhdef]
          by_cases hBa : B ⊆ a <;> by_cases hBb : B ⊆ b <;> simp [hBa, hBb]) t hts i₀ hi₀ hi₁
          (fun u hu hus => ih u hu hus)
      · exact step b a hab.symm (fun u hus => by rw [hsplit u hus, mul_comm]) (fun B => by
          simp only [hhdef]
          by_cases hBa : B ⊆ a <;> by_cases hBb : B ⊆ b <;> simp [hBa, hBb]) t hts i₀ hi₀ hi₂
          (fun u hu hus => ih u hu hus)
  have hfinal : h s = mobius f s :=
    eq_of_partSum_eq_of_subset (f := h) (g := mobius f)
      (fun u hus => by rw [key u hus, partSum_mobius f hf u]) s (subset_refl s)
      (Finset.nonempty_iff_ne_empty.mpr fun hcon => hsa (hcon ▸ Finset.empty_subset a))
  rw [← hfinal]
  simp only [hhdef, hsa, hsb, or_self, ite_false]

/-- Every element of `s` lies in exactly one block of a partition of `s`, so an `s`-indexed
product factors across the blocks. -/
lemma prod_prod_parts {s : Finset ι} (π : Finpartition s) (a : ι → ℝ) :
    ∏ B ∈ π.parts, ∏ i ∈ B, a i = ∏ i ∈ s, a i := by
  classical
  have hdisj : (π.parts : Set (Finset ι)).PairwiseDisjoint id := π.disjoint
  conv_rhs => rw [← π.biUnion_parts, Finset.prod_biUnion hdisj]
  rfl

end Partitions

/-! ### Section 3.  Joint moments and cumulants

Janson's mixed semiinvariants and the moment–cumulant relation.
-/

section Probability

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [DecidableEq ι]

/-- The raw joint moment `E ∏_{i ∈ s} X i`. -/
noncomputable def jointMoment (μ : Measure Ω) (X : ι → Ω → ℝ) (s : Finset ι) : ℝ :=
  ∫ ω, ∏ i ∈ s, X i ω ∂μ

omit [DecidableEq ι] in
@[simp]
lemma jointMoment_empty (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) :
    jointMoment μ X ∅ = 1 := by
  simp [jointMoment]

omit [DecidableEq ι] in
/-- For a constant family the joint moment is the raw moment of the corresponding order. -/
lemma jointMoment_const_fun (μ : Measure Ω) (X : Ω → ℝ) (s : Finset ι) :
    jointMoment μ (fun _ => X) s = ∫ ω, X ω ^ #s ∂μ := by
  simp [jointMoment, Finset.prod_const]

/-- **Janson (4.1).** The mixed semiinvariant of the family `(X_i)_{i ∈ s}`. -/
noncomputable def mixedCumulant (μ : Measure Ω) (X : ι → Ω → ℝ) (s : Finset ι) : ℝ :=
  mobius (jointMoment μ X) s

/-- The definition, written as a linear combination of products `∏_k E ∏_{i ∈ I_k} X_i` over
the partitions `I_1, …, I_l` of `s`. -/
lemma mixedCumulant_eq (μ : Measure Ω) (X : ι → Ω → ℝ) (s : Finset ι) :
    mixedCumulant μ X s
      = ∑ π : Finpartition s,
          ((-1) ^ (#π.parts - 1) * (Nat.factorial (#π.parts - 1) : ℝ))
            * ∏ B ∈ π.parts, ∫ ω, ∏ i ∈ B, X i ω ∂μ := rfl

/-- **Janson (2.1).** The `j`-th semiinvariant `κ_j (X)`, the mixed semiinvariant of `j`
copies of `X`. -/
noncomputable def cumulant (X : Ω → ℝ) (j : ℕ) (μ : Measure Ω) : ℝ :=
  mixedCumulant μ (fun _ : Fin j => X) univ

/-- **Moment–cumulant relation.** The joint moment is the sum over partitions of the products
of cumulants of the blocks. -/
theorem partSum_mixedCumulant (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (s : Finset ι) :
    ∑ π : Finpartition s, ∏ B ∈ π.parts, mixedCumulant μ X B = jointMoment μ X s :=
  partSum_mobius _ (jointMoment_empty μ X) s

@[simp]
lemma mixedCumulant_empty (μ : Measure Ω) (X : ι → Ω → ℝ) : mixedCumulant μ X ∅ = 1 :=
  mobius_empty _

@[simp]
lemma mixedCumulant_singleton (μ : Measure Ω) (X : ι → Ω → ℝ) (i : ι) :
    mixedCumulant μ X {i} = ∫ ω, X i ω ∂μ := by
  rw [mixedCumulant, mobius_singleton, jointMoment]
  simp

/-! #### The first three univariate cumulants -/

@[simp]
lemma cumulant_zero (X : Ω → ℝ) (μ : Measure Ω) : cumulant X 0 μ = 1 := by
  rw [cumulant, mixedCumulant, show (univ : Finset (Fin 0)) = ∅ from rfl, mobius_empty]

/-- `κ_1 (X) = E X`. -/
theorem cumulant_one (X : Ω → ℝ) (μ : Measure Ω) : cumulant X 1 μ = ∫ ω, X ω ∂μ := by
  rw [cumulant, show (univ : Finset (Fin 1)) = {0} from rfl, mixedCumulant_singleton]

/-- `κ_2 (X) = E X² - (E X)²`, as an identity of Bochner integrals (a non-integrable integral is
`0`); for square-integrable `X` this is the variance, see `cumulant_two_eq_variance`. -/
theorem cumulant_two (X : Ω → ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    cumulant X 2 μ = (∫ ω, X ω ^ 2 ∂μ) - (∫ ω, X ω ∂μ) ^ 2 := by
  classical
  set f : Finset (Fin 2) → ℝ := jointMoment μ (fun _ : Fin 2 => X) with hf
  have hf0 : f ∅ = 1 := jointMoment_empty μ _
  have hset : ((univ : Finset (Fin 2)).powerset.filter (fun D => (0 : Fin 2) ∈ D)).erase univ
      = {({0} : Finset (Fin 2))} := by decide
  rw [cumulant, mixedCumulant, ← hf, mobius_eq_sub f hf0 (i₀ := 0) (Finset.mem_univ _), hset,
    Finset.sum_singleton, mobius_singleton]
  rw [hf, jointMoment_const_fun, jointMoment_const_fun, jointMoment_const_fun,
    show #(univ : Finset (Fin 2)) = 2 from rfl, show #({0} : Finset (Fin 2)) = 1 from rfl,
    show #((univ : Finset (Fin 2)) \ {0}) = 1 from rfl]
  simp [sq]

/-- `κ_2 (X) = Var X` for square-integrable `X`. -/
theorem cumulant_two_eq_variance {X : Ω → ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hX : MemLp X 2 μ) : cumulant X 2 μ = variance X μ := by
  rw [cumulant_two, variance_eq_sub hX]
  rfl

/-- `κ_3 (X) = E X³ - 3 E X² E X + 2 (E X)³`. -/
theorem cumulant_three (X : Ω → ℝ) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    cumulant X 3 μ
      = (∫ ω, X ω ^ 3 ∂μ) - 3 * (∫ ω, X ω ^ 2 ∂μ) * (∫ ω, X ω ∂μ)
          + 2 * (∫ ω, X ω ∂μ) ^ 3 := by
  classical
  set f : Finset (Fin 3) → ℝ := jointMoment μ (fun _ : Fin 3 => X) with hf
  have hf0 : f ∅ = 1 := jointMoment_empty μ _
  have hset : ((univ : Finset (Fin 3)).powerset.filter (fun D => (0 : Fin 3) ∈ D)).erase univ
      = {({0} : Finset (Fin 3)), {0, 1}, {0, 2}} := by decide
  have hpair : ∀ b : Fin 3, b ≠ 0 →
      mobius f {0, b} = f {0, b} - f {0} * f {b} := by
    intro b hb
    have hmem : (0 : Fin 3) ∈ ({0, b} : Finset (Fin 3)) := by simp
    have hset2 : (({0, b} : Finset (Fin 3)).powerset.filter (fun D => (0 : Fin 3) ∈ D)).erase
        {0, b} = {({0} : Finset (Fin 3))} := by
      revert hb; revert b; decide
    have hsd : ({0, b} : Finset (Fin 3)) \ {0} = {b} := by revert hb; revert b; decide
    rw [mobius_eq_sub f hf0 hmem, hset2, Finset.sum_singleton, mobius_singleton, hsd]
  rw [cumulant, mixedCumulant, ← hf, mobius_eq_sub f hf0 (i₀ := 0) (Finset.mem_univ _), hset]
  rw [show ({({0} : Finset (Fin 3)), {0, 1}, {0, 2}} : Finset (Finset (Fin 3)))
      = insert ({0} : Finset (Fin 3)) (insert ({0, 1} : Finset (Fin 3)) {({0, 2})}) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    mobius_singleton, hpair 1 (by decide), hpair 2 (by decide)]
  rw [hf]
  simp only [jointMoment_const_fun]
  norm_num [show #(univ : Finset (Fin 3)) = 3 from rfl,
    show #((univ : Finset (Fin 3)) \ {0}) = 2 from rfl,
    show #((univ : Finset (Fin 3)) \ {0, 1}) = 1 from rfl,
    show #((univ : Finset (Fin 3)) \ {0, 2}) = 1 from rfl,
    show #({0} : Finset (Fin 3)) = 1 from rfl,
    show #({0, 1} : Finset (Fin 3)) = 2 from rfl,
    show #({0, 2} : Finset (Fin 3)) = 2 from rfl,
    show #({1} : Finset (Fin 3)) = 1 from rfl,
    show #({2} : Finset (Fin 3)) = 1 from rfl]
  ring

/-! #### Janson (2.3): homogeneity of degree `#s` -/

omit [DecidableEq ι] in
/-- Scaling each variable of the family scales the joint moment by the product of the
factors. -/
lemma jointMoment_smul (μ : Measure Ω) (X : ι → Ω → ℝ) (a : ι → ℝ) (s : Finset ι) :
    jointMoment μ (fun i => fun ω => a i * X i ω) s = (∏ i ∈ s, a i) * jointMoment μ X s := by
  rw [jointMoment, jointMoment, ← integral_const_mul]
  congr 1
  funext ω
  rw [Finset.prod_mul_distrib]

/-- **Janson (2.3), mixed form.** `κ (a_1 X_1, …, a_j X_j) = (∏ a_i) κ (X_1, …, X_j)`. -/
theorem mixedCumulant_smul (μ : Measure Ω) (X : ι → Ω → ℝ) (a : ι → ℝ) (s : Finset ι) :
    mixedCumulant μ (fun i => fun ω => a i * X i ω) s
      = (∏ i ∈ s, a i) * mixedCumulant μ X s := by
  classical
  rw [mixedCumulant, mixedCumulant, mobius, mobius, Finset.mul_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [Finset.prod_congr rfl (fun B _ => jointMoment_smul μ X a B), Finset.prod_mul_distrib,
    prod_prod_parts π a]
  ring

/-- **Janson (2.3).** `κ_j (a X) = a^j κ_j (X)`. -/
theorem cumulant_const_smul (X : Ω → ℝ) (a : ℝ) (j : ℕ) (μ : Measure Ω) :
    cumulant (fun ω => a * X ω) j μ = a ^ j * cumulant X j μ := by
  rw [cumulant, cumulant,
    show (fun _ : Fin j => fun ω => a * X ω) = (fun i : Fin j => fun ω => (fun _ => a) i * X ω)
      from rfl,
    mixedCumulant_smul μ (fun _ : Fin j => X) (fun _ => a) univ]
  simp

/-! #### Janson (2.2): additivity over independent summands -/

/-- The joint moments of a sum of independent variables convolve. The integrability hypotheses
state that `X ^ r` and `Y ^ r` are integrable for every `r ≤ n`. -/
theorem jointMoment_add_of_indepFun {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y μ) {n : ℕ}
    (hXi : ∀ r ≤ n, Integrable (fun ω => X ω ^ r) μ)
    (hYi : ∀ r ≤ n, Integrable (fun ω => Y ω ^ r) μ)
    {t : Finset ι} (htn : #t ≤ n) :
    jointMoment μ (fun _ : ι => fun ω => X ω + Y ω) t
      = ∑ A ∈ t.powerset,
          jointMoment μ (fun _ : ι => X) A * jointMoment μ (fun _ : ι => Y) (t \ A) := by
  classical
  set m := #t with hm
  have hindep : ∀ r : ℕ, IndepFun (fun ω => X ω ^ r) (fun ω => Y ω ^ (m - r)) μ :=
    fun r => hXY.comp (measurable_id.pow_const r) (measurable_id.pow_const (m - r))
  have hint : ∀ r ∈ Finset.range (m + 1),
      Integrable (fun ω => X ω ^ r * Y ω ^ (m - r) * ((m.choose r : ℕ) : ℝ)) μ := by
    intro r hr
    rw [Finset.mem_range] at hr
    exact (((hindep r).integrable_mul (hXi r (le_trans (by omega) htn))
      (hYi (m - r) (le_trans (by omega) htn)))).mul_const _
  have hrhs : ∀ A ∈ t.powerset,
      jointMoment μ (fun _ : ι => X) A * jointMoment μ (fun _ : ι => Y) (t \ A)
        = (∫ ω, X ω ^ #A ∂μ) * (∫ ω, Y ω ^ (m - #A) ∂μ) := by
    intro A hA
    rw [Finset.mem_powerset] at hA
    rw [jointMoment_const_fun, jointMoment_const_fun, Finset.card_sdiff,
      Finset.inter_eq_left.mpr hA]
  rw [jointMoment_const_fun, Finset.sum_congr rfl hrhs,
    Finset.sum_powerset_apply_card (fun r => (∫ ω, X ω ^ r ∂μ) * (∫ ω, Y ω ^ (m - r) ∂μ))]
  simp only [nsmul_eq_mul]
  rw [← hm]
  have hbin : (fun ω => (X ω + Y ω) ^ m)
      = fun ω => ∑ r ∈ Finset.range (m + 1), X ω ^ r * Y ω ^ (m - r) * ((m.choose r : ℕ) : ℝ) := by
    funext ω
    exact add_pow _ _ _
  rw [hbin, integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [integral_mul_const,
    (hindep r).integral_fun_mul_eq_mul_integral (hX.pow_const r).aestronglyMeasurable
      (hY.pow_const (m - r)).aestronglyMeasurable]
  ring

/-- **Janson (2.2).** `κ_j (X + Y) = κ_j (X) + κ_j (Y)` for independent `X` and `Y`. -/
theorem cumulant_add_of_indepFun {μ : Measure Ω} [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y μ) {j : ℕ} (hj : 0 < j)
    (hXi : ∀ r ≤ j, Integrable (fun ω => X ω ^ r) μ)
    (hYi : ∀ r ≤ j, Integrable (fun ω => Y ω ^ r) μ) :
    cumulant (fun ω => X ω + Y ω) j μ = cumulant X j μ + cumulant Y j μ := by
  classical
  rw [cumulant, cumulant, cumulant, mixedCumulant, mixedCumulant, mixedCumulant]
  refine mobius_add_of_conv (jointMoment_empty μ (fun _ : Fin j => X))
    (jointMoment_empty μ (fun _ : Fin j => Y)) (fun t => ?_) ?_
  · exact jointMoment_add_of_indepFun hX hY hXY hXi hYi
      (le_trans (Finset.card_le_card (Finset.subset_univ t)) (by simp))
  · exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hj⟩⟩

/-! #### Constants, and translation invariance at orders `≥ 2` -/

/-- The partition sum of a weight supported on singleton blocks: only the discrete partition
contributes. -/
lemma partSum_singletonWeight (c : ℝ) (t : Finset ι) :
    partSum (fun B => if #B = 1 then c else 0) t = c ^ #t := by
  classical
  induction t using Finset.strongInduction with
  | _ t ih =>
    rcases t.eq_empty_or_nonempty with rfl | ht
    · simp
    obtain ⟨i₀, hi₀⟩ := ht
    have hmem : ({i₀} : Finset ι) ∈ t.powerset.filter (fun D => i₀ ∈ D) :=
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hi₀),
        Finset.mem_singleton_self i₀⟩
    rw [partSum_recursion _ hi₀, ← Finset.add_sum_erase _ _ hmem]
    have hrest : ∀ D ∈ (t.powerset.filter (fun D => i₀ ∈ D)).erase ({i₀} : Finset ι),
        (if #D = 1 then c else 0) * partSum (fun B => if #B = 1 then c else 0) (t \ D) = 0 := by
      intro D hD
      rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_powerset] at hD
      have hne : #D ≠ 1 := fun hcon => hD.1 (by
        obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcon
        rw [hx] at hD ⊢
        rw [Finset.mem_singleton.mp hD.2.2])
      rw [ite_eq_right hne, zero_mul]
    rw [Finset.sum_congr rfl hrest, Finset.sum_const_zero, add_zero, Finset.card_singleton,
      ite_eq_left rfl, ih _ ((Finset.ssubset_iff_of_subset Finset.sdiff_subset).mpr
        ⟨i₀, hi₀, by simp⟩)]
    have hcard : #t - 1 + 1 = #t := by
      have hpos : 1 ≤ #t := Finset.card_pos.mpr ⟨i₀, hi₀⟩
      omega
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.singleton_subset_iff.mpr hi₀),
      Finset.card_singleton, ← pow_succ', hcard]

omit [DecidableEq ι] in
@[simp]
lemma jointMoment_const (μ : Measure Ω) [IsProbabilityMeasure μ] (c : ℝ) (s : Finset ι) :
    jointMoment μ (fun _ : ι => fun _ : Ω => c) s = c ^ #s := by
  simp [jointMoment]

/-- The mixed cumulant of a constant family is `c` at a singleton and `0` at any larger
index set. -/
theorem mixedCumulant_const (μ : Measure Ω) [IsProbabilityMeasure μ] (c : ℝ) {s : Finset ι}
    (hs : s.Nonempty) :
    mixedCumulant μ (fun _ : ι => fun _ : Ω => c) s = if #s = 1 then c else 0 := by
  refine eq_of_partSum_eq (f := mixedCumulant μ (fun _ : ι => fun _ : Ω => c))
    (g := fun B => if #B = 1 then c else 0) (fun t => ?_) hs
  rw [partSum, partSum_mixedCumulant, partSum_singletonWeight, jointMoment_const]

/-- `κ_j (c) = 0` for `j ≥ 2`, and `κ_1 (c) = c`. -/
theorem cumulant_const (c : ℝ) {j : ℕ} (hj : 0 < j) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    cumulant (fun _ : Ω => c) j μ = if j = 1 then c else 0 := by
  rw [cumulant, mixedCumulant_const μ c (Finset.univ_nonempty_iff.mpr ⟨⟨0, hj⟩⟩)]
  simp

/-- Translation invariance at orders `≥ 2`: `κ_j (X + c) = κ_j (X)`. -/
theorem cumulant_add_const (X : Ω → ℝ) (hX : Measurable X) (c : ℝ) {j : ℕ} (hj : 2 ≤ j)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hXi : ∀ r ≤ j, Integrable (fun ω => X ω ^ r) μ) :
    cumulant (fun ω => X ω + c) j μ = cumulant X j μ := by
  rw [cumulant_add_of_indepFun hX measurable_const (indepFun_const_right X c) (by omega) hXi
      (fun r _ => integrable_const _), cumulant_const c (by omega)]
  simp only [show j ≠ 1 by omega, ite_false, add_zero]

/-! #### Janson (4.4): the size of a mixed cumulant

For variables bounded by `A` almost surely, the mixed cumulant over `s` is at most
`C_{#s} A^{#s}`, proved directly from the partition expansion.
-/

/-- The constant of Janson (4.4): `∑_{π ∈ P(s)} (|π| - 1)!`. -/
noncomputable def mobiusBound (s : Finset ι) : ℝ :=
  ∑ π : Finpartition s, |mobiusWeight #π.parts|

lemma mobiusBound_nonneg (s : Finset ι) : 0 ≤ mobiusBound s :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

omit [DecidableEq ι] in
/-- A joint moment of uniformly bounded variables is bounded by the corresponding power. -/
lemma abs_jointMoment_le (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) {A : ℝ} (hbd : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ A) (B : Finset ι) :
    |jointMoment μ X B| ≤ A ^ #B := by
  classical
  have hae : ∀ᵐ ω ∂μ, |∏ i ∈ B, X i ω| ≤ A ^ #B := by
    have hall := (ae_ball_iff (Set.to_countable (↑B : Set ι))).mpr
      (fun i (_ : i ∈ (↑B : Set ι)) => hbd i)
    filter_upwards [hall] with ω hω
    rw [Finset.abs_prod]
    calc ∏ i ∈ B, |X i ω| ≤ ∏ _i ∈ B, A :=
          Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i hi => hω i hi)
      _ = A ^ #B := by rw [Finset.prod_const]
  have hmeas : Measurable (fun ω => ∏ i ∈ B, X i ω) :=
    Finset.measurable_prod _ fun i _ => hX i
  have hint : Integrable (fun ω => ∏ i ∈ B, X i ω) μ :=
    Integrable.mono' (integrable_const (A ^ #B)) hmeas.aestronglyMeasurable
      (by filter_upwards [hae] with ω hω using by rwa [Real.norm_eq_abs])
  rw [jointMoment, ← Real.norm_eq_abs]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  refine le_trans (integral_mono_ae hint.norm (integrable_const (A ^ #B)) ?_) (by simp)
  filter_upwards [hae] with ω hω
  rwa [Real.norm_eq_abs]

/-- **Janson (4.4), bounded form.** With `|X_i| ≤ A` a.s., the mixed cumulant of the family
over `s` is at most `C_{#s} A^{#s}`. -/
theorem abs_mixedCumulant_le (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) {A : ℝ} (hbd : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ A)
    (s : Finset ι) :
    |mixedCumulant μ X s| ≤ mobiusBound s * A ^ #s := by
  classical
  rw [mixedCumulant, mobius, mobiusBound, Finset.sum_mul]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun π _ => ?_)
  rw [abs_mul, Finset.abs_prod]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc ∏ B ∈ π.parts, |jointMoment μ X B|
      ≤ ∏ B ∈ π.parts, A ^ #B :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
          (fun B _ => abs_jointMoment_le μ X hX hbd B)
    _ = A ^ #s := by rw [Finset.prod_pow_eq_pow_sum, π.sum_card_parts]

/-- **Janson (4.4)** for the univariate cumulant. -/
theorem abs_cumulant_le (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : Measurable X) {A : ℝ} (hbd : ∀ᵐ ω ∂μ, |X ω| ≤ A) (j : ℕ) :
    |cumulant X j μ| ≤ mobiusBound (univ : Finset (Fin j)) * A ^ j := by
  have hb := abs_mixedCumulant_le μ (fun _ : Fin j => X) (fun _ => hX) (fun _ => hbd)
    (univ : Finset (Fin j))
  rw [cumulant]
  simpa using hb

/-! #### The cumulant depends on the variables only through their joint law -/

omit [DecidableEq ι] in
theorem jointMoment_map {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω) {g : Ω → Ω'}
    (hg : AEMeasurable g μ) (X : ι → Ω' → ℝ) (hX : ∀ i, Measurable (X i)) (s : Finset ι) :
    jointMoment (μ.map g) X s = jointMoment μ (fun i => fun ω => X i (g ω)) s := by
  rw [jointMoment, jointMoment,
    integral_map hg (Finset.measurable_prod _ fun i _ => hX i).aestronglyMeasurable]

theorem mixedCumulant_map {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω) {g : Ω → Ω'}
    (hg : AEMeasurable g μ) (X : ι → Ω' → ℝ) (hX : ∀ i, Measurable (X i)) (s : Finset ι) :
    mixedCumulant (μ.map g) X s = mixedCumulant μ (fun i => fun ω => X i (g ω)) s := by
  rw [mixedCumulant, mixedCumulant,
    show jointMoment (μ.map g) X = jointMoment μ (fun i => fun ω => X i (g ω)) from
      funext fun u => jointMoment_map μ hg X hX u]

theorem cumulant_map {Ω' : Type*} [MeasurableSpace Ω'] (μ : Measure Ω) {g : Ω → Ω'}
    (hg : AEMeasurable g μ) (X : Ω' → ℝ) (hX : Measurable X) (j : ℕ) :
    cumulant X j (μ.map g) = cumulant (fun ω => X (g ω)) j μ :=
  mixedCumulant_map μ hg (fun _ : Fin j => X) (fun _ => hX) univ

/-! #### Janson, Lemma 3: a mixed cumulant vanishes on an independently split family -/

/-- The family restricted to `a` and extended by `1` outside `a`, so that its product over a
subset of `a` is the product of the original family. -/
noncomputable def splitPart (X : ι → Ω → ℝ) (a : Finset ι) (ω : Ω) (i : ι) : ℝ :=
  if i ∈ a then X i ω else 1

lemma measurable_splitPart {X : ι → Ω → ℝ} (hXm : ∀ i, Measurable (X i)) (a : Finset ι) :
    Measurable (splitPart X a) := by
  refine Measurable.of_eval fun i => ?_
  by_cases hi : i ∈ a
  · have heq : (fun ω => splitPart X a ω i) = X i := by funext ω; simp [splitPart, hi]
    rw [heq]
    exact hXm i
  · have heq : (fun ω => splitPart X a ω i) = fun _ => (1 : ℝ) := by
      funext ω; simp [splitPart, hi]
    rw [heq]
    exact measurable_const

omit [MeasurableSpace Ω] in
lemma prod_splitPart {X : ι → Ω → ℝ} {a : Finset ι} (ω : Ω) {u : Finset ι} (hu : u ⊆ a) :
    ∏ i ∈ u, splitPart X a ω i = ∏ i ∈ u, X i ω :=
  Finset.prod_congr rfl fun i hi => by simp [splitPart, hu hi]

/-- The joint moment of an independently split family factors. -/
theorem jointMoment_split_of_indepFun {μ : Measure Ω} {X : ι → Ω → ℝ}
    (hXm : ∀ i, Measurable (X i)) {a b : Finset ι} (hab : Disjoint a b)
    (hindep : IndepFun (splitPart X a) (splitPart X b) μ)
    {t : Finset ι} (hta : t ⊆ a ∪ b) :
    jointMoment μ X t = jointMoment μ X (t ∩ a) * jointMoment μ X (t ∩ b) := by
  classical
  have hdisj : Disjoint (t ∩ a) (t ∩ b) :=
    Finset.disjoint_left.mpr fun i hi hj =>
      (Finset.disjoint_left.mp hab (Finset.mem_inter.mp hi).2) (Finset.mem_inter.mp hj).2
  have hunion : (t ∩ a) ∪ (t ∩ b) = t := by
    rw [← Finset.inter_union_distrib_left]
    exact Finset.inter_eq_left.mpr hta
  -- the two measurable functions of the two independent halves
  have hmeasA : Measurable (fun v : ι → ℝ => ∏ i ∈ t ∩ a, v i) :=
    Finset.measurable_prod _ fun i _ => measurable_pi_apply i
  have hmeasB : Measurable (fun v : ι → ℝ => ∏ i ∈ t ∩ b, v i) :=
    Finset.measurable_prod _ fun i _ => measurable_pi_apply i
  have hcompA : ((fun v : ι → ℝ => ∏ i ∈ t ∩ a, v i) ∘ splitPart X a)
      = fun ω => ∏ i ∈ t ∩ a, X i ω :=
    funext fun ω => prod_splitPart ω Finset.inter_subset_right
  have hcompB : ((fun v : ι → ℝ => ∏ i ∈ t ∩ b, v i) ∘ splitPart X b)
      = fun ω => ∏ i ∈ t ∩ b, X i ω :=
    funext fun ω => prod_splitPart ω Finset.inter_subset_right
  have hindep' : IndepFun (fun ω => ∏ i ∈ t ∩ a, X i ω) (fun ω => ∏ i ∈ t ∩ b, X i ω) μ := by
    have := hindep.comp hmeasA hmeasB
    rwa [hcompA, hcompB] at this
  have hprod : (fun ω => ∏ i ∈ t, X i ω)
      = fun ω => (∏ i ∈ t ∩ a, X i ω) * (∏ i ∈ t ∩ b, X i ω) := by
    funext ω
    rw [← Finset.prod_union hdisj, hunion]
  rw [jointMoment, jointMoment, jointMoment, hprod,
    hindep'.integral_fun_mul_eq_mul_integral
      (Finset.measurable_prod _ fun i _ => hXm i).aestronglyMeasurable
      (Finset.measurable_prod _ fun i _ => hXm i).aestronglyMeasurable]

/-- If the joint moments of the family split across `a` and `b`, then `κ (X_i : i ∈ s) = 0`
whenever `s` meets both. -/
theorem mixedCumulant_eq_zero_of_split (μ : Measure Ω) [IsProbabilityMeasure μ] (X : ι → Ω → ℝ)
    {s a b : Finset ι} (hab : Disjoint a b) (hcover : s ⊆ a ∪ b)
    (hsplit : ∀ t : Finset ι, t ⊆ s →
      jointMoment μ X t = jointMoment μ X (t ∩ a) * jointMoment μ X (t ∩ b))
    (hsa : ¬ s ⊆ a) (hsb : ¬ s ⊆ b) :
    mixedCumulant μ X s = 0 :=
  mobius_eq_zero_of_split (jointMoment_empty μ X) hab hcover hsplit hsa hsb

/-- **Janson, Lemma 3.** If `{X_1, …, X_j}` can be divided into two independent nonempty sets
of random variables, then `κ (X_1, …, X_j) = 0`. -/
theorem mixedCumulant_eq_zero_of_indepFun (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (hXm : ∀ i, Measurable (X i)) {s a b : Finset ι} (hab : Disjoint a b)
    (hcover : s ⊆ a ∪ b) (hindep : IndepFun (splitPart X a) (splitPart X b) μ)
    (hsa : ¬ s ⊆ a) (hsb : ¬ s ⊆ b) :
    mixedCumulant μ X s = 0 :=
  mixedCumulant_eq_zero_of_split μ X hab hcover
    (fun _t hts => jointMoment_split_of_indepFun hXm hab hindep (hts.trans hcover)) hsa hsb

end Probability

/-! ### Section 4.  Examples

The results above are evaluated on a skewed two-point law with `κ_1 = 1`, `κ_2 = 3` and
`κ_3 = 6`.
-/

section Witness

open scoped ENNReal

namespace SkewWitness

/-- The skewed two-point law with the value `4` with probability `1/4` and the value `0`
with probability `3/4`. Its raw moments are `E X = 1`, `E X² = 4`, `E X³ = 16`. -/
noncomputable def skewLaw : Measure ℝ :=
  (1/4 : ℝ≥0∞) • Measure.dirac (4 : ℝ) + (3/4 : ℝ≥0∞) • Measure.dirac (0 : ℝ)

instance : IsProbabilityMeasure skewLaw := by
  constructor
  simp only [skewLaw, Measure.coe_add, Pi.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ, Pi.one_apply, mul_one]
  rw [ENNReal.div_add_div_same, show (1 : ℝ≥0∞) + 3 = 4 by norm_num]
  exact ENNReal.div_self (by norm_num) (by norm_num)

private lemma int_one {f : ℝ → ℝ} (hf : Measurable f) :
    Integrable f ((1/4 : ℝ≥0∞) • Measure.dirac (4 : ℝ)) :=
  (integrable_dirac' hf.stronglyMeasurable (by simp)).smul_measure (by simp)

private lemma int_two {f : ℝ → ℝ} (hf : Measurable f) :
    Integrable f ((3/4 : ℝ≥0∞) • Measure.dirac (0 : ℝ)) :=
  (integrable_dirac' hf.stronglyMeasurable (by simp)).smul_measure
    (by simp [ENNReal.div_eq_top])

theorem integrable_skew {f : ℝ → ℝ} (hf : Measurable f) : Integrable f skewLaw := by
  rw [skewLaw]
  exact (int_one hf).add_measure (int_two hf)

theorem skewIntegral {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ x, f x ∂skewLaw = f 4 / 4 + 3 * f 0 / 4 := by
  rw [skewLaw, integral_add_measure (int_one hf) (int_two hf), integral_smul_measure,
    integral_smul_measure, integral_dirac, integral_dirac,
    show ((1/4 : ℝ≥0∞)).toReal = (1/4 : ℝ) by rw [ENNReal.toReal_div]; norm_num,
    show ((3/4 : ℝ≥0∞)).toReal = (3/4 : ℝ) by rw [ENNReal.toReal_div]; norm_num]
  simp only [smul_eq_mul]
  ring

theorem skew_moment (r : ℕ) : ∫ x, x ^ r ∂skewLaw = 4 ^ r / 4 + 3 * 0 ^ r / 4 :=
  skewIntegral (measurable_id.pow_const r)

@[simp] theorem skew_moment_one : ∫ x : ℝ, x ∂skewLaw = 1 := by
  have := skew_moment 1
  simpa using this

@[simp] theorem skew_moment_two : ∫ x : ℝ, x ^ 2 ∂skewLaw = 4 := by
  have := skew_moment 2
  norm_num at this
  exact this

@[simp] theorem skew_moment_three : ∫ x : ℝ, x ^ 3 ∂skewLaw = 16 := by
  have := skew_moment 3
  norm_num at this
  exact this

/-- `κ_1 = E X = 1`, through `cumulant_one`. -/
theorem skew_cumulant_one : cumulant id 1 skewLaw = 1 := by
  rw [cumulant_one]
  exact skew_moment_one

/-- `κ_2 = var X = 3`, through `cumulant_two`. -/
theorem skew_cumulant_two : cumulant id 2 skewLaw = 3 := by
  rw [cumulant_two, show (fun x : ℝ => (id x) ^ 2) = fun x : ℝ => x ^ 2 from rfl,
    show (fun x : ℝ => id x) = fun x : ℝ => x from rfl]
  simp only [skew_moment_one, skew_moment_two]
  norm_num

/-- `κ_3 = 6`, through `cumulant_three`. -/
theorem skew_cumulant_three : cumulant id 3 skewLaw = 6 := by
  rw [cumulant_three]
  rw [show (fun x : ℝ => (id x) ^ 3) = fun x : ℝ => x ^ 3 from rfl,
    show (fun x : ℝ => (id x) ^ 2) = fun x : ℝ => x ^ 2 from rfl]
  simp only [skew_moment_one, skew_moment_two, skew_moment_three, id_eq]
  norm_num

theorem skew_cumulant_three_ne_zero : cumulant id 3 skewLaw ≠ 0 := by
  rw [skew_cumulant_three]
  norm_num

/-- Janson (2.3) at `a = 2` and `j = 3`: `κ_3 (2 X) = 2³ κ_3 (X) = 48`. -/
theorem skew_scaling_witness : cumulant (fun x : ℝ => 2 * id x) 3 skewLaw = 48 := by
  rw [cumulant_const_smul, skew_cumulant_three]
  norm_num

/-- The moment–cumulant inversion at `j = 2`: the two partitions of a two-element set
contribute `κ_1² = 1` and `κ_2 = 3`, summing to the second raw moment `4`. -/
theorem skew_inversion_witness :
    (∑ π : Finpartition (univ : Finset (Fin 2)), ∏ B ∈ π.parts,
        mixedCumulant skewLaw (fun _ : Fin 2 => (id : ℝ → ℝ)) B) = 4 := by
  rw [partSum_mixedCumulant, jointMoment_const_fun]
  rw [show (fun x : ℝ => (id x) ^ #(univ : Finset (Fin 2))) = fun x : ℝ => x ^ 2 from rfl]
  exact skew_moment_two

/-- The discrete partition's contribution to `skew_inversion_witness`: `κ_1 = 1`. -/
theorem skew_inversion_block_singleton (i : Fin 2) :
    mixedCumulant skewLaw (fun _ : Fin 2 => (id : ℝ → ℝ)) {i} = 1 := by
  rw [mixedCumulant_singleton]
  exact skew_moment_one

/-- The indiscrete partition's contribution to `skew_inversion_witness`: `κ_2 = 3`. -/
theorem skew_inversion_block_full :
    mixedCumulant skewLaw (fun _ : Fin 2 => (id : ℝ → ℝ)) univ = 3 :=
  skew_cumulant_two

/-- `κ_3` of a constant is `0`, through `cumulant_const`, at a nonzero constant. -/
theorem skew_const_witness : cumulant (fun _ : ℝ => (5 : ℝ)) 3 skewLaw = 0 := by
  rw [cumulant_const (5 : ℝ) (by norm_num)]
  norm_num

/-- `κ_1` of a constant is the constant. -/
theorem skew_const_one_witness : cumulant (fun _ : ℝ => (5 : ℝ)) 1 skewLaw = 5 := by
  rw [cumulant_const (5 : ℝ) (by norm_num)]
  norm_num

/-- Translation invariance at order `3`: shifting by `5` leaves `κ_3 = 6` unchanged. -/
theorem skew_translation_witness : cumulant (fun x : ℝ => id x + 5) 3 skewLaw = 6 := by
  rw [cumulant_add_const id measurable_id 5 (by norm_num) skewLaw
      (fun r _ => integrable_skew (measurable_id.pow_const r)),
    skew_cumulant_three]

/-- The skewed law is supported on `{0, 4}`, so `|X| ≤ 4` almost surely. -/
theorem skew_bounded : ∀ᵐ x ∂skewLaw, |id x| ≤ 4 := by
  rw [ae_iff]
  have hms : MeasurableSet {x : ℝ | ¬ |id x| ≤ 4} :=
    (measurableSet_le (measurable_id.comp measurable_id).norm measurable_const).compl
  simp only [skewLaw, Measure.coe_add, Pi.add_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ hms]
  rw [Set.indicator_of_notMem (by norm_num), Set.indicator_of_notMem (by norm_num)]
  simp

/-- Janson (4.4) on the skewed law, where the bounded quantity is `6`. -/
theorem skew_bound_witness :
    |cumulant id 3 skewLaw| ≤ mobiusBound (univ : Finset (Fin 3)) * 4 ^ 3 :=
  abs_cumulant_le skewLaw id measurable_id skew_bounded 3

theorem skew_bound_witness_lhs : |cumulant id 3 skewLaw| = 6 := by
  rw [skew_cumulant_three]
  norm_num

/-! #### Two independent copies -/

/-- Two independent copies of the skewed law. -/
noncomputable def pairLaw : Measure (Fin 2 → ℝ) := Measure.pi fun _ => skewLaw

instance : IsProbabilityMeasure pairLaw := by
  unfold pairLaw; infer_instance

/-- The `i`-th coordinate. -/
def coord (i : Fin 2) (ω : Fin 2 → ℝ) : ℝ := ω i

theorem map_coord (i : Fin 2) : pairLaw.map (coord i) = skewLaw :=
  (MeasureTheory.measurePreserving_eval (fun _ => skewLaw) i).map_eq

/-- Every coordinate has the cumulants of the skewed law. -/
theorem coord_cumulant (i : Fin 2) (j : ℕ) :
    cumulant (coord i) j pairLaw = cumulant id j skewLaw := by
  have hm : Measurable (coord i) := measurable_pi_apply i
  rw [← map_coord i, cumulant_map pairLaw hm.aemeasurable id measurable_id]
  rfl

theorem coord_integrable (i : Fin 2) (r : ℕ) :
    Integrable (fun ω => coord i ω ^ r) pairLaw := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ r) (pairLaw.map (coord i)) := by
    rw [map_coord i]
    exact (measurable_id.pow_const r).aestronglyMeasurable
  have hint : Integrable (fun x : ℝ => x ^ r) (pairLaw.map (coord i)) := by
    rw [map_coord i]
    exact integrable_skew (measurable_id.pow_const r)
  have hm : Measurable (coord i) := measurable_pi_apply i
  exact (integrable_map_measure hmeas hm.aemeasurable).mp hint

theorem coord_indep : IndepFun (coord 0) (coord 1) pairLaw :=
  (iIndepFun_pi (μ := fun _ : Fin 2 => skewLaw) (X := fun _ => (id : ℝ → ℝ))
    (fun _ => aemeasurable_id)).indepFun (by decide)

/-- Janson (2.2): `κ_3 (X + Y) = 6 + 6 = 12` for two independent skewed variables. -/
theorem skew_additivity_witness :
    cumulant (fun ω => coord 0 ω + coord 1 ω) 3 pairLaw = 12 := by
  have h0 : Measurable (coord 0) := measurable_pi_apply 0
  have h1 : Measurable (coord 1) := measurable_pi_apply 1
  rw [cumulant_add_of_indepFun h0 h1 coord_indep (by norm_num)
      (fun r _ => coord_integrable 0 r) (fun r _ => coord_integrable 1 r),
    coord_cumulant, coord_cumulant, skew_cumulant_three]
  norm_num

/-- The two halves of the pair, as functions of one coordinate each. -/
private def lift (i : Fin 2) (x : ℝ) : Fin 2 → ℝ := fun k => if k ∈ ({i} : Finset (Fin 2))
  then x else 1

private lemma measurable_lift (i : Fin 2) : Measurable (lift i) :=
  Measurable.of_eval fun k => by
    by_cases hk : k ∈ ({i} : Finset (Fin 2))
    · have heq : (fun x : ℝ => lift i x k) = fun x : ℝ => x := by funext x; simp [lift, hk]
      rw [heq]; exact measurable_id
    · have heq : (fun x : ℝ => lift i x k) = fun _ : ℝ => (1 : ℝ) := by funext x; simp [lift, hk]
      rw [heq]; exact measurable_const

private lemma splitPart_coord (i : Fin 2) :
    splitPart coord ({i} : Finset (Fin 2)) = lift i ∘ coord i := by
  funext ω k
  by_cases hk : k ∈ ({i} : Finset (Fin 2))
  · rw [Finset.mem_singleton] at hk
    subst hk
    simp [splitPart, lift, coord]
  · simp [splitPart, lift, hk]

theorem split_indep :
    IndepFun (splitPart coord ({0} : Finset (Fin 2)))
      (splitPart coord ({1} : Finset (Fin 2))) pairLaw := by
  rw [splitPart_coord 0, splitPart_coord 1]
  exact coord_indep.comp (measurable_lift 0) (measurable_lift 1)

/-- Janson, Lemma 3: the mixed cumulant of two independent coordinates vanishes. -/
theorem skew_lemma_three_witness : mixedCumulant pairLaw coord univ = 0 := by
  refine mixedCumulant_eq_zero_of_indepFun pairLaw (fun i => measurable_pi_apply i)
    (a := ({0} : Finset (Fin 2))) (b := ({1} : Finset (Fin 2))) (by decide) (by decide)
    split_indep (by decide) (by decide)

/-- At the same index set and measure, a family made of two copies of the same coordinate has
mixed cumulant `3 ≠ 0`. -/
theorem skew_lemma_three_nonvacuous :
    mixedCumulant pairLaw (fun _ : Fin 2 => coord 0) univ = 3 := by
  rw [show mixedCumulant pairLaw (fun _ : Fin 2 => coord 0) univ = cumulant (coord 0) 2 pairLaw
    from rfl, coord_cumulant, skew_cumulant_two]

end SkewWitness

end Witness

end Cumulant

end StatLean.AsymptoticStatistics
