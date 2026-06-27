import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Packing of the Euclidean unit sphere (Wainwright Example 5.8)

A Chapter-5 metric-entropy prerequisite for the PCA minimax lower bound (Example 15.19): the unit
sphere of `ℝⁿ` admits a `1/2`-separated set of exponentially large cardinality,
```
log M(1/2; 𝕊ⁿ⁻¹, ‖·‖₂) ≥ n · log 2                    (Example 5.8)
```
i.e. a set `T` of unit vectors, pairwise at Euclidean distance `≥ 1/2`, with `log |T| ≥ n·log 2`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 5 (Metric entropy and its uses), Example 5.8
(used in Chapter 15, §15.3.4, Example 15.19).

## Proof architecture

The combinatorial existence of the packing is reduced to **one** quantitative geometric input,
isolated as the single named residual `two_pow_le_packingNumber_sphere`: the packing number of the
unit sphere at scale `1/2` is at least `2ⁿ` (Wainwright's volume/surface bound). Everything *around*
it is proved here from the Mathlib covering-number API
(`Mathlib/Topology/MetricSpace/CoveringNumbers.lean`):

* finiteness of the packing number (`packingNumber (1/2) 𝕊 ≠ ⊤`) from compactness of the sphere,
  via `packingNumber_two_mul_le_externalCoveringNumber` and a finite `1/4`-net;
* extraction of a concrete maximal-cardinality separated set
  (`exists_set_encard_eq_packingNumber`);
* translation of `Metric.IsSeparated` (a strict `edist` lower bound) and sphere membership into the
  norm-level statements `‖v‖ = 1` and `1/2 ≤ ‖u - v‖`.
-/

open scoped NNReal ENNReal
open Metric

namespace StatLean.Minimaxity

/-- **Wainwright Example 5.8, quantitative core (single residual).** The `1/2`-packing number of the
Euclidean unit sphere `𝕊ⁿ⁻¹ ⊆ ℝⁿ` is at least `2ⁿ`.

This is the genuine geometric heart of the example and the *only* `sorry` in this file. The rigorous
proof goes through the Haar→sphere **surface measure** `μ_S`
(`Mathlib/MeasureTheory/Constructions/HaarToSphere.lean`, `Measure.toSphere`): a maximal
`1/2`-separated set is also a `1/2`-cover, so `μ_S(𝕊) ≤ |T| · μ_S(cap(t, 1/2))`, and the spherical
cap bound `μ_S(cap(t, 1/2)) ≤ 2^{-n} · μ_S(𝕊)` yields `|T| ≥ 2ⁿ`. The ambient Lebesgue (ball)
volume ratio is *not* enough here — it only delivers a base `< 2`; the genuine base `2` requires the
surface measure (the cap estimate is sharp only after tuning the radius constant, hence is delicate
for small `n`).

TODO(mmx): discharge via `Measure.toSphere` polar disintegration + the spherical-cap surface
bound. -/
private theorem two_pow_le_packingNumber_sphere (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℕ∞) ^ n ≤
      packingNumber (1 / 2) (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
  sorry

/-- The `1/2`-packing number of the unit sphere of `ℝⁿ` is finite: the sphere is compact, hence
totally bounded, so it has a finite `1/4`-net, and the packing number at scale `1/2 = 2 · (1/4)` is
bounded by the external covering number at scale `1/4`. -/
private theorem packingNumber_sphere_ne_top (n : ℕ) :
    packingNumber (1 / 2) (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ⊤ := by
  set S : Set (EuclideanSpace ℝ (Fin n)) := sphere (0 : EuclideanSpace ℝ (Fin n)) 1 with hS
  -- A finite `1/4`-net of the (compact, hence totally bounded) sphere.
  have htb : TotallyBounded S := (isCompact_sphere _ _).totallyBounded
  obtain ⟨t, -, htfin, htcov⟩ :=
    finite_approx_of_totallyBounded htb ((1 / 4 : ℝ≥0) : ℝ) (by positivity)
  -- The net is a `1/4`-cover (closed balls contain the open balls).
  have hcover : IsCover (1 / 4) S t := by
    rw [isCover_iff_subset_iUnion_closedBall]
    exact htcov.trans (Set.iUnion₂_mono fun y _ => ball_subset_closedBall)
  -- Hence the external covering number at `1/4` is finite, and packing at `2·(1/4) = 1/2` ≤ it.
  have hext_ne : externalCoveringNumber (1 / 4) S ≠ ⊤ :=
    ne_top_of_le_ne_top htfin.encard_lt_top.ne hcover.externalCoveringNumber_le_encard
  have hpack_le : packingNumber (1 / 2) S ≤ externalCoveringNumber (1 / 4) S := by
    have h := packingNumber_two_mul_le_externalCoveringNumber (1 / 4 : ℝ≥0) S
    have e : (2 : ℝ≥0) * (1 / 4) = 1 / 2 := by
      apply NNReal.coe_injective; push_cast; norm_num
    rwa [e] at h
  exact ne_top_of_le_ne_top hext_ne hpack_le

-- USER-INPUT: `2^n ≤ |T|` packing-number lower bound for `𝕊ⁿ⁻¹` at scale `1/2`; Wainwright Ex 5.8.
-- Supplied internally by `two_pow_le_packingNumber_sphere` (named residual), not as a hypothesis.
/-- **Packing of the Euclidean unit sphere**, cardinality form (Wainwright Example 5.8): for `n ≥ 1`
there is a finite set `T` of `≥ 2ⁿ` unit vectors of `ℝⁿ` that are pairwise `≥ 1/2`-separated. -/
private theorem sphere_packing_card (n : ℕ) (hn : 1 ≤ n) :
    ∃ T : Finset (EuclideanSpace ℝ (Fin n)),
      (2 : ℝ) ^ n ≤ (T.card : ℝ) ∧
      (∀ v ∈ T, ‖v‖ = 1) ∧
      ∀ u ∈ T, ∀ v ∈ T, u ≠ v → (1 / 2 : ℝ) ≤ ‖u - v‖ := by
  set S : Set (EuclideanSpace ℝ (Fin n)) := sphere (0 : EuclideanSpace ℝ (Fin n)) 1 with hS
  have hfin : packingNumber (1 / 2) S ≠ ⊤ := packingNumber_sphere_ne_top n
  -- Extract a concrete maximal-cardinality `1/2`-separated subset of the sphere.
  obtain ⟨C, hCsub, hCfin, hCsep, hCenc⟩ := exists_set_encard_eq_packingNumber hfin
  refine ⟨hCfin.toFinset, ?_, ?_, ?_⟩
  · -- Cardinality: `2ⁿ ≤ |C| = |T|`, from the packing lower bound.
    have hge : (2 : ℕ∞) ^ n ≤ C.encard := by
      rw [hCenc]; exact two_pow_le_packingNumber_sphere n hn
    rw [hCfin.encard_eq_coe_toFinset_card] at hge
    have hnat : (2 : ℕ) ^ n ≤ hCfin.toFinset.card := by exact_mod_cast hge
    exact_mod_cast hnat
  · -- Unit norms: membership in `sphere 0 1`.
    intro v hv
    rw [Set.Finite.mem_toFinset] at hv
    exact mem_sphere_zero_iff_norm.mp (hCsub hv)
  · -- Separation: `IsSeparated` gives `(1/2 : ℝ≥0∞) < edist u v`, i.e. `1/2 < ‖u - v‖`.
    intro u hu v hv huv
    rw [Set.Finite.mem_toFinset] at hu hv
    have h := hCsep hu hv huv
    simp only at h  -- β-reduce the `Set.Pairwise` application to expose `edist`
    -- `h : ↑(1/2 : ℝ≥0) < edist u v`; rewrite both sides as `ENNReal.ofReal` and compare in `ℝ`.
    rw [edist_dist, ENNReal.coe_nnreal_eq,
      ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity), dist_eq_norm] at h
    have hhalf : ((1 / 2 : ℝ≥0) : ℝ) = (1 / 2 : ℝ) := by push_cast; norm_num
    rw [hhalf] at h
    exact le_of_lt h

/-- **Packing of the Euclidean unit sphere** (Wainwright Example 5.8): the unit sphere of `ℝⁿ`
contains a `1/2`-separated set `T` (pairwise Euclidean distance `≥ 1/2`) of unit vectors with
`log |T| ≥ n · log 2`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 5 (Metric entropy and its uses), Example 5.8. -/
theorem exists_sphere_packing (n : ℕ) :
    ∃ T : Finset (EuclideanSpace ℝ (Fin n)),
      (n : ℝ) * Real.log 2 ≤ Real.log T.card ∧
      (∀ v ∈ T, ‖v‖ = 1) ∧
      ∀ u ∈ T, ∀ v ∈ T, u ≠ v → (1 / 2 : ℝ) ≤ ‖u - v‖ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- `n = 0`: no unit vectors exist, but the bound is `0 ≤ log 0 = 0`, so the empty set works.
    subst hn
    refine ⟨∅, ?_, ?_, ?_⟩
    · simp
    · intro v hv; simp at hv
    · intro u hu; simp at hu
  · -- `n ≥ 1`: derive the `log` bound from the cardinality crux via monotonicity of `log`.
    obtain ⟨T, hcard, hnorm, hsep⟩ := sphere_packing_card n hn
    refine ⟨T, ?_, hnorm, hsep⟩
    have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
    have h := Real.log_le_log hpos hcard
    rwa [Real.log_pow] at h

end StatLean.Minimaxity
