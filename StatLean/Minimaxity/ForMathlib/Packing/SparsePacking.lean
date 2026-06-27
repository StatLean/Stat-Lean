import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Packing of sparse unit vectors (Wainwright Example 5.8 / Exercise 5.8)

A Chapter-5 metric-entropy prerequisite for the sparse-linear-regression minimax lower bound
(Example 15.16): the set of `s`-sparse unit vectors in `ℝᵈ` admits a `1/2`-separated set with
```
log M ≥ (s/2) · log((d − s)/s),
```
i.e. a set `T` of `s`-sparse unit vectors, pairwise at Euclidean distance `≥ 1/2`, with
`log |T| ≥ (s/2) log((d−s)/s)`. (Sparsity: at most `s` nonzero coordinates.)

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 5 (Metric entropy and its uses), Example 5.8
(used in Chapter 15, §15.3.3, Example 15.16).

## Proof architecture

The construction is **normalized support indicators**. To an `s`-element support `S ⊆ [d]` we attach
the unit vector `v_S = s^{-1/2} · 𝟙_S` (value `s^{-1/2}` on `S`, `0` elsewhere): it has norm `1` and
exactly `s` nonzero coordinates. For two supports `S, S'`,
```
‖v_S − v_S'‖² = (|S| + |S'| − 2|S ∩ S'|) / s = (2s − 2|S ∩ S'|)/s,
```
so whenever `2|S ∩ S'| ≤ s` we get `‖v_S − v_S'‖ ≥ 1 ≥ 1/2`. All of this geometry is discharged
below. The **only** residual is the combinatorial support count `exists_bounded_overlap_supports`: a
Gilbert–Varshamov packing of the `C(d,s)` weight-`s` supports with pairwise intersection `≤ s/2` and
`log |𝒮| ≥ (s/2) log((d−s)/s)`. Mapping `S ↦ v_S` (injective, since distinct supports give
`≥ 1`-separated vectors) transports that count to the sparse-vector packing.
-/

open scoped ENNReal
open Finset

namespace StatLean.Minimaxity

/-- The normalized support indicator `v_S = s^{-1/2} · 𝟙_S ∈ ℝᵈ`: value `s^{-1/2}` on the support
`S`, zero elsewhere. For `|S| = s` this is a unit vector with exactly `s` nonzero coordinates.

Formalizes Wainwright Example 5.8's packing element. Degenerate inputs (`s = 0`, or `S.card ≠ s`)
are harmless here: the scaling `s^{-1/2}` is still well defined (`Real.sqrt 0 = 0`, so the vector is
`0`), and all downstream lemmas carry the hypotheses `0 < s`, `S.card = s` that they need. -/
private noncomputable def sparseVec (d s : ℕ) (S : Finset (Fin d)) : EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => if i ∈ S then (Real.sqrt s)⁻¹ else 0)

private theorem sparseVec_apply (d s : ℕ) (S : Finset (Fin d)) (i : Fin d) :
    (sparseVec d s S) i = if i ∈ S then (Real.sqrt s)⁻¹ else 0 := rfl

/-- Each normalized support indicator with `|S| = s > 0` is a unit vector. -/
private theorem norm_sparseVec (d s : ℕ) (hs : 0 < s) (S : Finset (Fin d)) (hcard : S.card = s) :
    ‖sparseVec d s S‖ = 1 := by
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  rw [EuclideanSpace.norm_eq]
  have hsq : ∀ i, ‖(sparseVec d s S) i‖ ^ 2 = if i ∈ S then (s : ℝ)⁻¹ else 0 := by
    intro i
    rw [sparseVec_apply]
    by_cases h : i ∈ S <;>
      simp [h, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hspos.le]
  rw [Finset.sum_congr rfl (fun i _ => hsq i), Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const, hcard, nsmul_eq_mul, mul_inv_cancel₀ (ne_of_gt hspos), Real.sqrt_one]

/-- Two normalized support indicators with `|S| = |S'| = s` and pairwise intersection
`2|S ∩ S'| ≤ s` are `≥ 1/2`-separated (in fact `≥ 1`-separated):
`‖v_S − v_S'‖² = (2s − 2|S ∩ S'|)/s ≥ 1`. -/
private theorem half_le_norm_sparseVec_sub (d s : ℕ) (hs : 0 < s) (S S' : Finset (Fin d))
    (hS : S.card = s) (hS' : S'.card = s) (hov : 2 * (S ∩ S').card ≤ s) :
    (1 / 2 : ℝ) ≤ ‖sparseVec d s S - sparseVec d s S'‖ := by
  have hspos : (0 : ℝ) < s := by exact_mod_cast hs
  -- Abbreviations for the `{0,1}` indicators.
  set χ : Finset (Fin d) → Fin d → ℝ := fun A i => if i ∈ A then (1 : ℝ) else 0 with hχ
  have sumχ : ∀ A : Finset (Fin d), ∑ i, χ A i = (A.card : ℝ) := by
    intro A
    rw [hχ]; simp only
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, mul_one]
  -- Per-coordinate: `‖(v_S − v_S') i‖² = s⁻¹ · (χ_S i − χ_S' i)²`.
  have happ : ∀ i, ‖(sparseVec d s S - sparseVec d s S') i‖ ^ 2
      = (s : ℝ)⁻¹ * (χ S i - χ S' i) ^ 2 := by
    intro i
    have ha2 : ((Real.sqrt s)⁻¹) ^ 2 = (s : ℝ)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt hspos.le]
    rw [PiLp.sub_apply, sparseVec_apply, sparseVec_apply, Real.norm_eq_abs, sq_abs, hχ]
    simp only
    rw [show (if i ∈ S then (Real.sqrt s)⁻¹ else 0)
          = (Real.sqrt s)⁻¹ * (if i ∈ S then (1 : ℝ) else 0) by rw [mul_ite, mul_one, mul_zero],
        show (if i ∈ S' then (Real.sqrt s)⁻¹ else 0)
          = (Real.sqrt s)⁻¹ * (if i ∈ S' then (1 : ℝ) else 0) by rw [mul_ite, mul_one, mul_zero],
        ← mul_sub, mul_pow, ha2]
  -- Per-coordinate identity `(χ_S i − χ_S' i)² = χ_S i + χ_S' i − 2·χ_{S∩S'} i`.
  have key : ∀ i, (χ S i - χ S' i) ^ 2 = χ S i + χ S' i - χ (S ∩ S') i - χ (S ∩ S') i := by
    intro i
    rw [hχ]; simp only [Finset.mem_inter]
    by_cases h1 : i ∈ S <;> by_cases h2 : i ∈ S' <;>
      simp only [h1, h2, if_true, if_false, and_true, and_false] <;> ring
  -- Sum the per-coordinate squared norms.
  have hsumeq : ∑ i, ‖(sparseVec d s S - sparseVec d s S') i‖ ^ 2
      = (s : ℝ)⁻¹ * (2 * s - 2 * ((S ∩ S').card : ℝ)) := by
    rw [Finset.sum_congr rfl (fun i _ => happ i), ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_congr rfl (fun i _ => key i)]
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, sumχ, sumχ, sumχ,
      hS, hS']
    ring
  -- The squared norm is `≥ 1`.
  have hsum_ge : (1 : ℝ) ≤ ∑ i, ‖(sparseVec d s S - sparseVec d s S') i‖ ^ 2 := by
    rw [hsumeq]
    have hc : (2 * ((S ∩ S').card : ℝ)) ≤ s := by exact_mod_cast hov
    have hge : (s : ℝ) ≤ 2 * s - 2 * ((S ∩ S').card : ℝ) := by linarith
    calc (1 : ℝ) = (s : ℝ)⁻¹ * s := by rw [inv_mul_cancel₀ (ne_of_gt hspos)]
      _ ≤ (s : ℝ)⁻¹ * (2 * s - 2 * ((S ∩ S').card : ℝ)) :=
          mul_le_mul_of_nonneg_left hge (le_of_lt (inv_pos.2 hspos))
  -- Conclude via `√`.
  rw [EuclideanSpace.norm_eq]
  calc (1 / 2 : ℝ) ≤ 1 := by norm_num
    _ = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (∑ i, ‖(sparseVec d s S - sparseVec d s S') i‖ ^ 2) :=
        Real.sqrt_le_sqrt hsum_ge

/-- **Gilbert–Varshamov packing of weight-`s` supports** (the combinatorial heart of Wainwright
Example 5.8, isolated as the single named residual). There is a family `𝒮` of `s`-element subsets of
`[d]`, pairwise with intersection `2|S ∩ S'| ≤ s` (equivalently symmetric difference `≥ s`), and
```
log |𝒮| ≥ (s/2) · log((d − s)/s).
```

Sketch: take a maximal `𝒮` among weight-`s` supports with pairwise `2|S ∩ S'| ≤ s`. By maximality
the "intersection balls" `{T : |T| = s, 2|S ∩ T| > s}` cover all `C(d,s)` supports, so
`C(d,s) ≤ |𝒮| · max_S #ball`; the binomial volume estimate
`#ball ≤ C(d,s) · ((d−s)/s)^{−s/2}` then yields the bound. (For `d ≤ 2s` the right side is `≤ 0`
and a singleton family suffices.)

TODO(mmx): discharge via the maximal-packing covering argument + the binomial volume estimate
(cf. `gilbert_varshamov` in `HammingPacking.lean` for the analogous `{0,1}^m` argument). -/
private theorem exists_bounded_overlap_supports (d s : ℕ) (hs : 0 < s) (hsd : s ≤ d) :
    ∃ 𝒮 : Finset (Finset (Fin d)),
      (∀ S ∈ 𝒮, S.card = s) ∧
      (∀ S ∈ 𝒮, ∀ S' ∈ 𝒮, S ≠ S' → 2 * (S ∩ S').card ≤ s) ∧
      (s / 2 : ℝ) * Real.log ((d - s : ℝ) / s) ≤ Real.log 𝒮.card :=
  sorry

-- USER-INPUT: `log |𝒮| ≥ (s/2) log((d−s)/s)` support-count bound; Wainwright Ex 5.8.
-- Supplied internally by `exists_bounded_overlap_supports` (named residual), not as a hypothesis.
/-- **Packing of sparse unit vectors**, construction form (Wainwright Example 5.8): the set of
`s`-sparse unit vectors in `ℝᵈ` contains a `1/2`-separated set `T` with
`log |T| ≥ (s/2) log((d−s)/s)`. -/
private theorem sparse_packing (d s : ℕ) (hs : 0 < s) (hsd : s ≤ d) :
    ∃ T : Finset (EuclideanSpace ℝ (Fin d)),
      (s / 2 : ℝ) * Real.log ((d - s : ℝ) / s) ≤ Real.log T.card ∧
      (∀ v ∈ T, ‖v‖ = 1 ∧ (Finset.univ.filter fun i => v i ≠ 0).card ≤ s) ∧
      ∀ u ∈ T, ∀ v ∈ T, u ≠ v → (1 / 2 : ℝ) ≤ ‖u - v‖ := by
  classical
  obtain ⟨𝒮, hcard, hov, hlog⟩ := exists_bounded_overlap_supports d s hs hsd
  -- The packing: image of the support family under the normalized-indicator map.
  refine ⟨𝒮.image (sparseVec d s), ?_, ?_, ?_⟩
  · -- Cardinality is preserved (the map is injective on `𝒮`), so the log bound transports.
    have hinj : Set.InjOn (sparseVec d s) 𝒮 := by
      intro S hS S' hS' heq
      by_contra hne
      have hsep := half_le_norm_sparseVec_sub d s hs S S' (hcard S hS) (hcard S' hS')
        (hov S hS S' hS' hne)
      rw [heq, sub_self, norm_zero] at hsep
      linarith
    rwa [Finset.card_image_of_injOn hinj]
  · -- Each image vector is a unit vector with exactly `s` nonzero coordinates.
    intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨S, hS, rfl⟩ := hv
    refine ⟨norm_sparseVec d s hs S (hcard S hS), ?_⟩
    have hane : (Real.sqrt s)⁻¹ ≠ 0 := by
      have : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.2 (by exact_mod_cast hs)
      positivity
    have hsupp : (Finset.univ.filter fun i => (sparseVec d s S) i ≠ 0) = S := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, sparseVec_apply]
      by_cases h : i ∈ S <;> simp [h, hane]
    rw [hsupp]; exact le_of_eq (hcard S hS)
  · -- Separation, transported from the support-overlap bound.
    intro u hu v hv huv
    rw [Finset.mem_image] at hu hv
    obtain ⟨S, hS, rfl⟩ := hu
    obtain ⟨S', hS', rfl⟩ := hv
    have hne : S ≠ S' := fun h => huv (by rw [h])
    exact half_le_norm_sparseVec_sub d s hs S S' (hcard S hS) (hcard S' hS') (hov S hS S' hS' hne)

/-- **Packing of sparse unit vectors** (Wainwright Example 5.8): the set of `s`-sparse unit
vectors in `ℝᵈ` contains a `1/2`-separated set `T` with `log |T| ≥ (s/2) log((d−s)/s)`; each
element is a unit vector with at most `s` nonzero coordinates, and any two are at Euclidean
distance `≥ 1/2`.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 5 (Metric entropy and its uses), Example 5.8. -/
theorem exists_sparse_packing (d s : ℕ) (hs : 0 < s) (hsd : s ≤ d) :
    ∃ T : Finset (EuclideanSpace ℝ (Fin d)),
      (s / 2 : ℝ) * Real.log ((d - s : ℝ) / s) ≤ Real.log T.card ∧
      (∀ v ∈ T, ‖v‖ = 1 ∧ (Finset.univ.filter fun i => v i ≠ 0).card ≤ s) ∧
      ∀ u ∈ T, ∀ v ∈ T, u ≠ v → (1 / 2 : ℝ) ≤ ‖u - v‖ :=
  sparse_packing d s hs hsd

end StatLean.Minimaxity
