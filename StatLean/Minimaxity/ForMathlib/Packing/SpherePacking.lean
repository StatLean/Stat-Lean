import StatLean.Minimaxity.ForMathlib.Packing.HammingPacking
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Packing of the Euclidean unit sphere (Wainwright Example 5.8)

A Chapter-5 metric-entropy prerequisite for the PCA minimax lower bound (Example 15.19): the unit
sphere of `ℝⁿ` admits a `1/2`-separated set of exponentially large cardinality. Wainwright's
statement is
```
log M(1/2; 𝕊ⁿ⁻¹, ‖·‖₂) ≥ n · log 2                    (Example 5.8)
```
i.e. a set `T` of unit vectors, pairwise at Euclidean distance `≥ 1/2`, with `log |T| ≥ n·log 2`.

**Constant deviation (documented per CLAUDE.md §1).** We prove the *exponential* bound
`log |T| ≥ n/10` instead of the book's `n·log 2` (`log 2 ≈ 0.693`). The looser base is harmless:
the PCA Fano argument (Example 15.19) only needs a packing of cardinality `2^{Ω(n)}`, and
`e^{n/10}` is exponential in `n`. The slack comes from routing the construction through the
Gilbert–Varshamov binary code (`exists_hamming_packing`, whose own constant `m/10` is a provable
Chernoff slack below the true binary entropy) rather than a sharp spherical-cap surface bound.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 5 (Metric entropy and its uses), Example 5.8
(used in Chapter 15, §15.3.4, Example 15.19).

## Proof architecture

The sphere packing is the image of a Gilbert–Varshamov **binary code** under the sign embedding
```
v α := (i ↦ (±1)/√n) ,  with sign `+` iff `α i = true`   (α : Fin n → Bool),
```
which lands every codeword on the unit sphere (each entry squared is `1/n`, summing to `1`). For two
codewords the difference has entry `±2/√n` exactly on the Hamming-disagreement coordinates and `0`
elsewhere, so
```
‖v α − v β‖² = hammingDist α β · (4/n) ≥ (n/4)·(4/n) = 1,
```
using the code's pairwise Hamming separation `≥ n/4`. Hence the images are unit vectors that are
pairwise `≥ 1`-separated (a fortiori `≥ 1/2`); distinctness of the `≥ 1`-separated images makes the
embedding injective, so `|image| = |code|` and the code's count `log |code| ≥ n/10` transports. The
entire geometric content is local (per-coordinate), and the combinatorial count is the single
imported brick `exists_hamming_packing` (`HammingPacking.lean`) — no measure theory.
-/

open scoped ENNReal
open Finset

namespace StatLean.Minimaxity

/-- The **sign embedding** `v α ∈ ℝⁿ` of a binary codeword `α : Fin n → Bool`: entry `+1/√n` where
`α i = true`, entry `−1/√n` where `α i = false`. For `n > 0` this is a unit vector, and the Hamming
distance between two codewords controls the Euclidean distance between their images.

Formalizes the packing element of Wainwright Example 5.8 (via the Gilbert–Varshamov code). The
degenerate input `n = 0` is harmless: the vector lives in the trivial space and the downstream
lemmas carry `0 < n`. -/
private noncomputable def sphereVec (n : ℕ) (α : Fin n → Bool) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => (if α i then (1 : ℝ) else -1) / Real.sqrt n)

private theorem sphereVec_apply (n : ℕ) (α : Fin n → Bool) (i : Fin n) :
    (sphereVec n α) i = (if α i then (1 : ℝ) else -1) / Real.sqrt n := rfl

/-- Each sign-embedded codeword is a unit vector (`n > 0`): every entry squared is `1/n`, and there
are `n` of them. -/
private theorem norm_sphereVec (n : ℕ) (hn : 0 < n) (α : Fin n → Bool) :
    ‖sphereVec n α‖ = 1 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [EuclideanSpace.norm_eq]
  have hsq : ∀ i, ‖(sphereVec n α) i‖ ^ 2 = (n : ℝ)⁻¹ := by
    intro i
    rw [sphereVec_apply, Real.norm_eq_abs, sq_abs, div_pow, Real.sq_sqrt hnpos.le]
    cases hi : α i <;> simp [one_div]
  rw [Finset.sum_congr rfl (fun i _ => hsq i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_inv_cancel₀ (ne_of_gt hnpos), Real.sqrt_one]

/-- Two sign-embedded codewords at Hamming distance `≥ n/4` are `≥ 1/2`-separated (in fact
`≥ 1`-separated): the difference is `±2/√n` exactly on the disagreement coordinates, so
`‖v α − v β‖² = (hammingDist α β)·(4/n) ≥ 1`. -/
private theorem norm_sphereVec_sub (n : ℕ) (hn : 0 < n) (α β : Fin n → Bool)
    (hd : (n / 4 : ℝ) ≤ (hammingDist α β : ℝ)) :
    (1 / 2 : ℝ) ≤ ‖sphereVec n α - sphereVec n β‖ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hs2 : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
  -- Per-coordinate: the squared entry is `4/n` on disagreement coordinates, `0` elsewhere.
  have happ : ∀ i, ‖(sphereVec n α - sphereVec n β) i‖ ^ 2
      = (if α i ≠ β i then (4 : ℝ) else 0) * (n : ℝ)⁻¹ := by
    intro i
    rw [PiLp.sub_apply, sphereVec_apply, sphereVec_apply, Real.norm_eq_abs, sq_abs,
      div_sub_div_same, div_pow, hs2]
    cases α i <;> cases β i <;> simp [div_eq_mul_inv] <;> norm_num
  -- Count the disagreement coordinates: `∑ (if α i ≠ β i then 4 else 0) = 4 · hammingDist α β`.
  have hsumcount : ∑ i : Fin n, (if α i ≠ β i then (4 : ℝ) else 0) = 4 * (hammingDist α β : ℝ) := by
    have hcard : (hammingDist α β : ℝ) = ∑ i : Fin n, (if α i ≠ β i then (1 : ℝ) else 0) := by
      simp only [hammingDist, Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
        Nat.cast_zero]
    rw [hcard, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split <;> norm_num
  -- Sum the squared entries.
  have hsum : ∑ i, ‖(sphereVec n α - sphereVec n β) i‖ ^ 2
      = (4 * (hammingDist α β : ℝ)) * (n : ℝ)⁻¹ := by
    rw [Finset.sum_congr rfl (fun i _ => happ i), ← Finset.sum_mul, hsumcount]
  -- The squared norm is `≥ 1`.
  have hge1 : (1 : ℝ) ≤ ∑ i, ‖(sphereVec n α - sphereVec n β) i‖ ^ 2 := by
    rw [hsum]
    have hd4 : (n : ℝ) ≤ 4 * (hammingDist α β : ℝ) := by linarith
    calc (1 : ℝ) = (n : ℝ) * (n : ℝ)⁻¹ := (mul_inv_cancel₀ (ne_of_gt hnpos)).symm
      _ ≤ (4 * (hammingDist α β : ℝ)) * (n : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right hd4 (le_of_lt (inv_pos.2 hnpos))
  -- Conclude via `√`.
  rw [EuclideanSpace.norm_eq]
  calc (1 / 2 : ℝ) ≤ 1 := by norm_num
    _ = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (∑ i, ‖(sphereVec n α - sphereVec n β) i‖ ^ 2) := Real.sqrt_le_sqrt hge1

-- USER-INPUT: `log |code| ≥ n/10` Gilbert–Varshamov binary-code count; Wainwright Ex 5.3.
-- Supplied internally by `exists_hamming_packing` (a fully proved theorem), not as a hypothesis.
/-- **Packing of the Euclidean unit sphere**, cardinality form (Wainwright Example 5.8, loose
constant): for `n ≥ 1` there is a finite set `T` of unit vectors of `ℝⁿ`, pairwise
`≥ 1/2`-separated, with `log |T| ≥ n/10`. (Book constant `n·log 2` replaced by the provable
exponential `n/10`; see the module docstring.) -/
private theorem sphere_packing_card (n : ℕ) (hn : 0 < n) :
    ∃ T : Finset (EuclideanSpace ℝ (Fin n)),
      (n / 10 : ℝ) ≤ Real.log T.card ∧
      (∀ v ∈ T, ‖v‖ = 1) ∧
      ∀ u ∈ T, ∀ v ∈ T, u ≠ v → (1 / 2 : ℝ) ≤ ‖u - v‖ := by
  classical
  obtain ⟨C, hlog, hsep⟩ := exists_hamming_packing n
  -- The packing: image of the binary code under the sign embedding.
  refine ⟨C.image (sphereVec n), ?_, ?_, ?_⟩
  · -- Cardinality is preserved (the embedding is injective on `C`), so the count transports.
    have hinj : Set.InjOn (sphereVec n) C := by
      intro α hα β hβ heq
      by_contra hne
      have h := norm_sphereVec_sub n hn α β (hsep α hα β hβ hne)
      rw [heq, sub_self, norm_zero] at h
      linarith
    rwa [Finset.card_image_of_injOn hinj]
  · -- Each image vector is a unit vector.
    intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨α, hα, rfl⟩ := hv
    exact norm_sphereVec n hn α
  · -- Separation, transported from the Hamming separation of the code.
    intro u hu v hv huv
    rw [Finset.mem_image] at hu hv
    obtain ⟨α, hα, rfl⟩ := hu
    obtain ⟨β, hβ, rfl⟩ := hv
    have hne : α ≠ β := fun h => huv (by rw [h])
    exact norm_sphereVec_sub n hn α β (hsep α hα β hβ hne)

/-- **Packing of the Euclidean unit sphere** (Wainwright Example 5.8): the unit sphere of `ℝⁿ`
contains a `1/2`-separated set `T` (pairwise Euclidean distance `≥ 1/2`) of unit vectors with
`log |T| ≥ n/10`.

**Constant deviation.** The book states `log |T| ≥ n · log 2`; we prove the looser but still
exponential `log |T| ≥ n/10` (`1/10 < log 2`), inherited from the Gilbert–Varshamov code
(`exists_hamming_packing`). This is all the PCA Fano lower bound (Example 15.19) requires. See the
module docstring.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 5 (Metric entropy and its uses), Example 5.8. -/
theorem exists_sphere_packing (n : ℕ) :
    ∃ T : Finset (EuclideanSpace ℝ (Fin n)),
      (n / 10 : ℝ) ≤ Real.log T.card ∧
      (∀ v ∈ T, ‖v‖ = 1) ∧
      ∀ u ∈ T, ∀ v ∈ T, u ≠ v → (1 / 2 : ℝ) ≤ ‖u - v‖ := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- `n = 0`: no unit vectors exist, but the bound is `0 ≤ log 0 = 0`, so the empty set works.
    subst hn
    refine ⟨∅, ?_, ?_, ?_⟩
    · simp
    · intro v hv; simp at hv
    · intro u hu; simp at hu
  · exact sphere_packing_card n hn

end StatLean.Minimaxity
