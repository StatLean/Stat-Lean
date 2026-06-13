import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Order

/-!
# ℓ¹ and ℓ∞ vector norms on `EuclideanSpace ℝ (Fin d)`

Theorem-agnostic bricks (`ForMathlib` layer) used by the Lasso / OLS rate
proofs (Lu, *Big Data Analysis* ch.8): the ℓ¹ and ℓ∞ vector norms, the
Hölder pairing `|⟨x,y⟩| ≤ ‖x‖₁ ‖y‖∞`, the support-restriction operator
`x ↦ x|_S`, and the `√|S|`-bound `‖x|_S‖₁ ≤ √|S| · ‖x‖₂`.

Design choice: vectors live in `EuclideanSpace ℝ (Fin d)` (the ambient
ℓ²/inner-product space used everywhere else in the library). We do **not**
stack additional `PiLp p`/`WithLp p` instances on the same carrier — that
creates instance diamonds — and instead expose ℓ¹ / ℓ∞ as explicit functions
defined coordinate-wise via `x.ofLp`.

For `d = 0` the index set is empty: every quantity below collapses to `0`
(`Real.sSup_empty : sSup ∅ = 0`), and all inequalities hold trivially.
-/

namespace StatLean.HighDimensionalStatistics

open scoped InnerProductSpace
open Finset

variable {d : ℕ}

/-- ℓ¹ vector norm on `EuclideanSpace ℝ (Fin d)`: formalizes the textbook
`‖x‖₁ = ∑ᵢ |xᵢ|`. Defined as an explicit function (not a `PiLp 1`
instance) to avoid an instance diamond with the ambient ℓ² inner-product
structure. -/
def l1Norm (x : EuclideanSpace ℝ (Fin d)) : ℝ := ∑ i, |x.ofLp i|

/-- ℓ∞ vector norm on `EuclideanSpace ℝ (Fin d)`: formalizes the textbook
`‖x‖∞ = supᵢ |xᵢ|`. Defined via `iSup` over a finite index set so the
value is unconditionally a real number; the range `Set.range (fun i => |x.ofLp i|)`
is finite and hence `BddAbove`, so `iSup` agrees with the finite maximum
whenever `Fin d` is nonempty. For `d = 0` the value is
`sSup ∅ = 0` (Mathlib convention on ℝ). -/
noncomputable def linfNorm (x : EuclideanSpace ℝ (Fin d)) : ℝ := ⨆ i, |x.ofLp i|

@[simp] lemma l1Norm_nonneg (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ l1Norm x :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- Each coordinate is dominated by the ℓ∞ norm. -/
lemma abs_le_linfNorm (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    |x.ofLp i| ≤ linfNorm x :=
  le_ciSup (Set.finite_range _).bddAbove i

lemma linfNorm_nonneg (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ linfNorm x := by
  by_cases h : Nonempty (Fin d)
  · obtain ⟨i⟩ := h
    exact (abs_nonneg _).trans (abs_le_linfNorm x i)
  · rw [not_nonempty_iff] at h
    haveI : IsEmpty (Fin d) := h
    have heq : linfNorm x = 0 := by
      change sSup (Set.range (fun i : Fin d => |x.ofLp i|)) = 0
      rw [Set.range_eq_empty_iff.mpr ‹_›, Real.sSup_empty]
    linarith

/-- Hölder / ℓ¹–ℓ∞ duality (Lu-BDA ch.8): for `x y : EuclideanSpace ℝ (Fin d)`,
`|⟪x, y⟫_ℝ| ≤ ‖x‖₁ · ‖y‖∞`. -/
theorem abs_inner_le_l1Norm_mul_linfNorm (x y : EuclideanSpace ℝ (Fin d)) :
    |⟪x, y⟫_ℝ| ≤ l1Norm x * linfNorm y := by
  have hinner : (⟪x, y⟫_ℝ : ℝ) = ∑ i, x.ofLp i * y.ofLp i := by
    simp [PiLp.inner_apply, RCLike.inner_apply']
  rw [hinner]
  calc |∑ i, x.ofLp i * y.ofLp i|
      ≤ ∑ i, |x.ofLp i * y.ofLp i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |x.ofLp i| * |y.ofLp i| := by
        refine Finset.sum_congr rfl ?_
        intro i _; exact abs_mul _ _
    _ ≤ ∑ i, |x.ofLp i| * linfNorm y :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (abs_le_linfNorm y i) (abs_nonneg _)
    _ = (∑ i, |x.ofLp i|) * linfNorm y := by rw [← Finset.sum_mul]
    _ = l1Norm x * linfNorm y := rfl

/-- Coordinate form of the Hölder bound, often the more directly usable shape:
`|∑ᵢ xᵢ yᵢ| ≤ (∑ᵢ |xᵢ|) · supᵢ |yᵢ|`. -/
theorem abs_sum_mul_le_l1Norm_mul_linfNorm (x y : EuclideanSpace ℝ (Fin d)) :
    |∑ i, x.ofLp i * y.ofLp i| ≤ (∑ i, |x.ofLp i|) * ⨆ i, |y.ofLp i| := by
  have h := abs_inner_le_l1Norm_mul_linfNorm x y
  have hinner : (⟪x, y⟫_ℝ : ℝ) = ∑ i, x.ofLp i * y.ofLp i := by
    simp [PiLp.inner_apply, RCLike.inner_apply']
  rw [hinner] at h
  exact h

/-- Support-restriction operator: zero out coordinates outside `S`.
Used in Lasso / sparse-recovery analyses (Lu-BDA ch.8). -/
def restrict (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => if i ∈ S then x.ofLp i else 0)

@[simp] lemma restrict_ofLp_apply
    (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) (i : Fin d) :
    (restrict S x).ofLp i = if i ∈ S then x.ofLp i else 0 := by
  unfold restrict
  rw [WithLp.ofLp_toLp]

/-- `‖x|_S‖₂ ≤ ‖x‖₂`: the support restriction shrinks the ℓ² norm. -/
lemma norm_restrict_le_norm (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    ‖restrict S x‖ ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum ?_
  intro i _
  rw [restrict_ofLp_apply]
  split_ifs with h
  · exact le_refl _
  · simp [Real.norm_eq_abs, sq_nonneg]

/-- `‖x|_S‖₁ = ∑_{i ∈ S} |xᵢ|`. -/
lemma l1Norm_restrict_eq_sum (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    l1Norm (restrict S x) = ∑ i ∈ S, |x.ofLp i| := by
  unfold l1Norm
  have h1 : ∀ i, |(restrict S x).ofLp i| = if i ∈ S then |x.ofLp i| else 0 := by
    intro i
    rw [restrict_ofLp_apply]
    split_ifs <;> simp
  simp_rw [h1]
  exact Fintype.sum_ite_mem S _

/-- √s ℓ¹–ℓ² bound on the support (Lu-BDA ch.8):
`‖x|_S‖₁ ≤ √|S| · ‖x‖₂`. Proof: Cauchy–Schwarz with the all-ones vector on `S`
gives `(∑_{i∈S} |xᵢ|)² ≤ |S| · ∑_{i∈S} xᵢ²`; taking square roots and bounding
`∑_{i∈S} xᵢ² ≤ ∑ᵢ xᵢ² = ‖x‖²` yields the claim. The Mathlib brick is
`Finset.sum_mul_sq_le_sq_mul_sq` (polynomial Cauchy–Schwarz over a finset). -/
theorem l1Norm_restrict_le_sqrt_card_mul_norm
    (S : Finset (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    l1Norm (restrict S x) ≤ Real.sqrt (S.card : ℝ) * ‖x‖ := by
  rw [l1Norm_restrict_eq_sum]
  set f : Fin d → ℝ := fun i => x.ofLp i with hf
  -- Cauchy–Schwarz applied to (1, |f|) on `S`:
  have hCS :
      (∑ i ∈ S, |f i|) ^ 2 ≤ (S.card : ℝ) * (∑ i ∈ S, (f i) ^ 2) := by
    have key := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun i => |f i|)
    -- LHS: (∑ i ∈ S, 1 * |f i|)² = (∑ i ∈ S, |f i|)²
    -- RHS: (∑ i ∈ S, 1²) * (∑ i ∈ S, |f i|²) = |S| * ∑ i ∈ S, (f i)²
    simp only [one_mul, one_pow, Finset.sum_const, Nat.smul_one_eq_cast, sq_abs] at key
    exact key
  -- Nonnegativity prerequisites for taking square roots.
  have h_sum_abs_nonneg : 0 ≤ ∑ i ∈ S, |f i| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h_card_nonneg : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
  have h_sum_sq_nonneg : 0 ≤ ∑ i ∈ S, (f i) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  -- Take √ of `hCS` and rewrite both sides.
  have h1 : ∑ i ∈ S, |f i| ≤
      Real.sqrt ((S.card : ℝ) * (∑ i ∈ S, (f i) ^ 2)) := by
    have := Real.sqrt_le_sqrt hCS
    rwa [Real.sqrt_sq h_sum_abs_nonneg] at this
  rw [Real.sqrt_mul h_card_nonneg] at h1
  -- Bound `∑_{i∈S} (f i)² ≤ ∑ᵢ (f i)² = ‖x‖²`, then take √ and combine.
  have h_sub : ∑ i ∈ S, (f i) ^ 2 ≤ ∑ i, (f i) ^ 2 :=
    Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
  have h_normsq : ‖x‖ = Real.sqrt (∑ i, (f i) ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro i _
    simp [hf, Real.norm_eq_abs, sq_abs]
  refine h1.trans ?_
  rw [h_normsq]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h_sub) (Real.sqrt_nonneg _)

end StatLean.HighDimensionalStatistics
