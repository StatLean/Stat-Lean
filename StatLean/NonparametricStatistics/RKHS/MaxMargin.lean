import StatLean.NonparametricStatistics.RKHS.Separation

/-!
# The maximal margin classifier

For finite linearly separable labeled data `(x i, λ i)`, `i : Fin n`, `λ i ∈ {±1}`, the
**maximal margin hyperplane** is the separating hyperplane maximizing the least distance
of the data to the hyperplane.  Normalizing the constraints to
`λ i · (⟪x i, v⟫ − c) ≥ 1`, the margin is `1/‖v‖`, so the problem becomes: minimize
`‖v‖` over the feasible set

`marginFeasible x lab = {v | ∃ c, ∀ i, 1 ≤ λ i · (⟪x i, v⟫ − c)}`.

We prove the feasible set is closed and convex, nonempty when the data is separable
(finiteness allows rescaling the strict inequalities to `≥ 1`), that a unique minimum
norm solution `w` exists (Hilbert projection theorem), that `w` lies in the span of the
data, and that the associated hyperplane maximizes the minimal margin among all
separating hyperplanes.

**Bibliographic comments.** The optimal (maximal-margin) hyperplane is due to
V. N. Vapnik and A. Ya. Chervonenkis (1964, 1974) and B. E. Boser, I. M. Guyon and
V. N. Vapnik, COLT (1992); uniqueness via strict convexity of the norm is classical.
-/

open scoped RealInnerProductSpace

namespace StatLean.NonparametricStatistics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ}

/-- The **normalized feasible set** of the maximal margin problem: normal vectors `v`
admitting an offset `c` with all data constraints `λ i (⟪x i, v⟫ − c) ≥ 1`. -/
def marginFeasible (x : Fin n → E) (lab : Fin n → ℝ) : Set E :=
  {v : E | ∃ c : ℝ, ∀ i, 1 ≤ lab i * (⟪x i, v⟫ - c)}

/-- The margin of a hyperplane on the data: the least distance from a data point to the
hyperplane. -/
noncomputable def dataMargin (x : Fin n → E) (v : E) (c : ℝ) : ℝ :=
  ⨅ i, Metric.infDist (x i) (hyperplane v c)

/-- **Maximal margin hyperplane**: a separating hyperplane whose margin dominates the
margin of every separating hyperplane. -/
def IsMaxMarginHyperplane (v : E) (c : ℝ) (x : Fin n → E) (lab : Fin n → ℝ) : Prop :=
  SeparatesData v c x lab ∧
    ∀ (v' : E) (c' : ℝ), SeparatesData v' c' x lab →
      dataMargin x v' c' ≤ dataMargin x v c

/-- The feasible set is convex. -/
theorem convex_marginFeasible (x : Fin n → E) (lab : Fin n → ℝ) :
    Convex ℝ (marginFeasible x lab) := by
  rintro v₁ ⟨c₁, h₁⟩ v₂ ⟨c₂, h₂⟩ s t hs ht hst
  refine ⟨s * c₁ + t * c₂, fun i => ?_⟩
  have e : ⟪x i, s • v₁ + t • v₂⟫ = s * ⟪x i, v₁⟫ + t * ⟪x i, v₂⟫ := by
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left (h₁ i) hs, mul_le_mul_of_nonneg_left (h₂ i) ht]

/-- The feasible set is closed. -/
theorem isClosed_marginFeasible (x : Fin n → E) (lab : Fin n → ℝ) :
    IsClosed (marginFeasible x lab) := by
  sorry

/-- Separable finite data has nonempty feasible set: the finitely many strict constraints
can be rescaled to clear the threshold `1`. -/
theorem marginFeasible_nonempty {x : Fin n → E} {lab : Fin n → ℝ}
    -- USER-INPUT: the data is linearly separable
    (hsep : LinearlySeparable x lab) :
    (marginFeasible x lab).Nonempty := by
  obtain ⟨v, c, h⟩ := hsep
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact ⟨0, 0, fun i => i.elim0⟩
  · have hne : (Finset.univ : Finset (Fin n)).Nonempty :=
      Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hn)
    set δ := Finset.univ.inf' hne (fun i => lab i * (⟪x i, v⟫ - c)) with hδ
    have hδpos : 0 < δ := by
      rw [hδ, Finset.lt_inf'_iff]
      exact fun i _ => h i
    refine ⟨δ⁻¹ • v, δ⁻¹ * c, fun i => ?_⟩
    have hle : δ ≤ lab i * (⟪x i, v⟫ - c) := Finset.inf'_le _ (Finset.mem_univ i)
    rw [real_inner_smul_right]
    have hrw : lab i * (δ⁻¹ * ⟪x i, v⟫ - δ⁻¹ * c)
        = δ⁻¹ * (lab i * (⟪x i, v⟫ - c)) := by ring
    rw [hrw]
    calc (1 : ℝ) = δ⁻¹ * δ := by field_simp
      _ ≤ δ⁻¹ * (lab i * (⟪x i, v⟫ - c)) :=
          mul_le_mul_of_nonneg_left hle (le_of_lt (inv_pos.mpr hδpos))

/-- **Existence and uniqueness of the maximal margin normal vector**: the feasible set of
separable data contains a unique element of minimal norm. -/
theorem existsUnique_min_norm_marginFeasible [CompleteSpace E] {x : Fin n → E}
    {lab : Fin n → ℝ}
    -- USER-INPUT: the data is linearly separable
    (hsep : LinearlySeparable x lab) :
    ∃! w : E, w ∈ marginFeasible x lab ∧
      ∀ v ∈ marginFeasible x lab, ‖w‖ ≤ ‖v‖ := by
  sorry

/-- The minimal-norm feasible vector lies in the span of the data. -/
theorem min_norm_marginFeasible_mem_span [CompleteSpace E] {x : Fin n → E}
    {lab : Fin n → ℝ} {w : E}
    (hw : w ∈ marginFeasible x lab)
    (hmin : ∀ v ∈ marginFeasible x lab, ‖w‖ ≤ ‖v‖) :
    w ∈ Submodule.span ℝ (Set.range x) := by
  sorry

/-- **The minimal-norm solution is a maximal margin hyperplane**: an offset `c` for the
minimal-norm feasible `w` realizes the maximal margin among all separating hyperplanes,
with margin `1/‖w‖`. -/
theorem isMaxMarginHyperplane_of_min_norm [CompleteSpace E] {x : Fin n → E}
    {lab : Fin n → ℝ} {w : E}
    -- LEAN-ONLY: at least one data point; the margin is an infimum over the data
    (hn : 0 < n)
    -- USER-INPUT: binary `±1` labels
    (hlab : ∀ i, lab i = 1 ∨ lab i = -1)
    (hw : w ∈ marginFeasible x lab)
    (hmin : ∀ v ∈ marginFeasible x lab, ‖w‖ ≤ ‖v‖) :
    ∃ c : ℝ, (∀ i, 1 ≤ lab i * (⟪x i, w⟫ - c)) ∧
      IsMaxMarginHyperplane w c x lab := by
  sorry

/-- Quadratic-form reduction: for `v = ∑ αⱼ x ⱼ` in the span of the data, the objective
`‖v‖²` is the Gram quadratic form `∑ᵢⱼ αᵢ αⱼ ⟪x ⱼ, x ᵢ⟫` — the optimization only needs
the pairwise inner products of the data. -/
theorem norm_sq_eq_gram_quadForm (x : Fin n → E) (α : Fin n → ℝ) :
    ‖∑ j, α j • x j‖ ^ 2 = ∑ i, ∑ j, α i * α j * ⟪x j, x i⟫ := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_right, real_inner_comm]
  ring

end StatLean.NonparametricStatistics
