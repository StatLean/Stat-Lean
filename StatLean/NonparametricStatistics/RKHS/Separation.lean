import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Linear separation of labeled data in a real Hilbert space

Binary classification background for the maximal margin classifier: labeled data
`(x i, λ i)` with `λ i ∈ {±1}` is **linearly separated** by the affine hyperplane
`{y | ⟪y, v⟫ = c}` when every point lies strictly on its label's side, i.e.
`0 < λ i · (⟪x i, v⟫ − c)`.  We prove:

* the distance of a point to the hyperplane is `|⟪p, v⟫ − c| / ‖v‖`;
* a separating normal vector can always be replaced by its orthogonal projection onto
  the span of the data, without changing any of the constraint values.

**Bibliographic comments.** The geometry of separating hyperplanes for classification
goes back to R. A. Fisher (1936) and F. Rosenblatt's perceptron (1958); the Hilbert-space
formulation is standard in statistical learning theory, cf. V. N. Vapnik, *The Nature of
Statistical Learning Theory* (Springer, 1995).
-/

open scoped RealInnerProductSpace

namespace StatLean.NonparametricStatistics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable (v : E) (c : ℝ) in
/-- The affine hyperplane `{y | ⟪y, v⟫ = c}` with normal vector `v` and offset `c`. -/
def hyperplane : Set E := {y : E | ⟪y, v⟫ = c}

/-- `(v, c)` **separates** the labeled data `(x, lab)`: every point lies strictly on the
side of the hyperplane prescribed by its `±1` label. -/
def SeparatesData {ι : Type*} (v : E) (c : ℝ) (x : ι → E) (lab : ι → ℝ) : Prop :=
  ∀ i, 0 < lab i * (⟪x i, v⟫ - c)

/-- Labeled data is **linearly separable** if some affine hyperplane separates it. -/
def LinearlySeparable {ι : Type*} (x : ι → E) (lab : ι → ℝ) : Prop :=
  ∃ (v : E) (c : ℝ), SeparatesData v c x lab

/-- A separating normal vector is necessarily nonzero (given at least one data point). -/
theorem SeparatesData.ne_zero {ι : Type*} [Nonempty ι] {v : E} {c : ℝ} {x : ι → E}
    {lab : ι → ℝ} (h : SeparatesData v c x lab) : v ≠ 0 := by
  sorry

/-- **Distance to an affine hyperplane**: for `v ≠ 0`,
`d(p, {⟪·, v⟫ = c}) = |⟪p, v⟫ − c| / ‖v‖`. -/
theorem infDist_hyperplane [CompleteSpace E] (p : E) {v : E}
    -- LEAN-ONLY: nondegenerate normal vector; for `v = 0` the "hyperplane" is `∅` or `E`
    (hv : v ≠ 0) (c : ℝ) :
    Metric.infDist p (hyperplane v c) = |⟪p, v⟫ - c| / ‖v‖ := by
  sorry

/-- Inner products against members of a subspace see only the subspace component of the
other vector: `⟪m, P_M v⟫ = ⟪m, v⟫` for `m ∈ M`. -/
theorem inner_starProjection_of_mem {M : Submodule ℝ E} [M.HasOrthogonalProjection]
    {m : E} (hm : m ∈ M) (v : E) :
    ⟪m, M.starProjection v⟫ = ⟪m, v⟫ := by
  sorry

/-- **The separating normal can be chosen in the span of the data**: projecting `v` onto
any closed subspace containing the data preserves all constraint values, hence preserves
separation. -/
theorem SeparatesData.starProjection {ι : Type*} {v : E} {c : ℝ} {x : ι → E}
    {lab : ι → ℝ} {M : Submodule ℝ E} [M.HasOrthogonalProjection]
    -- LEAN-ONLY: the subspace contains the data; instantiated with the closed span
    (hxM : ∀ i, x i ∈ M)
    (h : SeparatesData v c x lab) :
    SeparatesData (M.starProjection v) c x lab := by
  sorry

end StatLean.NonparametricStatistics
