/-
Copyright (c) 2026 Junwei Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Convex.Measure
import Mathlib.Topology.MetricSpace.Thickening

/-!
# The Gaussian boundary-shell bound for convex sets

For the standard Gaussian `γ = N(0, I_k)` on `EuclideanSpace ℝ (Fin k)` and a convex set `B`,
the mass of the `ε`-boundary shell of `B` is `O_k(ε)`:

`γ(Bᵋ) ≤ γ(B) + C_k ε`  and  `γ(B) ≤ γ(B_{-ε}) + C_k ε`,

where `Bᵋ` is the `ε`-thickening and `B_{-ε}` the `ε`-erosion. This is the missing ingredient of
the elementary convex Berry–Esseen bound
`StatLean.HypothesisTesting.berryEsseen_convex_elementary`, where the *sharp* form of the constant
(K. Ball's `4 k^{1/4}` bound on the Gaussian surface area of a convex body) is what produces the
dimension factor `k^{1/4}` of Bentkus (2003). The elementary assembly only needs *finiteness* of
`C_k` at fixed `k`, and that is what is proved here, with the explicit constant
`C_k = 8 k^{3/2}/√(2π)` (`gaussianShellConst`).

## The argument

Everything rests on one elementary observation about convex sets and *coordinate lines*.

* (Support) If `V` is convex and `x ∉ interior V` then some `u ≠ 0` supports `V` at `x`:
  `⟪u, w - x⟫ ≤ 0` for all `w ∈ V` (`exists_inner_le_zero_of_notMem_interior`). For
  `interior V ≠ ∅` this is `geometric_hahn_banach_open_point` applied to `interior V`, extended to
  `closure (interior V) = closure V ⊇ V`; for `interior V = ∅` the affine span of `V` is a proper
  affine subspace and `u` is taken orthogonal to its direction.
* (Escape) Some coordinate of a unit vector is at least `1/√k` in absolute value, so moving from
  `x` by `± c` along that coordinate axis moves *away* from the supporting hyperplane by at least
  `c/√k`; hence `infDist (x ± c • eᵢ) V ≥ c/√k` (`infDist_add_smul_single_ge`).
* (Slice) For a convex `V` and a coordinate `i`, the set `{x ∈ V : x + c • eᵢ ∉ V}` meets every
  line parallel to `eᵢ` in a set of diameter `≤ |c|` — because the trace of `V` on such a line is
  an interval. Its Gaussian mass is therefore at most `2|c|/√(2π)`, by Fubini for
  `γ = ⨂ N(0,1)` (`map_pi_eq_stdGaussian`) and the `1/√(2π)` bound on the one-dimensional
  Gaussian density (`gaussian_mem_notMem_shift_le`). This step is where the Gaussian enters; note
  that the bound is *dimension-free*, the factor `k^{3/2}` coming only from the `2k` coordinate
  directions and the `√k` loss in the escape step.

Combining: the shell `Bᵋ \ B` (resp. `B \ B_{-ε}`) is covered by the `2k` sets
`{x ∈ Bᵋ : x ± c • eᵢ ∉ Bᵋ}` with `c = 2ε√k`, giving `γ(shell) ≤ 2k · 2c/√(2π) = C_k ε`.

The same covering with `c → 0` shows `γ(V \ interior V) = 0` for every convex `V`
(`gaussian_diff_interior_eq_zero`), which is the degenerate case (`interior B = ∅`, i.e. `B` inside
a hyperplane) of the erosion bound.
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped InnerProductSpace ENNReal NNReal Real

namespace StatLean.HypothesisTesting

section GaussianShell

variable {k : ℕ}

/-! ### One-dimensional density bounds -/

/-- The standard normal law is dominated by `(2π)^{-1/2}` times Lebesgue measure: its density is
bounded by the peak value `(2π)^{-1/2}`. -/
lemma gaussianReal_le_smul_volume (A : Set ℝ) :
    gaussianReal 0 1 A ≤ ENNReal.ofReal (Real.sqrt (2 * π))⁻¹ * volume A := by
  have hbound : ∀ x : ℝ, gaussianPDFReal 0 1 x ≤ (Real.sqrt (2 * π))⁻¹ := by
    intro x
    have hexp : Real.exp (-(x - 0) ^ 2 / (2 * 1)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg (x - 0)]
    have hpos : (0 : ℝ) ≤ (Real.sqrt (2 * π * 1))⁻¹ := by positivity
    calc gaussianPDFReal 0 1 x
        = (Real.sqrt (2 * π * 1))⁻¹ * Real.exp (-(x - 0) ^ 2 / (2 * 1)) := rfl
      _ ≤ (Real.sqrt (2 * π * 1))⁻¹ * 1 := mul_le_mul_of_nonneg_left hexp hpos
      _ = (Real.sqrt (2 * π))⁻¹ := by norm_num
  rw [gaussianReal_apply 0 one_ne_zero A]
  calc ∫⁻ x in A, gaussianPDF 0 1 x
      ≤ ∫⁻ _ in A, ENNReal.ofReal (Real.sqrt (2 * π))⁻¹ := by
        refine lintegral_mono fun x => ?_
        exact ENNReal.ofReal_le_ofReal (hbound x)
    _ = ENNReal.ofReal (Real.sqrt (2 * π))⁻¹ * volume A := by
        rw [setLIntegral_const]

/-- A set of diameter at most `c` has standard normal mass at most `2c/√(2π)`. -/
lemma gaussianReal_le_of_diam_le {A : Set ℝ} {c : ℝ}
    (h : ∀ s ∈ A, ∀ t ∈ A, |s - t| ≤ c) :
    gaussianReal 0 1 A ≤ ENNReal.ofReal (2 * c / Real.sqrt (2 * π)) := by
  rcases A.eq_empty_or_nonempty with rfl | ⟨t₀, ht₀⟩
  · simp
  · have hsub : A ⊆ Set.Icc (t₀ - c) (t₀ + c) := by
      intro s hs
      have := h s hs t₀ ht₀
      rw [abs_le] at this
      exact ⟨by linarith [this.1], by linarith [this.2]⟩
    calc gaussianReal 0 1 A
        ≤ ENNReal.ofReal (Real.sqrt (2 * π))⁻¹ * volume A := gaussianReal_le_smul_volume A
      _ ≤ ENNReal.ofReal (Real.sqrt (2 * π))⁻¹ * volume (Set.Icc (t₀ - c) (t₀ + c)) := by
          gcongr
      _ = ENNReal.ofReal (2 * c / Real.sqrt (2 * π)) := by
          rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          have : t₀ + c - (t₀ - c) = 2 * c := by ring
          rw [this]
          field_simp

/-! ### The Gaussian as a product measure -/

/-- `N(0, I_k)` is the pushforward of the `k`-fold product of `N(0,1)` under the (identity)
`toLp` map. This is `map_pi_eq_stdGaussian` combined with `multivariateGaussian_zero_one`. -/
lemma multivariateGaussian_eq_map_pi (k : ℕ) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1
      = (Measure.pi fun _ : Fin k => gaussianReal 0 1).map (WithLp.toLp 2) := by
  rw [multivariateGaussian_zero_one, ← map_pi_eq_stdGaussian]

/-! ### The coordinate-slice bound

The Gaussian input of the whole file: for convex `V` and a coordinate direction `eᵢ`, the set of
points of `V` that leave `V` after a shift by `c • eᵢ` has Gaussian mass at most `2|c|/√(2π)`,
with **no dimension factor**. Its trace on each line parallel to `eᵢ` has diameter `≤ |c|`
because the trace of `V` on that line is an interval; Fubini for the product form of `N(0, I_k)`
then costs nothing. -/

/-- If `J ⊆ ℝ` is convex then the set of points of `J` whose `c`-shift leaves `J` has diameter at
most `|c|`: two such points further apart would have the shift of one of them strictly between
them, hence inside `J`. -/
private lemma diam_shift_le_of_convex {J : Set ℝ} (hJ : Convex ℝ J) (c : ℝ) :
    ∀ s ∈ {t | t ∈ J ∧ t + c ∉ J}, ∀ t ∈ {t | t ∈ J ∧ t + c ∉ J}, |s - t| ≤ |c| := by
  have hoc : J.OrdConnected := convex_iff_ordConnected.mp hJ
  have key : ∀ s ∈ {t | t ∈ J ∧ t + c ∉ J}, ∀ t ∈ {t | t ∈ J ∧ t + c ∉ J},
      s ≤ t → t - s ≤ |c| := by
    intro s hs t ht hst
    by_contra hcon
    rw [not_le] at hcon
    rcases le_or_gt 0 c with hc | hc
    · rw [abs_of_nonneg hc] at hcon
      exact hs.2 (hoc.out hs.1 ht.1 ⟨by linarith, by linarith⟩)
    · rw [abs_of_neg hc] at hcon
      exact ht.2 (hoc.out hs.1 ht.1 ⟨by linarith, by linarith⟩)
  intro s hs t ht
  rcases le_total s t with h | h
  · rw [abs_sub_comm, abs_of_nonneg (by linarith : (0:ℝ) ≤ t - s)]
    exact key s hs t ht h
  · rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ s - t)]
    exact key t ht s hs h

/-- Inserting an affine combination in the `i`-th slot is the affine combination of the
insertions: `t ↦ i.insertNth t y` is an affine map `ℝ → (Fin (m+1) → ℝ)`. -/
private lemma insertNth_affine {m : ℕ} (i : Fin (m + 1)) (y : Fin m → ℝ) {a b s r : ℝ}
    (hsr : s + r = 1) :
    Fin.insertNth (α := fun _ => ℝ) i (s * a + r * b) y
      = s • Fin.insertNth (α := fun _ => ℝ) i a y
        + r • Fin.insertNth (α := fun _ => ℝ) i b y := by
  refine funext ((Fin.forall_iff_succAbove i).2 ⟨by simp, fun j => ?_⟩)
  simp only [Fin.insertNth_apply_succAbove, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (-(y j)) * hsr

/-- Shifting the inserted coordinate by `c` is adding `c • Pi.single i 1`. -/
private lemma insertNth_add_single {m : ℕ} (i : Fin (m + 1)) (y : Fin m → ℝ) (t c : ℝ) :
    Fin.insertNth (α := fun _ => ℝ) i (t + c) y
      = Fin.insertNth (α := fun _ => ℝ) i t y
        + c • (Pi.single i (1 : ℝ) : Fin (m + 1) → ℝ) := by
  refine funext ((Fin.forall_iff_succAbove i).2 ⟨by simp, fun j => ?_⟩)
  simp [Fin.insertNth_apply_succAbove]

/-- **Coordinate-slice anti-concentration.** For a convex measurable `V` and a coordinate `i`,
the standard Gaussian mass of `{x ∈ V : x + c • eᵢ ∉ V}` is at most `2|c|/√(2π)`. The constant is
dimension-free. -/
lemma gaussian_mem_notMem_shift_le (hk : 0 < k) (i : Fin k) (c : ℝ)
    {V : Set (EuclideanSpace ℝ (Fin k))} (hVm : MeasurableSet V) (hVc : Convex ℝ V) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1
        {x | x ∈ V ∧ x + c • EuclideanSpace.single i (1 : ℝ) ∉ V}
      ≤ ENNReal.ofReal (2 * |c| / Real.sqrt (2 * π)) := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos hk).symm⟩
  set L : (Fin (m + 1) → ℝ) → EuclideanSpace ℝ (Fin (m + 1)) := WithLp.toLp 2 with hLdef
  have hLmeas : Measurable L := by rw [hLdef]; fun_prop
  set T : Set (EuclideanSpace ℝ (Fin (m + 1))) :=
    {x | x ∈ V ∧ x + c • EuclideanSpace.single i (1 : ℝ) ∉ V} with hTdef
  have hTm : MeasurableSet T := by
    have hmap : Measurable (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
        x + c • EuclideanSpace.single i (1 : ℝ)) := by fun_prop
    exact hVm.inter (hmap hVm.compl)
  rw [multivariateGaussian_eq_map_pi, Measure.map_apply hLmeas hTm]
  -- the peeled product form
  set μ : Fin (m + 1) → Measure ℝ := fun _ => gaussianReal 0 1 with hμdef
  set e : ((_ : Fin (m + 1)) → ℝ) ≃ᵐ ℝ × ((_ : Fin m) → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i with hedef
  have hmp : MeasurePreserving e (Measure.pi μ)
      ((μ i).prod (Measure.pi fun j : Fin m => μ (i.succAbove j))) :=
    measurePreserving_piFinSuccAbove μ i
  set S : Set (ℝ × ((_ : Fin m) → ℝ)) := e.symm ⁻¹' (L ⁻¹' T) with hSdef
  have hSm : MeasurableSet S := e.symm.measurable (hLmeas hTm)
  have hpre : e ⁻¹' S = L ⁻¹' T := by
    ext x; simp [hSdef]
  have hkey : Measure.pi μ (L ⁻¹' T)
      = ((μ i).prod (Measure.pi fun j : Fin m => μ (i.succAbove j))) S := by
    rw [← hpre]; exact hmp.measure_preimage hSm.nullMeasurableSet
  rw [hkey, Measure.prod_apply_symm hSm]
  -- each line slice has diameter `≤ |c|`
  have hslice : ∀ y : Fin m → ℝ, (μ i) ((fun t => (t, y)) ⁻¹' S)
      ≤ ENNReal.ofReal (2 * |c| / Real.sqrt (2 * π)) := by
    intro y
    set J : Set ℝ := {t : ℝ | L (Fin.insertNth (α := fun _ => ℝ) i t y) ∈ V} with hJdef
    have hJconv : Convex ℝ J := by
      intro a ha b hb s r hs hr hsr
      have hins := insertNth_affine i y (a := a) (b := b) hsr
      have : L (Fin.insertNth (α := fun _ => ℝ) i (s * a + r * b) y)
          = s • L (Fin.insertNth (α := fun _ => ℝ) i a y)
            + r • L (Fin.insertNth (α := fun _ => ℝ) i b y) := by rw [hins]; rfl
      simpa [hJdef, this] using hVc ha hb hs hr hsr
    have hsym : ∀ t : ℝ, e.symm (t, y) = Fin.insertNth (α := fun _ => ℝ) i t y := fun _ => rfl
    have hset : (fun t => (t, y)) ⁻¹' S = {t | t ∈ J ∧ t + c ∉ J} := by
      ext t
      have hshift : L (Fin.insertNth (α := fun _ => ℝ) i (t + c) y)
          = L (Fin.insertNth (α := fun _ => ℝ) i t y)
            + c • EuclideanSpace.single i (1 : ℝ) := by
        rw [insertNth_add_single]; rfl
      simp only [Set.mem_preimage, hSdef, hsym, hTdef, Set.mem_setOf_eq, hJdef, hshift]
    rw [hset, hμdef]
    exact gaussianReal_le_of_diam_le (diam_shift_le_of_convex hJconv c)
  calc ∫⁻ y, (μ i) ((fun t => (t, y)) ⁻¹' S)
          ∂(Measure.pi fun j : Fin m => μ (i.succAbove j))
      ≤ ∫⁻ _, ENNReal.ofReal (2 * |c| / Real.sqrt (2 * π))
          ∂(Measure.pi fun j : Fin m => μ (i.succAbove j)) := lintegral_mono hslice
    _ = ENNReal.ofReal (2 * |c| / Real.sqrt (2 * π)) := by
        rw [lintegral_const, hμdef]
        simp

/-! ### Supporting functionals and the escape direction -/

/-- **Supporting hyperplane at a non-interior point.** If `V` is convex and `x ∉ interior V`,
some `u ≠ 0` supports `V` at `x`, i.e. `⟪u, w - x⟫ ≤ 0` for all `w` in the *closure* of `V`.

If `interior V ≠ ∅` this is `geometric_hahn_banach_open_point` applied to the open convex set
`interior V`, whose closure is `closure V`. If `interior V = ∅` then `V` spans a proper affine
subspace (`Convex.interior_nonempty_iff_affineSpan_eq_top`) and any `u ≠ 0` orthogonal to its
direction makes `⟪u, · - x⟫` constant on `V`; one of `±u` then works. -/
lemma exists_inner_le_zero_of_notMem_interior (hk : 0 < k)
    {V : Set (EuclideanSpace ℝ (Fin k))} (hV : Convex ℝ V)
    {x : EuclideanSpace ℝ (Fin k)} (hx : x ∉ interior V) :
    ∃ u : EuclideanSpace ℝ (Fin k), u ≠ 0 ∧ ∀ w ∈ closure V, ⟪u, w - x⟫_ℝ ≤ 0 := by
  suffices h : ∃ u : EuclideanSpace ℝ (Fin k), u ≠ 0 ∧ ∀ w ∈ V, ⟪u, w - x⟫_ℝ ≤ 0 by
    obtain ⟨u, hu0, hu⟩ := h
    refine ⟨u, hu0, ?_⟩
    have hclosed : IsClosed {w : EuclideanSpace ℝ (Fin k) | ⟪u, w - x⟫_ℝ ≤ 0} :=
      isClosed_le (Continuous.inner continuous_const (continuous_id.sub continuous_const))
        continuous_const
    exact fun w hw => hclosed.closure_subset_iff.mpr hu hw
  rcases (interior V).eq_empty_or_nonempty with hint | hint
  · -- degenerate case: `V` lies in a proper affine subspace
    rcases V.eq_empty_or_nonempty with rfl | ⟨w₀, hw₀⟩
    · obtain ⟨i⟩ : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
      exact ⟨EuclideanSpace.single i 1, by simp, by simp⟩
    · have hspan : affineSpan ℝ V ≠ ⊤ := by
        intro h
        have hne : (interior V).Nonempty := hV.interior_nonempty_iff_affineSpan_eq_top.2 h
        rw [hint] at hne
        exact Set.not_nonempty_empty hne
      have hvs : vectorSpan ℝ V ≠ ⊤ := fun h =>
        hspan ((AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ
          (EuclideanSpace ℝ (Fin k)) (EuclideanSpace ℝ (Fin k)) ⟨w₀, hw₀⟩).mpr h)
      have hbot : (vectorSpan ℝ V)ᗮ ≠ ⊥ := fun h => hvs (Submodule.orthogonal_eq_bot_iff.mp h)
      obtain ⟨u, hu, hune⟩ := Submodule.ne_bot_iff _ |>.mp hbot
      have hconst : ∀ w ∈ V, ⟪u, w - x⟫_ℝ = ⟪u, w₀ - x⟫_ℝ := by
        intro w hw
        have hmem : w - w₀ ∈ vectorSpan ℝ V := by
          simpa using vsub_mem_vectorSpan ℝ hw hw₀
        have hzero : ⟪u, w - w₀⟫_ℝ = 0 := by
          rw [real_inner_comm]
          exact (Submodule.mem_orthogonal _ u).1 hu _ hmem
        have hsplit : w - x = (w - w₀) + (w₀ - x) := by abel
        rw [hsplit, inner_add_right, hzero, zero_add]
      rcases le_or_gt (⟪u, w₀ - x⟫_ℝ) 0 with h0 | h0
      · exact ⟨u, hune, fun w hw => (hconst w hw).le.trans h0⟩
      · refine ⟨-u, neg_ne_zero.mpr hune, fun w hw => ?_⟩
        rw [inner_neg_left, hconst w hw]
        linarith
  · -- main case: separate the open convex set `interior V` from the point `x`
    obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hV.interior isOpen_interior hx
    obtain ⟨a, ha⟩ := hint
    refine ⟨(InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin k))).symm f, ?_, ?_⟩
    · intro h0
      have hlt : f a < f x := hf a ha
      have hfa : f a = 0 := by
        rw [← InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (y := f) (x := a), h0, inner_zero_left]
      have hfx : f x = 0 := by
        rw [← InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (y := f) (x := x), h0, inner_zero_left]
      rw [hfa, hfx] at hlt
      exact lt_irrefl _ hlt
    · intro w hw
      have hVsub : V ⊆ closure (interior V) := by
        rw [hV.closure_interior_eq_closure_of_nonempty_interior ⟨a, ha⟩]
        exact subset_closure
      have hclosed : IsClosed {y : EuclideanSpace ℝ (Fin k) | f y ≤ f x} :=
        isClosed_le f.continuous continuous_const
      have hle : f w ≤ f x :=
        hclosed.closure_subset_iff.mpr (fun y hy => (hf y hy).le) (hVsub hw)
      rw [InnerProductSpace.toDual_symm_apply, map_sub]
      linarith

/-- **Escape direction.** If `u ≠ 0` supports `V` at `x`, then some coordinate satisfies
`|uᵢ| ≥ ‖u‖/√k`, and moving from `x` by `±c` along that axis (sign chosen to increase `⟪u, ·⟫`)
lands at distance at least `c/√k` from every point of `V`. -/
lemma exists_dist_ge_of_inner_le_zero (hk : 0 < k)
    {V : Set (EuclideanSpace ℝ (Fin k))} {x u : EuclideanSpace ℝ (Fin k)} (hu : u ≠ 0)
    (hsupp : ∀ w ∈ V, ⟪u, w - x⟫_ℝ ≤ 0) {c : ℝ} (hc : 0 ≤ c) :
    ∃ (i : Fin k) (d : ℝ), |d| = c ∧
      ∀ w ∈ V, c / Real.sqrt k ≤ dist (x + d • EuclideanSpace.single i (1 : ℝ)) w := by
  classical
  have hne : (Finset.univ : Finset (Fin k)).Nonempty :=
    Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.mp hk)
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => |u j|) hne
  have hkr : (0 : ℝ) < Real.sqrt k := Real.sqrt_pos.2 (by exact_mod_cast hk)
  have hunorm : 0 < ‖u‖ := norm_pos_iff.2 hu
  -- the largest coordinate carries at least `‖u‖/√k`
  have hcoord : ‖u‖ ≤ Real.sqrt k * |u i| := by
    have hsum : ∑ j, ‖u j‖ ^ 2 ≤ (k : ℝ) * |u i| ^ 2 := by
      calc ∑ j : Fin k, ‖u j‖ ^ 2 ≤ ∑ _j : Fin k, |u i| ^ 2 := by
            refine Finset.sum_le_sum fun j _ => ?_
            have := hi j (Finset.mem_univ j)
            rw [Real.norm_eq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) this 2
        _ = (k : ℝ) * |u i| ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [EuclideanSpace.norm_eq]
    calc Real.sqrt (∑ j, ‖u j‖ ^ 2) ≤ Real.sqrt ((k : ℝ) * |u i| ^ 2) := Real.sqrt_le_sqrt hsum
      _ = Real.sqrt k * |u i| := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (abs_nonneg _)]
  refine ⟨i, if 0 ≤ u i then c else -c, by split_ifs <;> simp [abs_of_nonneg hc], ?_⟩
  intro w hw
  set d : ℝ := if 0 ≤ u i then c else -c with hd
  have hdu : d * u i = c * |u i| := by
    rw [hd]; split_ifs with h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (not_le.mp h)]; ring
  set y : EuclideanSpace ℝ (Fin k) := x + d • EuclideanSpace.single i (1 : ℝ) with hy
  have hinner : ⟪u, y - w⟫_ℝ = d * u i - ⟪u, w - x⟫_ℝ := by
    have hsplit : y - w = d • EuclideanSpace.single i (1 : ℝ) - (w - x) := by rw [hy]; abel
    have hsingle : ⟪u, EuclideanSpace.single i (1 : ℝ)⟫_ℝ = u i := by
      simpa using EuclideanSpace.inner_single_right i (1 : ℝ) u
    rw [hsplit, inner_sub_right, real_inner_smul_right, hsingle]
  have hlow : c * |u i| ≤ ⟪u, y - w⟫_ℝ := by
    rw [hinner, hdu]
    linarith [hsupp w hw]
  have hcs : ⟪u, y - w⟫_ℝ ≤ ‖u‖ * ‖y - w‖ := real_inner_le_norm u (y - w)
  have hstep : c * ‖u‖ / Real.sqrt k ≤ ‖u‖ * ‖y - w‖ := by
    have : c * ‖u‖ / Real.sqrt k ≤ c * |u i| := by
      rw [div_le_iff₀ hkr]
      calc c * ‖u‖ ≤ c * (Real.sqrt k * |u i|) := by
            exact mul_le_mul_of_nonneg_left hcoord hc
        _ = c * |u i| * Real.sqrt k := by ring
    linarith
  rw [dist_eq_norm, div_le_iff₀ hkr]
  rw [div_le_iff₀ hkr] at hstep
  have hmul : ‖u‖ * c ≤ ‖u‖ * (‖y - w‖ * Real.sqrt k) := by
    calc ‖u‖ * c = c * ‖u‖ := mul_comm _ _
      _ ≤ ‖u‖ * ‖y - w‖ * Real.sqrt k := hstep
      _ = ‖u‖ * (‖y - w‖ * Real.sqrt k) := by ring
  exact le_of_mul_le_mul_left hmul hunorm

/-! ### The covering bookkeeping -/

/-- The `2k` coordinate shifts cover: if every point of `S` sits in the convex measurable set `W`
and leaves `W` after a shift by `±c` along some coordinate axis, then `γ S ≤ 4kc/√(2π)`. -/
private lemma gaussian_le_of_shift_cover (hk : 0 < k)
    {W S : Set (EuclideanSpace ℝ (Fin k))} (hWm : MeasurableSet W) (hWc : Convex ℝ W)
    {c : ℝ} (hc : 0 ≤ c)
    (hcover : ∀ x ∈ S, ∃ (i : Fin k) (d : ℝ), |d| = c ∧ x ∈ W ∧
      x + d • EuclideanSpace.single i (1 : ℝ) ∉ W) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 S
      ≤ ENNReal.ofReal (4 * k * c / Real.sqrt (2 * π)) := by
  classical
  set γ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 with hγ
  set A : Fin k → Set (EuclideanSpace ℝ (Fin k)) := fun i =>
    {x | x ∈ W ∧ x + c • EuclideanSpace.single i (1 : ℝ) ∉ W} ∪
      {x | x ∈ W ∧ x + (-c) • EuclideanSpace.single i (1 : ℝ) ∉ W} with hA
  have hsub : S ⊆ ⋃ i, A i := by
    intro x hx
    obtain ⟨i, d, hd, hxW, hout⟩ := hcover x hx
    refine Set.mem_iUnion.2 ⟨i, ?_⟩
    rcases (abs_eq hc).mp hd with rfl | rfl
    · exact Or.inl ⟨hxW, hout⟩
    · exact Or.inr ⟨hxW, hout⟩
  have hpiece : ∀ i : Fin k, γ (A i) ≤ ENNReal.ofReal (4 * c / Real.sqrt (2 * π)) := by
    intro i
    have h1 := gaussian_mem_notMem_shift_le hk i c hWm hWc
    have h2 := gaussian_mem_notMem_shift_le hk i (-c) hWm hWc
    rw [abs_of_nonneg hc, ← hγ] at h1
    rw [abs_neg, abs_of_nonneg hc, ← hγ] at h2
    calc γ (A i) ≤ γ {x | x ∈ W ∧ x + c • EuclideanSpace.single i (1 : ℝ) ∉ W}
          + γ {x | x ∈ W ∧ x + (-c) • EuclideanSpace.single i (1 : ℝ) ∉ W} :=
          measure_union_le _ _
      _ ≤ ENNReal.ofReal (2 * c / Real.sqrt (2 * π))
          + ENNReal.ofReal (2 * c / Real.sqrt (2 * π)) := add_le_add h1 h2
      _ = ENNReal.ofReal (4 * c / Real.sqrt (2 * π)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
  calc γ S ≤ γ (⋃ i, A i) := measure_mono hsub
    _ ≤ ∑ i, γ (A i) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _i : Fin k, ENNReal.ofReal (4 * c / Real.sqrt (2 * π)) :=
        Finset.sum_le_sum fun i _ => hpiece i
    _ = ENNReal.ofReal (4 * k * c / Real.sqrt (2 * π)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-! ### The shell bounds -/

/-- The constant of the Gaussian shell bound, `C_k = 8 k^{3/2}/√(2π)`. (Ball's sharp constant is
`4 k^{1/4}`; only finiteness at fixed `k` is needed here.) -/
noncomputable def gaussianShellConst (k : ℕ) : ℝ := 8 * k * Real.sqrt k / Real.sqrt (2 * π)

lemma gaussianShellConst_pos (hk : 0 < k) : 0 < gaussianShellConst k := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have : 0 < Real.sqrt k := Real.sqrt_pos.2 hk'
  unfold gaussianShellConst
  positivity

/-- The covering constant at width `c = 2ε√k` is exactly `C_k ε`. -/
private lemma shift_cover_const (_hk : 0 < k) (ε : ℝ) :
    4 * (k : ℝ) * (2 * ε * Real.sqrt k) / Real.sqrt (2 * π) = gaussianShellConst k * ε := by
  unfold gaussianShellConst
  ring

/-- **A convex set differs from its interior by a Gaussian-null set.** Every non-interior point of
a convex `V` carries a supporting functional, so it leaves `V` after an arbitrarily small
coordinate shift; the slice bound then gives mass `≤ 4kc/√(2π)` for every `c > 0`. -/
theorem gaussian_diff_interior_eq_zero (hk : 0 < k)
    {V : Set (EuclideanSpace ℝ (Fin k))} (hVm : MeasurableSet V) (hVc : Convex ℝ V) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 (V \ interior V) = 0 := by
  have hkr : (0 : ℝ) < Real.sqrt k := Real.sqrt_pos.2 (by exact_mod_cast hk)
  have hsq : (0 : ℝ) < Real.sqrt (2 * π) := Real.sqrt_pos.2 (by positivity)
  have hk' : (0 : ℝ) < 4 * k := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    linarith
  have hle : ∀ c : ℝ, 0 < c →
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 (V \ interior V)
        ≤ ENNReal.ofReal (4 * k * c / Real.sqrt (2 * π)) := by
    intro c hc
    refine gaussian_le_of_shift_cover hk hVm hVc hc.le fun x hx => ?_
    obtain ⟨u, hu0, hu⟩ := exists_inner_le_zero_of_notMem_interior hk hVc hx.2
    obtain ⟨i, d, hd, hdist⟩ := exists_dist_ge_of_inner_le_zero hk hu0
      (fun w hw => hu w (subset_closure hw)) hc.le
    refine ⟨i, d, hd, hx.1, fun hmem => ?_⟩
    have hzero := hdist _ hmem
    rw [dist_self] at hzero
    exact absurd hzero (not_le.2 (div_pos hc hkr))
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) (zero_le _)
  have hεr : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hcpos : 0 < (ε : ℝ) * Real.sqrt (2 * π) / (4 * k) := by positivity
  have hval : 4 * (k : ℝ) * ((ε : ℝ) * Real.sqrt (2 * π) / (4 * k)) / Real.sqrt (2 * π)
      = (ε : ℝ) := by
    field_simp
  have := hle _ hcpos
  rw [hval, ENNReal.ofReal_coe_nnreal] at this
  simpa using this

/-- **Outer shell bound.** For convex `B`, the `ε`-thickening adds at most `C_k ε` Gaussian mass.

A point of `Bᵋ \ B` is not in `interior B`, so a supporting functional escapes it by `2ε` along a
coordinate axis (`c = 2ε√k`), which leaves `Bᵋ` altogether; `Bᵋ` is convex and open, so the slice
bound applies to it. -/
theorem gaussian_thickening_le (hk : 0 < k) {B : Set (EuclideanSpace ℝ (Fin k))}
    (hBc : Convex ℝ B) {ε : ℝ} (hε : 0 < ε) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 (Metric.thickening ε B)
      ≤ multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 B
        + ENNReal.ofReal (gaussianShellConst k * ε) := by
  have hkr : (0 : ℝ) < Real.sqrt k := Real.sqrt_pos.2 (by exact_mod_cast hk)
  set W := Metric.thickening ε B with hW
  have hWopen : IsOpen W := Metric.isOpen_thickening
  have hWconv : Convex ℝ W := hBc.thickening ε
  set c : ℝ := 2 * ε * Real.sqrt k with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hshell : multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 (W \ B)
      ≤ ENNReal.ofReal (gaussianShellConst k * ε) := by
    rw [← shift_cover_const hk ε, ← hc]
    refine gaussian_le_of_shift_cover hk hWopen.measurableSet hWconv hcpos.le fun x hx => ?_
    have hxint : x ∉ interior B := fun h => hx.2 (interior_subset h)
    obtain ⟨u, hu0, hu⟩ := exists_inner_le_zero_of_notMem_interior hk hBc hxint
    obtain ⟨i, d, hd, hdist⟩ := exists_dist_ge_of_inner_le_zero hk hu0 hu hcpos.le
    refine ⟨i, d, hd, hx.1, fun hmem => ?_⟩
    obtain ⟨z, hzB, hzlt⟩ := Metric.mem_thickening_iff.1 hmem
    have hge := hdist z (subset_closure hzB)
    have hck : c / Real.sqrt k = 2 * ε := by
      rw [hc, mul_div_assoc, div_self hkr.ne', mul_one]
    linarith
  calc multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 W
      ≤ multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 (B ∪ (W \ B)) := by
        refine measure_mono fun x hx => ?_
        by_cases hxB : x ∈ B
        · exact Or.inl hxB
        · exact Or.inr ⟨hx, hxB⟩
    _ ≤ multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 B
        + multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 (W \ B) := measure_union_le _ _
    _ ≤ _ := add_le_add le_rfl hshell

/-! ### The erosion (inner parallel body) -/

/-- The open `ε`-erosion of `B`: the points whose closed `ε`-ball lies in the interior of `B`.
It is open and convex, and its `ε`-thickening is contained in `B`. -/
def erosion (ε : ℝ) (B : Set (EuclideanSpace ℝ (Fin k))) : Set (EuclideanSpace ℝ (Fin k)) :=
  {x | Metric.closedBall x ε ⊆ interior B}

lemma isOpen_erosion (ε : ℝ) (B : Set (EuclideanSpace ℝ (Fin k))) : IsOpen (erosion ε B) := by
  rw [Metric.isOpen_iff]
  intro x hx
  obtain ⟨δ, hδ, hsub⟩ :=
    (isCompact_closedBall x ε).exists_thickening_subset_open isOpen_interior hx
  refine ⟨δ, hδ, ?_⟩
  intro x' hx'
  simp only [erosion, Set.mem_setOf_eq]
  intro y hy
  refine hsub (Metric.mem_thickening_iff.2 ⟨y + (x - x'), ?_, ?_⟩)
  · simp only [Metric.mem_closedBall, dist_eq_norm] at hy ⊢
    have hrw : y + (x - x') - x = y - x' := by abel
    rw [hrw]
    exact hy
  · simp only [dist_eq_norm]
    have hrw : y - (y + (x - x')) = x' - x := by abel
    rw [hrw]
    have := Metric.mem_ball.1 hx'
    rw [dist_eq_norm] at this
    exact this

lemma convex_erosion {ε : ℝ} {B : Set (EuclideanSpace ℝ (Fin k))} (hB : Convex ℝ B) :
    Convex ℝ (erosion ε B) := by
  intro x hx y hy s r hs hr hsr
  simp only [erosion, Set.mem_setOf_eq] at hx hy ⊢
  intro z hz
  set v := z - (s • x + r • y) with hv
  have hvnorm : ‖v‖ ≤ ε := by
    rw [hv]
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hzx : x + v ∈ interior B := by
    refine hx ?_
    simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact hvnorm
  have hzy : y + v ∈ interior B := by
    refine hy ?_
    simp only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
    exact hvnorm
  have hzeq : s • (x + v) + r • (y + v) = z := by
    have hv' : s • v + r • v = v := by rw [← add_smul, hsr, one_smul]
    rw [smul_add, smul_add]
    have hrw : s • x + s • v + (r • y + r • v) = s • x + r • y + (s • v + r • v) := by abel
    rw [hrw, hv', hv]
    abel
  rw [← hzeq]
  exact hB.interior hzx hzy hs hr hsr

lemma thickening_erosion_subset (ε : ℝ) (B : Set (EuclideanSpace ℝ (Fin k))) :
    Metric.thickening ε (erosion ε B) ⊆ B := by
  intro y hy
  obtain ⟨a, ha, hlt⟩ := Metric.mem_thickening_iff.1 hy
  exact interior_subset (ha (Metric.mem_closedBall.2 hlt.le))

/-- **Inner shell bound.** For convex measurable `B`, eroding by `ε` costs at most `C_k ε` of
Gaussian mass. A point of `B` that is not in the erosion has a point `z` within `ε` that is not
interior to `B`; the functional supporting `B` at `z` escapes `2ε` along a coordinate axis, hence
still escapes `ε` from `x`. -/
theorem gaussian_le_erosion_add (hk : 0 < k) {B : Set (EuclideanSpace ℝ (Fin k))}
    (hBm : MeasurableSet B) (hBc : Convex ℝ B) {ε : ℝ} (hε : 0 < ε) :
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 B
      ≤ multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 (erosion ε B)
        + ENNReal.ofReal (gaussianShellConst k * ε) := by
  have hkr : (0 : ℝ) < Real.sqrt k := Real.sqrt_pos.2 (by exact_mod_cast hk)
  set c : ℝ := 2 * ε * Real.sqrt k with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  have hshell : multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 (B \ erosion ε B)
      ≤ ENNReal.ofReal (gaussianShellConst k * ε) := by
    rw [← shift_cover_const hk ε, ← hc]
    refine gaussian_le_of_shift_cover hk hBm hBc hcpos.le fun x hx => ?_
    obtain ⟨z, hzball, hzint⟩ :=
      Set.not_subset.1 (hx.2 : ¬ (Metric.closedBall x ε ⊆ interior B))
    obtain ⟨u, hu0, hu⟩ := exists_inner_le_zero_of_notMem_interior hk hBc hzint
    obtain ⟨i, d, hd, hdist⟩ := exists_dist_ge_of_inner_le_zero hk hu0 hu hcpos.le
    refine ⟨i, d, hd, hx.1, fun hmem => ?_⟩
    have hge := hdist _ (subset_closure hmem)
    -- the shifted point `x + d•eᵢ` is within `ε` of `z + d•eᵢ`
    have htri : dist (z + d • EuclideanSpace.single i (1 : ℝ))
        (x + d • EuclideanSpace.single i (1 : ℝ)) ≤ ε := by
      simp only [dist_eq_norm]
      have : z + d • EuclideanSpace.single i (1 : ℝ) - (x + d • EuclideanSpace.single i (1 : ℝ))
          = z - x := by abel
      rw [this]
      simpa [dist_eq_norm] using Metric.mem_closedBall.1 hzball
    have hck : c / Real.sqrt k = 2 * ε := by
      rw [hc, mul_div_assoc, div_self hkr.ne', mul_one]
    linarith
  calc multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 B
      ≤ multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1
          (erosion ε B ∪ (B \ erosion ε B)) := by
        refine measure_mono fun x hx => ?_
        by_cases hxA : x ∈ erosion ε B
        · exact Or.inl hxA
        · exact Or.inr ⟨hx, hxA⟩
    _ ≤ multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 (erosion ε B)
        + multivariateGaussian (0 : EuclideanSpace ℝ (Fin k)) 1 (B \ erosion ε B) :=
        measure_union_le _ _
    _ ≤ _ := add_le_add le_rfl hshell

end GaussianShell

end StatLean.HypothesisTesting
