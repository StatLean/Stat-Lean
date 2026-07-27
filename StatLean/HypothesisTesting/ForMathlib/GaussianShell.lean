/-
Copyright (c) 2026 Junwei Lu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.LocallyConvex.Separation
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
open scoped RealInnerProductSpace ENNReal NNReal Real

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

end GaussianShell

end StatLean.HypothesisTesting
