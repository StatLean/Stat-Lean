import StatLean.RobustStatistics.LocationScale.Mean
import StatLean.ConcentrationInequalities.SubGaussian.Hoeffding
import StatLean.ConcentrationInequalities.SubGaussian.Bounded
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Probability.Moments.Variance

/-!
# Multivariate median-of-means via minimal-radius majority balls — dimension-free

Extending median-of-means to `ℝᵈ` requires a multivariate median. The coordinate-wise
median pays a `√(Tr(Σ) log(d/δ))` price; the *minimal-radius majority ball* median of
`LM §3.2` is dimension-free: define `μ̂` as a center whose ball containing **more than
half** of the block means has minimal radius. Chebyshev in norm puts each block mean
within `r = 2√(Tr(Σ)/m)` of `μ` with probability `≥ 3/4`; on the majority event the
optimal ball has radius `≤ r`, any two majority balls share a block mean, and the
triangle inequality gives `‖μ̂ − μ‖ ≤ 2r` (`LM Proposition 1`):

  `‖μ̂ − μ‖ ≤ 4 √( Tr(Σ)(8 log(1/δ) + 1) / n )`  with probability `≥ 1 − δ`.

Here `Tr(Σ) = E‖X − μ‖²` is carried directly as the second moment. The sub-Gaussian
benchmark this should be compared against is `LM (3.1)`; the truly sub-Gaussian
median-of-means *tournament* estimator (`LM §3.4`) and the geometric median-of-means
(Minsker (2015)) are bib notes only, not formalized this round.

* `blockMeanVec`, `momCount`, `momRadius`, `IsBallMoMCenter`.
* `momRadius_le_of_majority`, `majority_of_lt_momRadius` — the `sInf` interface.
* `dist_le_of_majority_two` — two majority balls intersect (the pigeonhole).
* `norm_blockMeanVec_sq_moment` — `E‖Z_j − μ‖² = Tr(Σ)/m`.
* `ballMoM_deviation` — `LM Proposition 1`.

**Reference.** G. Lugosi and S. Mendelson, *Mean estimation and regression under
heavy-tailed distributions — a survey*, Found. Comput. Math. (2019); arXiv:1906.04280v1.
(`LM`.) §3.1–§3.2, display (3.1), Proposition 1.
-/

open MeasureTheory Filter Topology ProbabilityTheory

namespace StatLean.RobustStatistics

variable {d : ℕ}

/-- The blockwise mean of vector observations (`LM §3.2`, `Z_j = (1/m) ∑_{i∈B_j} X_i`),
with the block structure presented as a double index. -/
noncomputable def blockMeanVec {k m : ℕ} (x : Fin k → Fin m → EuclideanSpace ℝ (Fin d))
    (j : Fin k) : EuclideanSpace ℝ (Fin d) :=
  (m : ℝ)⁻¹ • ∑ i, x j i

/-- The number of the `k` points within distance `r` of a candidate center `c`
(`LM §3.2`, "the ball centered at `μ̂` that contains more than `k/2` of the points"). -/
noncomputable def momCount {k : ℕ} (Z : Fin k → EuclideanSpace ℝ (Fin d))
    (c : EuclideanSpace ℝ (Fin d)) (r : ℝ) : ℕ :=
  (Finset.univ.filter fun j => ‖Z j - c‖ ≤ r).card

/-- **The majority-ball radius** (`LM §3.2`): the infimum radius of a ball at `c`
containing *strictly more than half* of the points (`k < 2·count`). The defining set is
nonempty (any radius dominating all distances works) and bounded below by `0`, so the
infimum is honest; it is `0` when a strict majority of the points coincide with `c`. -/
noncomputable def momRadius {k : ℕ} (Z : Fin k → EuclideanSpace ℝ (Fin d))
    (c : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sInf {r : ℝ | 0 ≤ r ∧ k < 2 * momCount Z c r}

/-- **The ball-MoM center property** (`LM §3.2`): `c` minimizes the majority-ball
radius over all candidate centers. As with all argmin estimators in this library, the
estimator is a predicate; the theorems consume any selection satisfying it. -/
def IsBallMoMCenter {k : ℕ} (Z : Fin k → EuclideanSpace ℝ (Fin d))
    (c : EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ a : EuclideanSpace ℝ (Fin d), momRadius Z c ≤ momRadius Z a

/-- If a radius `r ≥ 0` captures a strict majority, the majority-ball radius is `≤ r`. -/
theorem momRadius_le_of_majority {k : ℕ} {Z : Fin k → EuclideanSpace ℝ (Fin d)}
    {c : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hr : 0 ≤ r)
    (h : k < 2 * momCount Z c r) : momRadius Z c ≤ r :=
  -- The defining set is bounded below by `0` (membership carries `0 ≤ r`), so `csInf_le`
  -- applies to the witness `r` itself.
  csInf_le ⟨0, fun _ hx => hx.1⟩ ⟨hr, h⟩

/-- The majority count is monotone in the radius (the filter is monotone in its
predicate). -/
private theorem momCount_mono {k : ℕ} {Z : Fin k → EuclideanSpace ℝ (Fin d)}
    {c : EuclideanSpace ℝ (Fin d)} {r₁ r₂ : ℝ} (h : r₁ ≤ r₂) :
    momCount Z c r₁ ≤ momCount Z c r₂ := by
  refine Finset.card_le_card fun j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  exact hj.trans h

/-- Any radius strictly above the majority-ball radius captures a strict majority (the
count is monotone in `r`, and the infimum's defining set is upward closed). -/
theorem majority_of_lt_momRadius {k : ℕ} {Z : Fin k → EuclideanSpace ℝ (Fin d)}
    {c : EuclideanSpace ℝ (Fin d)} {r : ℝ} (hk : k ≠ 0)
    (h : momRadius Z c < r) : k < 2 * momCount Z c r := by
  have hbdd : BddBelow {r : ℝ | 0 ≤ r ∧ k < 2 * momCount Z c r} := ⟨0, fun _ hx => hx.1⟩
  -- The total sum of the distances dominates every single distance, so it captures all
  -- `k` points; with `k ≠ 0` that is a strict majority, and the defining set is nonempty.
  have hne : {r : ℝ | 0 ≤ r ∧ k < 2 * momCount Z c r}.Nonempty := by
    refine ⟨∑ j, ‖Z j - c‖, Finset.sum_nonneg fun _ _ => norm_nonneg _, ?_⟩
    have hall : momCount Z c (∑ j, ‖Z j - c‖) = k := by
      unfold momCount
      rw [Finset.filter_true_of_mem fun j _ =>
        Finset.single_le_sum (f := fun j => ‖Z j - c‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)]
      simp
    rw [hall]; omega
  -- Some member of the defining set already lies below `r`; upward closure does the rest.
  obtain ⟨a, haS, har⟩ := (csInf_lt_iff hbdd hne).mp h
  exact lt_of_lt_of_le haS.2 (Nat.mul_le_mul_left 2 (momCount_mono har.le))

/-- **Two majority balls intersect in a data point** (`LM §3.2` proof, "at least one of
the `Z_j` is within distance `r` to both `μ` and `μ̂`"): if balls of radii `r₁, r₂` at
`c₁, c₂` each capture a strict majority, some `Z_j` lies in both, so
`‖c₁ − c₂‖ ≤ r₁ + r₂`. -/
theorem dist_le_of_majority_two {k : ℕ} {Z : Fin k → EuclideanSpace ℝ (Fin d)}
    {c₁ c₂ : EuclideanSpace ℝ (Fin d)} {r₁ r₂ : ℝ}
    (h₁ : k < 2 * momCount Z c₁ r₁) (h₂ : k < 2 * momCount Z c₂ r₂) :
    ‖c₁ - c₂‖ ≤ r₁ + r₂ := by
  set A := Finset.univ.filter fun j => ‖Z j - c₁‖ ≤ r₁ with hA
  set B := Finset.univ.filter fun j => ‖Z j - c₂‖ ≤ r₂ with hB
  -- `|A ∪ B| + |A ∩ B| = |A| + |B| > k ≥ |A ∪ B|`, so the intersection is nonempty.
  have hcard : (A ∪ B).card + (A ∩ B).card = A.card + B.card :=
    Finset.card_union_add_card_inter A B
  have hub : (A ∪ B).card ≤ k := by simpa using Finset.card_le_univ (A ∪ B)
  have hpos : 0 < (A ∩ B).card := by
    simp only [momCount, ← hA, ← hB] at h₁ h₂
    omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
  rw [Finset.mem_inter, hA, hB] at hj
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  calc ‖c₁ - c₂‖ = ‖(c₁ - Z j) + (Z j - c₂)‖ := by congr 1; abel
    _ ≤ ‖c₁ - Z j‖ + ‖Z j - c₂‖ := norm_add_le _ _
    _ ≤ r₁ + r₂ := by rw [norm_sub_rev]; exact add_le_add hj.1 hj.2

variable {Ξ : Type*} [MeasurableSpace Ξ] {μprob : Measure Ξ} [IsProbabilityMeasure μprob]
  {P : Measure (EuclideanSpace ℝ (Fin d))} [IsProbabilityMeasure P]

/-- Coordinate evaluation on `EuclideanSpace` is measurable (the `WithLp` measurable
structure is the product one). -/
private theorem measurable_coord (a : Fin d) :
    Measurable (fun v : EuclideanSpace ℝ (Fin d) => v a) := by fun_prop

/-- The squared Euclidean norm as the sum of the squared coordinates. -/
private theorem norm_sq_eq_sum_coord (v : EuclideanSpace ℝ (Fin d)) :
    ‖v‖ ^ 2 = ∑ a, (v a) ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [sq_abs]

/-- **Second moment of a block mean** (`LM §3.2` proof, `E‖Z_j − μ‖² = Tr(Σ)/m`): for a
block of `m` i.i.d. centered square-integrable vectors, the squared-norm moment of the
block mean is `trSigma/m`, where `trSigma = E‖X − μ₀‖²` is the trace of the covariance. -/
theorem norm_blockMeanVec_sq_moment {m : ℕ} (hm : m ≠ 0)
    {X : Fin m → Ξ → EuclideanSpace ℝ (Fin d)} {μ₀ : EuclideanSpace ℝ (Fin d)}
    {trSigma : ℝ}
    -- LEAN-ONLY: coordinate measurability; LM §3 regularity
    (hX_meas : ∀ i, Measurable (X i))
    -- USER-INPUT: independent block coordinates; LM Proposition 1
    (hX_indep : iIndepFun X μprob)
    -- USER-INPUT: common law P; LM Proposition 1
    (hX_law : ∀ i, μprob.map (X i) = P)
    -- USER-INPUT: square-integrability, mean, and trace second moment; LM §3
    (hL2 : MemLp id 2 P) (hmean : ∫ x, x ∂P = μ₀)
    (htr : ∫ x, ‖x - μ₀‖ ^ 2 ∂P = trSigma) :
    ∫ ξ, ‖(m : ℝ)⁻¹ • (∑ i, X i ξ) - μ₀‖ ^ 2 ∂μprob = trSigma / m := by
  have hmR : (0 : ℝ) < m := by positivity
  have hmR' : (m : ℝ) ≠ 0 := ne_of_gt hmR
  have hid : Integrable (fun v : EuclideanSpace ℝ (Fin d) => v) P := hL2.integrable one_le_two
  have hcen : Measurable (fun v : EuclideanSpace ℝ (Fin d) => v - μ₀) :=
    measurable_id.sub_const μ₀
  -- the law transports square-integrability from `P` to each observation
  have hXL2 : ∀ i, MemLp (X i) 2 μprob := by
    intro i
    have h := hL2
    rw [← hX_law i] at h
    exact (memLp_map_measure_iff (by fun_prop) (hX_meas i).aemeasurable).mp h
  have hYL2 : ∀ i, MemLp (fun ξ => X i ξ - μ₀) 2 μprob := fun i =>
    (hXL2 i).sub (memLp_const μ₀)
  have hYmeas : ∀ i, Measurable (fun ξ => X i ξ - μ₀) := fun i => (hX_meas i).sub measurable_const
  -- coordinates of the centred observations, under `μprob` and under `P`
  have hWmeas : ∀ (a : Fin d) (i : Fin m), Measurable (fun ξ => (X i ξ - μ₀) a) := fun a i =>
    (measurable_coord a).comp (hYmeas i)
  have hWL2 : ∀ (a : Fin d) (i : Fin m), MemLp (fun ξ => (X i ξ - μ₀) a) 2 μprob := fun a i =>
    (hYL2 i).mono (hWmeas a i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => PiLp.norm_apply_le _ a)
  have hPWL2 : ∀ a : Fin d, MemLp (fun v : EuclideanSpace ℝ (Fin d) => (v - μ₀) a) 2 P :=
    fun a => (hL2.sub (memLp_const μ₀)).mono
      ((measurable_coord a).comp hcen).aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => PiLp.norm_apply_le _ a)
  -- transport of a coordinate integrand from `μprob` to `P`
  have htrans : ∀ (i : Fin m) (f : EuclideanSpace ℝ (Fin d) → ℝ), Measurable f →
      ∫ ξ, f (X i ξ) ∂μprob = ∫ v, f v ∂P := by
    intro i f hf
    rw [← hX_law i, integral_map (hX_meas i).aemeasurable hf.aestronglyMeasurable]
  -- each centred coordinate has mean zero
  have hWmean : ∀ (a : Fin d) (i : Fin m), ∫ ξ, (X i ξ - μ₀) a ∂μprob = 0 := by
    intro a i
    rw [htrans i (fun v => (v - μ₀) a) ((measurable_coord a).comp hcen)]
    have hint : Integrable (fun v : EuclideanSpace ℝ (Fin d) => v - μ₀) P :=
      hid.sub (integrable_const μ₀)
    have hcomm := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj (𝕜 := ℝ) a) hint
    rw [show (∫ v, (v - μ₀) a ∂P) = ∫ v, EuclideanSpace.proj (𝕜 := ℝ) a (v - μ₀) ∂P from rfl,
      hcomm, integral_sub hid (integrable_const _)]
    simp [hmean]
  have hfun : ∀ a : Fin d, (∑ i ∈ Finset.univ, fun ξ => (X i ξ - μ₀) a)
      = fun ξ => ∑ i, (X i ξ - μ₀) a := fun a => by
    funext ξ; simp [Finset.sum_apply]
  -- the block-sum variance identity, one coordinate at a time
  have hWvar : ∀ a : Fin d, ∫ ξ, (∑ i, (X i ξ - μ₀) a) ^ 2 ∂μprob
      = m * ∫ v, ((v - μ₀) a) ^ 2 ∂P := by
    intro a
    have hindep : Set.Pairwise (↑(Finset.univ : Finset (Fin m)))
        fun i j => (fun ξ => (X i ξ - μ₀) a) ⟂ᵢ[μprob] (fun ξ => (X j ξ - μ₀) a) :=
      fun i _ j _ hij => (hX_indep.indepFun hij).comp
        ((measurable_coord a).comp hcen) ((measurable_coord a).comp hcen)
    have hvs := IndepFun.variance_sum
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin m))) => hWL2 a i) hindep
    rw [hfun a] at hvs
    have hmeanS : ∫ ξ, ∑ i, (X i ξ - μ₀) a ∂μprob = 0 := by
      rw [integral_finset_sum _ fun i _ => (hWL2 a i).integrable one_le_two]
      exact Finset.sum_eq_zero fun i _ => hWmean a i
    have hLHS : Var[fun ξ => ∑ i, (X i ξ - μ₀) a; μprob]
        = ∫ ξ, (∑ i, (X i ξ - μ₀) a) ^ 2 ∂μprob := by
      rw [variance_eq_integral
        (Finset.measurable_sum _ fun i _ => hWmeas a i).aemeasurable, hmeanS]
      simp
    have hRHS : ∀ i : Fin m, Var[fun ξ => (X i ξ - μ₀) a; μprob]
        = ∫ v, ((v - μ₀) a) ^ 2 ∂P := by
      intro i
      rw [variance_eq_integral (hWmeas a i).aemeasurable, hWmean a i]
      simp only [sub_zero]
      exact htrans i (fun v => ((v - μ₀) a) ^ 2) (((measurable_coord a).comp hcen).pow_const 2)
    rw [hLHS] at hvs
    rw [hvs, Finset.sum_congr rfl fun i _ => hRHS i]
    simp [Finset.card_univ]
  -- sum the coordinates back up
  have hsum : ∫ ξ, ‖∑ i, (X i ξ - μ₀)‖ ^ 2 ∂μprob = m * trSigma := by
    have h1 : ∀ ξ, ‖∑ i, (X i ξ - μ₀)‖ ^ 2 = ∑ a, (∑ i, (X i ξ - μ₀) a) ^ 2 := by
      intro ξ; rw [norm_sq_eq_sum_coord]; simp
    have hSL2 : ∀ a : Fin d, MemLp (fun ξ => ∑ i, (X i ξ - μ₀) a) 2 μprob := fun a => by
      have h := memLp_finset_sum' (μ := μprob) (p := 2) (f := fun i ξ => (X i ξ - μ₀) a)
        Finset.univ fun i _ => hWL2 a i
      rwa [hfun a] at h
    calc ∫ ξ, ‖∑ i, (X i ξ - μ₀)‖ ^ 2 ∂μprob
        = ∫ ξ, ∑ a, (∑ i, (X i ξ - μ₀) a) ^ 2 ∂μprob := by simp only [h1]
      _ = ∑ a, ∫ ξ, (∑ i, (X i ξ - μ₀) a) ^ 2 ∂μprob :=
          integral_finset_sum _ fun a _ => (hSL2 a).integrable_sq
      _ = ∑ a, (m : ℝ) * ∫ v, ((v - μ₀) a) ^ 2 ∂P := Finset.sum_congr rfl fun a _ => hWvar a
      _ = (m : ℝ) * ∑ a, ∫ v, ((v - μ₀) a) ^ 2 ∂P := by rw [Finset.mul_sum]
      _ = (m : ℝ) * ∫ v, ∑ a, ((v - μ₀) a) ^ 2 ∂P := by
          rw [integral_finset_sum _ fun a _ => (hPWL2 a).integrable_sq]
      _ = (m : ℝ) * trSigma := by
          rw [← htr]; congr 1; exact integral_congr_ae
            (Filter.Eventually.of_forall fun v => (norm_sq_eq_sum_coord (v - μ₀)).symm)
  -- rewrite the block mean as the centred block sum and conclude
  have hpt : ∀ ξ, (m : ℝ)⁻¹ • (∑ i, X i ξ) - μ₀ = (m : ℝ)⁻¹ • ∑ i, (X i ξ - μ₀) := by
    intro ξ
    have hs : ∑ i, (X i ξ - μ₀) = (∑ i, X i ξ) - (m : ℝ) • μ₀ := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        ← Nat.cast_smul_eq_nsmul ℝ]
    rw [hs, smul_sub, inv_smul_smul₀ hmR']
  calc ∫ ξ, ‖(m : ℝ)⁻¹ • (∑ i, X i ξ) - μ₀‖ ^ 2 ∂μprob
      = ∫ ξ, ((m : ℝ) ^ 2)⁻¹ * ‖∑ i, (X i ξ - μ₀)‖ ^ 2 ∂μprob := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
        show ‖(m : ℝ)⁻¹ • (∑ i, X i ξ) - μ₀‖ ^ 2
            = ((m : ℝ) ^ 2)⁻¹ * ‖∑ i, (X i ξ - μ₀)‖ ^ 2
        rw [hpt ξ, norm_smul, mul_pow, Real.norm_eq_abs, abs_inv, Nat.abs_cast, inv_pow]
    _ = ((m : ℝ) ^ 2)⁻¹ * ((m : ℝ) * trSigma) := by rw [integral_const_mul, hsum]
    _ = trSigma / m := by field_simp


/-- **The minimal-radius-ball median-of-means is dimension-free** (`LM Proposition 1`):
for i.i.d. random vectors with mean `μ₀` and covariance trace `trSigma`, blocked into
`k = ⌈8 log(1/δ)⌉` blocks of size `m` with `n = km`, any measurable selection `Ĉ` of
ball-MoM centers satisfies, with probability at least `1 − δ`,

  `‖Ĉ − μ₀‖ ≤ 4 √( trSigma (8 log(1/δ) + 1) / n )`. -/
theorem ballMoM_deviation {k m n : ℕ} (hk : k ≠ 0) (hm : m ≠ 0)
    {X : Fin k → Fin m → Ξ → EuclideanSpace ℝ (Fin d)}
    {Chat : Ξ → EuclideanSpace ℝ (Fin d)} {μ₀ : EuclideanSpace ℝ (Fin d)}
    {trSigma δ : ℝ}
    -- LEAN-ONLY: coordinate measurability; LM §3 regularity
    (hX_meas : ∀ j i, Measurable (X j i))
    -- USER-INPUT: the n observations are jointly independent; LM Proposition 1
    (hX_indep : iIndepFun (fun q : Fin k × Fin m => X q.1 q.2) μprob)
    -- USER-INPUT: common law P; LM Proposition 1
    (hX_law : ∀ j i, μprob.map (X j i) = P)
    -- USER-INPUT: square-integrability, mean, covariance trace; LM Proposition 1
    (hL2 : MemLp id 2 P) (hmean : ∫ x, x ∂P = μ₀)
    (htr : ∫ x, ‖x - μ₀‖ ^ 2 ∂P = trSigma) (htrpos : 0 < trSigma)
    -- USER-INPUT: confidence level and block count; LM Proposition 1
    (hδ : 0 < δ) (hδ1 : δ < 1) (hn : n = k * m)
    (hkc : k = ⌈8 * Real.log (1 / δ)⌉₊)
    -- USER-INPUT: Ĉ is a ball-MoM center of the block means, sample-wise; LM §3.2
    (hChat : ∀ ξ, IsBallMoMCenter (fun j => blockMeanVec (fun j i => X j i ξ) j)
      (Chat ξ))
    -- LEAN-ONLY: measurability of the selection, for the deviation event
    (hCmeas : Measurable Chat) :
    μprob.real {ξ | 4 * Real.sqrt (trSigma * (8 * Real.log (1 / δ) + 1) / n)
        < ‖Chat ξ - μ₀‖}
      ≤ δ := by
  sorry

end StatLean.RobustStatistics
