import StatLean.HypothesisTesting.GoodnessOfFit.ChiSquaredMaximin

/-! Scratch development file for wave-5 lane B, multinomial half.  Not part of the library. -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators NNReal InnerProductSpace

namespace StatLean.HypothesisTesting

open AsymptoticStatistics (WeakConverges)
open StatLean.MultipleTesting (chiSquared)

/-- Every function on a finite discrete space is integrable against a finite measure. -/
private lemma integrable_of_fintype' {X : Type*} [MeasurableSpace X] [Fintype X]
    [MeasurableSingletonClass X] (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) :
    Integrable f μ := by
  have hmeas : Measurable f := measurable_of_countable f
  refine (integrable_const (∑ y, ‖f y‖)).mono' hmeas.aestronglyMeasurable ?_
  filter_upwards with x
  exact Finset.single_le_sum (f := fun y => ‖f y‖) (fun y _ => norm_nonneg _)
    (Finset.mem_univ x)

/-- The real inner product on `EuclideanSpace ℝ (Fin k)` as a coordinate sum. -/
private lemma inner_coord_sum {k : ℕ} (u v : EuclideanSpace ℝ (Fin k)) :
    ⟪u, v⟫_ℝ = ∑ i, u i * v i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- **An orthonormal centred score system for a multinomial null.**  For an interior point
`π` of the simplex there are `k` functions on the `k+1` cells that are centred and
orthonormal in `L²(π)`.  Obtained from an orthonormal basis of the orthogonal complement of
the unit vector `(√πⱼ)ⱼ` in `EuclideanSpace ℝ (Fin (k+1))`. -/
private lemma exists_multinomial_scores {k : ℕ} {π : Fin (k + 1) → ℝ}
    (hπpos : ∀ j, 0 < π j) (hπsum : ∑ j, π j = 1) :
    ∃ ψ : Fin k → Fin (k + 1) → ℝ,
      (∀ i, ∑ j, π j * ψ i j = 0) ∧
      (∀ i i', ∑ j, π j * (ψ i j * ψ i' j) = if i = i' then 1 else 0) := by
  classical
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (k + 1))) = k + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  set w : EuclideanSpace ℝ (Fin (k + 1)) :=
    WithLp.toLp 2 (fun j => Real.sqrt (π j)) with hwdef
  have hwval : ∀ j, w j = Real.sqrt (π j) := fun j => rfl
  have hwnorm : ‖w‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    have : ∑ j, ‖w j‖ ^ 2 = 1 := by
      have h1 : ∀ j : Fin (k + 1), ‖w j‖ ^ 2 = π j := by
        intro j
        rw [hwval j, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hπpos j).le]
      simp_rw [h1]
      exact hπsum
    rw [this, Real.sqrt_one]
  have hwne : w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hwnorm
    exact zero_ne_one hwnorm
  set e := OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ)
    (E := EuclideanSpace ℝ (Fin (k + 1))) k hwne with hedef
  refine ⟨fun i j => ((e i : EuclideanSpace ℝ (Fin (k + 1))) j) / Real.sqrt (π j), ?_, ?_⟩
  · intro i
    have hperp : ⟪w, (e i : EuclideanSpace ℝ (Fin (k + 1)))⟫_ℝ = 0 := by
      have hmem := (e i).2
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hmem
      exact hmem
    rw [inner_coord_sum] at hperp
    have hcalc : ∀ j : Fin (k + 1),
        π j * (((e i : EuclideanSpace ℝ (Fin (k + 1))) j) / Real.sqrt (π j))
          = w j * (e i : EuclideanSpace ℝ (Fin (k + 1))) j := by
      intro j
      set sq : ℝ := Real.sqrt (π j) with hsqdef
      have hs : sq ≠ 0 := by rw [hsqdef]; exact (Real.sqrt_pos.mpr (hπpos j)).ne'
      have hsq : sq * sq = π j := by rw [hsqdef]; exact Real.mul_self_sqrt (hπpos j).le
      rw [hwval j, ← hsqdef, ← hsq]
      field_simp
    simp_rw [hcalc]
    exact hperp
  · intro i i'
    have horth : ⟪(e i : EuclideanSpace ℝ (Fin (k + 1))),
        (e i' : EuclideanSpace ℝ (Fin (k + 1)))⟫_ℝ = if i = i' then 1 else 0 := by
      have h := e.orthonormal
      rw [orthonormal_iff_ite] at h
      have hii := h i i'
      rwa [Submodule.coe_inner] at hii
    rw [inner_coord_sum] at horth
    have hcalc : ∀ j : Fin (k + 1),
        π j * ((((e i : EuclideanSpace ℝ (Fin (k + 1))) j) / Real.sqrt (π j))
            * (((e i' : EuclideanSpace ℝ (Fin (k + 1))) j) / Real.sqrt (π j)))
          = (e i : EuclideanSpace ℝ (Fin (k + 1))) j
              * (e i' : EuclideanSpace ℝ (Fin (k + 1))) j := by
      intro j
      set sq : ℝ := Real.sqrt (π j) with hsqdef
      have hs : sq ≠ 0 := by rw [hsqdef]; exact (Real.sqrt_pos.mpr (hπpos j)).ne'
      have hsq : sq * sq = π j := by rw [hsqdef]; exact Real.mul_self_sqrt (hπpos j).le
      rw [← hsq]
      field_simp
    simp_rw [hcalc]
    exact horth


/-! ### Elementary logarithm bounds -/

/-- `|log(1+u) − (u − u²/2)| ≤ 2|u|³` for `|u| ≤ 1/2`. -/
private lemma abs_log_one_add_sub_quad_le {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |Real.log (1 + u) - (u - u ^ 2 / 2)| ≤ 2 * |u| ^ 3 := by
  have hlt : |(-u)| < 1 := by rw [abs_neg]; linarith
  have h := Real.abs_log_sub_add_sum_range_le hlt 2
  have hsum : (∑ i ∈ Finset.range 2, (-u) ^ (i + 1) / ((i : ℝ) + 1)) = -u + u ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ]
  have hone : (1 : ℝ) - (-u) = 1 + u := by ring
  rw [hsum, hone] at h
  have habs : |(-u)| = |u| := abs_neg u
  rw [habs] at h
  have hden : (1 : ℝ) / 2 ≤ 1 - |u| := by linarith
  have hpos : (0 : ℝ) < 1 - |u| := by linarith
  have hpow : |u| ^ (2 + 1) = |u| ^ 3 := by norm_num
  rw [hpow] at h
  have hstep : |u| ^ 3 / (1 - |u|) ≤ 2 * |u| ^ 3 := by
    rw [div_le_iff₀ hpos]
    have hc : (0 : ℝ) ≤ |u| ^ 3 := pow_nonneg (abs_nonneg u) 3
    nlinarith
  have heq : -u + u ^ 2 / 2 + Real.log (1 + u) = Real.log (1 + u) - (u - u ^ 2 / 2) := by ring
  rw [heq] at h
  exact h.trans hstep

/-- `|log(1+u)| ≤ 1` for `|u| ≤ 1/2`. -/
private lemma abs_log_one_add_le_one {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |Real.log (1 + u)| ≤ 1 := by
  have hb := abs_le.mp hu
  have hpos : (0 : ℝ) < 1 + u := by linarith [hb.1]
  have hup : Real.log (1 + u) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos hpos
    linarith [hb.2]
  have hlow : -1 ≤ Real.log (1 + u) := by
    have h := Real.log_le_sub_one_of_pos (x := (1 + u)⁻¹) (by positivity)
    rw [Real.log_inv] at h
    have hinv : (1 + u)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ hpos (by norm_num)]
      linarith [hb.1]
    linarith
  rw [abs_le]
  exact ⟨hlow, hup⟩

/-! ### A weak law of large numbers on the canonical product experiment -/

/-- **WLLN on the canonical `n`-fold product.**  For a finite family of integrable functions
with prescribed means, the total absolute deviation of the empirical means tends to `0` in
probability under the `n`-fold product of the sampling law. -/
private lemma pi_lln_tendsto {X : Type*} [MeasurableSpace X] {P₀ : Measure X}
    [IsProbabilityMeasure P₀] {ι : Type*} [Fintype ι] (F : ι → X → ℝ) (cst : ι → ℝ)
    (hFmeas : ∀ a, Measurable (F a)) (hFint : ∀ a, Integrable (F a) P₀)
    (hFmean : ∀ a, ∫ x, F a x ∂P₀ = cst a) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => ((Measure.pi fun _ : Fin n => P₀)
      {d : Fin n → X | δ ≤ ∑ a, |(∑ l : Fin n, F a (d l)) / (n : ℝ) - cst a|}).toReal)
      atTop (nhds 0) := by
  classical
  obtain ⟨Ω₀, mΩ₀, P₀c, Z, hZmeas, hZlaw, hZindep, hP₀cprob⟩ :=
    ProbabilityTheory.exists_iid ℕ P₀
  letI : MeasurableSpace Ω₀ := mΩ₀
  haveI : IsProbabilityMeasure P₀c := hP₀cprob
  set V : (n : ℕ) → (Fin n → X) → ℝ :=
    fun n d => ∑ a, |(∑ l : Fin n, F a (d l)) / (n : ℝ) - cst a| with hVdef
  have hVmeas : ∀ n, Measurable (V n) := by
    intro n
    refine Finset.univ.measurable_sum fun a _ => ?_
    exact (((Finset.univ.measurable_sum fun l _ =>
      (hFmeas a).comp (measurable_pi_apply l)).div measurable_const).sub measurable_const).abs
  have hZfun : ∀ n : ℕ, Measurable (fun ω (l : Fin n) => Z (l : ℕ) ω) :=
    fun n => measurable_pi_lambda _ fun l => hZmeas (l : ℕ)
  set G : ℕ → Ω₀ → ℝ := fun n ω => V n (fun l : Fin n => Z (l : ℕ) ω) with hGdef
  have hGmeas : ∀ n, Measurable (G n) := fun n => (hVmeas n).comp (hZfun n)
  -- almost sure convergence, coordinate by coordinate
  have hcoord : ∀ a : ι, ∀ᵐ ω ∂P₀c, Tendsto
      (fun n : ℕ => (∑ l : Fin n, F a (Z (l : ℕ) ω)) / (n : ℝ)) atTop (nhds (cst a)) := by
    intro a
    have hmapeq : P₀c.map (Z 0) = P₀ := (hZlaw 0).map_eq
    have hint0 : Integrable (fun ω => F a (Z 0 ω)) P₀c := by
      have h1 : Integrable (F a) (P₀c.map (Z 0)) := by rw [hmapeq]; exact hFint a
      refine (integrable_map_measure ?_ (hZmeas 0).aemeasurable).1 h1
      rw [hmapeq]; exact (hFint a).aestronglyMeasurable
    have hindep : Pairwise (fun i j : ℕ => ProbabilityTheory.IndepFun
        (fun ω => F a (Z i ω)) (fun ω => F a (Z j ω)) P₀c) := by
      have hcomp : iIndepFun (fun (i : ℕ) ω => F a (Z i ω)) P₀c :=
        hZindep.comp (fun _ => F a) (fun _ => hFmeas a)
      exact fun i j hij => hcomp.indepFun hij
    have hident : ∀ i, IdentDistrib (fun ω => F a (Z i ω)) (fun ω => F a (Z 0 ω)) P₀c P₀c :=
      fun i => (show IdentDistrib (Z i) (Z 0) P₀c P₀c from
        ⟨(hZmeas i).aemeasurable, (hZmeas 0).aemeasurable,
          (hZlaw i).map_eq.trans (hZlaw 0).map_eq.symm⟩).comp (hFmeas a)
    have hmean : ∫ ω, F a (Z 0 ω) ∂P₀c = cst a := by
      rw [show (∫ ω, F a (Z 0 ω) ∂P₀c) = ∫ x, F a x ∂(P₀c.map (Z 0)) from
        (integral_map (hZmeas 0).aemeasurable
          (by rw [hmapeq]; exact (hFint a).aestronglyMeasurable)).symm, hmapeq]
      exact hFmean a
    have hlaw := ProbabilityTheory.strong_law_ae (fun i ω => F a (Z i ω)) hint0 hindep hident
    filter_upwards [hlaw] with ω hω
    rw [hmean] at hω
    refine hω.congr fun n => ?_
    rw [Fin.sum_univ_eq_sum_range (fun l => F a (Z l ω)) n, smul_eq_mul, div_eq_inv_mul]
  have hae : ∀ᵐ ω ∂P₀c, Tendsto (fun n => G n ω) atTop (nhds 0) := by
    rw [← ae_all_iff] at hcoord
    filter_upwards [hcoord] with ω hω
    have hzero : (0 : ℝ) = ∑ _a : ι, (0 : ℝ) := by simp
    rw [hGdef]
    simp only [hVdef]
    rw [hzero]
    refine tendsto_finset_sum _ fun a _ => ?_
    have hconst : Tendsto (fun _ : ℕ => cst a) atTop (nhds (cst a)) := tendsto_const_nhds
    have hsub : Tendsto (fun n : ℕ => (∑ l : Fin n, F a (Z (l : ℕ) ω)) / (n : ℝ) - cst a)
        atTop (nhds 0) := by simpa using (hω a).sub hconst
    simpa using hsub.abs
  have hmeasure : TendstoInMeasure P₀c G atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hGmeas n).aestronglyMeasurable) hae
  have h1 := hmeasure (ENNReal.ofReal δ) (by simpa using hδ)
  -- transport the measure back to the product law
  have hmap : ∀ n : ℕ, (Measure.pi fun _ : Fin n => P₀)
      = P₀c.map (fun ω (l : Fin n) => Z (l : ℕ) ω) := by
    intro n
    rw [(iIndepFun_iff_map_fun_eq_pi_map
      (f := fun (l : Fin n) => Z (l : ℕ)) (fun l => (hZmeas (l : ℕ)).aemeasurable)).1
      (hZindep.precomp Fin.val_injective)]
    congr 1
    funext l
    exact ((hZlaw (l : ℕ)).map_eq).symm
  have hVset : ∀ n : ℕ, MeasurableSet {d : Fin n → X | δ ≤ V n d} :=
    fun n => measurableSet_le measurable_const (hVmeas n)
  have hVnn : ∀ n (d : Fin n → X), 0 ≤ V n d :=
    fun n d => Finset.sum_nonneg fun a _ => abs_nonneg _
  have hsets : ∀ n : ℕ, (Measure.pi fun _ : Fin n => P₀) {d : Fin n → X | δ ≤ V n d}
      = P₀c {ω | ENNReal.ofReal δ ≤ edist (G n ω) 0} := by
    intro n
    rw [hmap n, Measure.map_apply (hZfun n) (hVset n)]
    congr 1
    ext ω
    simp only [Set.mem_preimage, Set.mem_setOf_eq, edist_dist, Real.dist_eq, sub_zero, hGdef]
    rw [ENNReal.ofReal_le_ofReal_iff (abs_nonneg _), abs_of_nonneg (hVnn n _)]
  have h2 : Tendsto (fun n : ℕ => ((Measure.pi fun _ : Fin n => P₀)
      {d : Fin n → X | δ ≤ V n d})) atTop (nhds 0) := by
    refine h1.congr fun n => ?_
    rw [hsets n]
  have h3 := (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).tendsto.comp h2
  simp only [hVdef] at h3
  simpa using h3

end StatLean.HypothesisTesting
