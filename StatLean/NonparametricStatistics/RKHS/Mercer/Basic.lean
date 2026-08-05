import StatLean.NonparametricStatistics.RKHS.Mercer.Defs
import StatLean.NonparametricStatistics.RKHS.OrthonormalExpansion
import StatLean.NonparametricStatistics.RKHS.Continuity
import Mathlib.Topology.UniformSpace.Dini

/-!
# Basic theory of Mercer kernels

For a Mercer kernel `K` on a compact metric space `X` and a finite Borel measure `μ`:

* norm comparisons on the RKHS `H` of `K`: `‖f‖_{L²} ≤ √μ(X) ‖f‖_∞` and
  `‖f x‖ ≤ √(sup K(x,x)) ‖f‖_H`;
* `H` is separable (kernel functions over a countable dense set of `X` are dense);
* **uniform absolute convergence** of the basis expansion of `K`: the partial sums of
  `∑ᵢ conj (eᵢ y) eᵢ x` converge uniformly on `X × X` (Dini's theorem on the diagonal
  plus Cauchy–Schwarz off the diagonal);
* the integral operator `T_K` is bounded with `‖T_K‖ ≤ ‖K‖_{L²(μ×μ)}`, has continuous
  range, and is a positive operator;
* conversely (for `μ` of full support), a continuous Hermitian `K` with positive `T_K`
  is a Mercer kernel;
* the image of the `L²` unit ball under `T_K` is equicontinuous and pointwise bounded.

**Bibliographic comments.** J. Mercer, Philos. Trans. Roy. Soc. A **209** (1909);
the Dini argument for uniform convergence is from E. H. Moore's treatment, cf.
F. Smithies, *Integral Equations* (CUP, 1958), Ch. 7.
-/

open RKHS ComplexConjugate MeasureTheory
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X]
variable {μ : Measure X} [IsFiniteMeasure μ]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [RKHS 𝕜 H X 𝕜]

section NormComparison

omit [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- The norm of a kernel function is the square root of the kernel diagonal. -/
private theorem norm_kernelFun_eq_sqrt (x : X) :
    ‖kernelFun H x‖ = Real.sqrt (RCLike.re (scalarKernel H x x)) := by
  rw [scalarKernel_eq_inner, ← norm_sq_eq_re_inner (𝕜 := 𝕜), Real.sqrt_sq (norm_nonneg _)]

omit [MeasurableSpace X] [BorelSpace X] in
/-- The diagonal of a continuous kernel on a compact space is bounded above. -/
private theorem bddAbove_re_diag {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2) :
    BddAbove (Set.range fun t : X => RCLike.re (K t t)) := by
  have hc : Continuous fun t : X => RCLike.re (K t t) :=
    RCLike.continuous_re.comp' (hKc.comp' (continuous_id.prodMk continuous_id))
  simpa [Set.image_univ] using isCompact_univ.bddAbove_image hc.continuousOn

omit [MeasurableSpace X] [BorelSpace X] in
/-- Pointwise bound over the kernel diagonal supremum: for `f` in the RKHS of a Mercer
kernel, `‖f x‖ ≤ √(sup_t K(t,t)) · ‖f‖`. -/
theorem norm_apply_le_sSup {K : X → X → 𝕜} (hK : IsMercerKernel 𝕜 K)
    -- USER-INPUT: `H` has reproducing kernel `K`
    (hKH : scalarKernel H = K) (f : H) (x : X) :
    ‖f x‖ ≤ Real.sqrt (⨆ t : X, RCLike.re (K t t)) * ‖f‖ := by
  refine le_trans (norm_apply_le f x) (mul_le_mul_of_nonneg_right ?_ (norm_nonneg f))
  rw [norm_kernelFun_eq_sqrt (𝕜 := 𝕜) (H := H) x, hKH]
  exact Real.sqrt_le_sqrt (le_ciSup (bddAbove_re_diag hK.continuous) x)

omit [BorelSpace X] in
/-- The `L²(μ)` norm of an RKHS member is controlled by its sup norm:
`∫ ‖f x‖² dμ ≤ μ(X) · (sup_x ‖f x‖)²` — the members of a Mercer RKHS embed in `L²`. -/
theorem integral_normSq_le {K : X → X → 𝕜} (hK : IsMercerKernel 𝕜 K)
    -- USER-INPUT: `H` has reproducing kernel `K`
    (hKH : scalarKernel H = K) (f : H) :
    ∫ x, ‖f x‖ ^ 2 ∂μ ≤ (μ Set.univ).toReal * (⨆ x : X, ‖f x‖) ^ 2 := by
  have hfc : Continuous (f : X → 𝕜) :=
    continuous_coe_of_continuous_scalarKernel (by rw [hKH]; exact hK.continuous) f
  have hbdd : BddAbove (Set.range fun x : X => ‖f x‖) := by
    simpa [Set.image_univ] using isCompact_univ.bddAbove_image hfc.norm.continuousOn
  have hle : ∀ x : X, ‖f x‖ ^ 2 ≤ (⨆ x : X, ‖f x‖) ^ 2 := fun x => by
    have h := le_ciSup hbdd x
    have : (0 : ℝ) ≤ ‖f x‖ := norm_nonneg _
    nlinarith
  calc ∫ x, ‖f x‖ ^ 2 ∂μ ≤ ∫ _x : X, (⨆ x : X, ‖f x‖) ^ 2 ∂μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
          (integrable_const _) (Filter.Eventually.of_forall hle)
    _ = (μ Set.univ).toReal * (⨆ x : X, ‖f x‖) ^ 2 := by
        rw [integral_const, smul_eq_mul, measureReal_def]

end NormComparison

section Separability

/-- **The RKHS of a Mercer kernel is separable**: kernel functions over a countable
dense subset of the compact base space already span densely. -/
theorem separableSpace_of_mercer {K : X → X → 𝕜} (hK : IsMercerKernel 𝕜 K)
    -- USER-INPUT: `H` has reproducing kernel `K`
    (hKH : scalarKernel H = K) :
    TopologicalSpace.SeparableSpace H := by
  sorry

end Separability

section UniformConvergence

omit [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- Finite Cauchy–Schwarz for the off-diagonal partial sums; stated publicly below as
`sq_norm_sum_le`, but needed already for `tendstoUniformly_scalarKernel`. -/
private theorem sq_norm_sum_le_aux {ι : Type*} (e : HilbertBasis ι 𝕜 H) (s : Finset ι)
    (x y : X) :
    ‖∑ i ∈ s, conj ((e i : H) y) * (e i : H) x‖ ^ 2
      ≤ (∑ i ∈ s, ‖(e i : H) x‖ ^ 2) * (∑ i ∈ s, ‖(e i : H) y‖ ^ 2) := by
  have h1 : ‖∑ i ∈ s, conj ((e i : H) y) * (e i : H) x‖
      ≤ ∑ i ∈ s, ‖(e i : H) x‖ * ‖(e i : H) y‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, RCLike.norm_conj, mul_comm]
  have h2 : (∑ i ∈ s, ‖(e i : H) x‖ * ‖(e i : H) y‖) ^ 2
      ≤ (∑ i ∈ s, ‖(e i : H) x‖ ^ 2) * (∑ i ∈ s, ‖(e i : H) y‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq s _ _
  refine le_trans ?_ h2
  gcongr

omit [MeasurableSpace X] [BorelSpace X] in
/-- Dini upgrade on the diagonal: the partial sums of `∑ᵢ ‖eᵢ x‖²` converge to the
continuous limit `re K(x,x)` uniformly on the compact space `X`. -/
theorem tendstoUniformly_diag {K : X → X → 𝕜} (hK : IsMercerKernel 𝕜 K)
    -- USER-INPUT: `H` has reproducing kernel `K`
    (hKH : scalarKernel H = K) {ι : Type*} (e : HilbertBasis ι 𝕜 H) :
    TendstoUniformly
      (fun s : Finset ι => fun x : X => ∑ i ∈ s, ‖(e i : H) x‖ ^ 2)
      (fun x => RCLike.re (K x x)) Filter.atTop := by
  have hKsc : Continuous fun p : X × X => scalarKernel H p.1 p.2 := by
    rw [hKH]; exact hK.continuous
  have hcont : ∀ i : ι, Continuous ((e i : H) : X → 𝕜) := fun i =>
    continuous_coe_of_continuous_scalarKernel hKsc _
  refine Monotone.tendstoUniformly_of_forall_tendsto ?_ ?_ ?_ ?_
  · exact fun s => continuous_finset_sum s fun i _ => ((hcont i).norm).pow 2
  · exact fun s t hst x =>
      Finset.sum_le_sum_of_subset_of_nonneg hst fun i _ _ => by positivity
  · exact RCLike.continuous_re.comp'
      (hK.continuous.comp' (continuous_id.prodMk continuous_id))
  · intro x
    have h := hasSum_scalarKernel_self e x
    rw [hKH] at h
    exact h

omit [MeasurableSpace X] [BorelSpace X] in
/-- **Uniform absolute convergence of the basis expansion of a Mercer kernel**: the
partial sums of `∑ᵢ conj (eᵢ y) eᵢ x` converge to `K` uniformly on `X × X`. -/
theorem tendstoUniformly_scalarKernel {K : X → X → 𝕜} (hK : IsMercerKernel 𝕜 K)
    -- USER-INPUT: `H` has reproducing kernel `K`
    (hKH : scalarKernel H = K) {ι : Type*} (e : HilbertBasis ι 𝕜 H) :
    TendstoUniformly
      (fun s : Finset ι => fun p : X × X => ∑ i ∈ s, conj ((e i : H) p.2) * (e i : H) p.1)
      (fun p => K p.1 p.2) Filter.atTop := by
  classical
  have hpart : ∀ (z : X) (u : Finset ι),
      ∑ i ∈ u, ‖(e i : H) z‖ ^ 2 ≤ RCLike.re (K z z) := by
    intro z u
    have h := hasSum_scalarKernel_self e z
    rw [hKH] at h
    exact sum_le_hasSum u (fun i _ => by positivity) h
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hδ0 : (0 : ℝ) < ε / 2 := by positivity
  have hdiag := (Metric.tendstoUniformly_iff.mp (tendstoUniformly_diag hK hKH e)) _ hδ0
  obtain ⟨s₀, hs₀⟩ := Filter.eventually_atTop.mp hdiag
  refine Filter.eventually_atTop.mpr ⟨s₀, fun s hs p => ?_⟩
  obtain ⟨x, y⟩ := p
  have hsum : HasSum (fun i => conj ((e i : H) y) * (e i : H) x) (K x y) := by
    have h := hasSum_scalarKernel e x y
    rw [hKH] at h
    exact h
  -- uniform tail bound on the diagonal partial sums, from Dini and monotonicity
  have htail : ∀ (z : X) (t : Finset ι), s ⊆ t →
      ∑ i ∈ t \ s, ‖(e i : H) z‖ ^ 2 ≤ ε / 2 := by
    intro z t hst
    have h1 : ∑ i ∈ t \ s, ‖(e i : H) z‖ ^ 2 + ∑ i ∈ s, ‖(e i : H) z‖ ^ 2
        = ∑ i ∈ t, ‖(e i : H) z‖ ^ 2 := Finset.sum_sdiff hst
    have h2 := hpart z t
    have h3 := hs₀ s hs z
    rw [Real.dist_eq] at h3
    have h4 := abs_lt.mp h3
    linarith [h4.1, h4.2]
  -- Cauchy–Schwarz turns it into a tail bound for the off-diagonal partial sums
  have hkey : ∀ t : Finset ι, s ⊆ t →
      ‖(∑ i ∈ t, conj ((e i : H) y) * (e i : H) x)
        - ∑ i ∈ s, conj ((e i : H) y) * (e i : H) x‖ ≤ ε / 2 := by
    intro t hst
    have hsplit : (∑ i ∈ t, conj ((e i : H) y) * (e i : H) x)
        - ∑ i ∈ s, conj ((e i : H) y) * (e i : H) x
        = ∑ i ∈ t \ s, conj ((e i : H) y) * (e i : H) x := by
      rw [← Finset.sum_sdiff hst]; ring
    rw [hsplit]
    have hcs := sq_norm_sum_le_aux e (t \ s) x y
    have hx := htail x t hst
    have hy := htail y t hst
    have hnx : (0 : ℝ) ≤ ∑ i ∈ t \ s, ‖(e i : H) x‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => by positivity
    have hny : (0 : ℝ) ≤ ∑ i ∈ t \ s, ‖(e i : H) y‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => by positivity
    nlinarith [norm_nonneg (∑ i ∈ t \ s, conj ((e i : H) y) * (e i : H) x)]
  have ht : Filter.Tendsto
      (fun t : Finset ι => ∑ i ∈ t, conj ((e i : H) y) * (e i : H) x)
      Filter.atTop (nhds (K x y)) := hsum
  have hlim : Filter.Tendsto
      (fun t : Finset ι => ‖(∑ i ∈ t, conj ((e i : H) y) * (e i : H) x)
        - ∑ i ∈ s, conj ((e i : H) y) * (e i : H) x‖)
      Filter.atTop
      (nhds ‖K x y - ∑ i ∈ s, conj ((e i : H) y) * (e i : H) x‖) :=
    (ht.sub tendsto_const_nhds).norm
  have hfin : ‖K x y - ∑ i ∈ s, conj ((e i : H) y) * (e i : H) x‖ ≤ ε / 2 :=
    le_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨s, fun t hst => hkey t hst⟩)
  rw [dist_eq_norm]
  linarith

omit [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
/-- Tail bound by Cauchy–Schwarz: partial sums of the expansion off the diagonal are
dominated through the diagonal tails,
`‖∑_{i ∈ s} conj (eᵢ y) eᵢ x‖² ≤ (∑_{i ∈ s} ‖eᵢ x‖²) (∑_{i ∈ s} ‖eᵢ y‖²)`. -/
theorem sq_norm_sum_le {ι : Type*} (e : HilbertBasis ι 𝕜 H) (s : Finset ι) (x y : X) :
    ‖∑ i ∈ s, conj ((e i : H) y) * (e i : H) x‖ ^ 2
      ≤ (∑ i ∈ s, ‖(e i : H) x‖ ^ 2) * (∑ i ∈ s, ‖(e i : H) y‖ ^ 2) :=
  sq_norm_sum_le_aux e s x y

end UniformConvergence

section OperatorProperties

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] [IsFiniteMeasure μ] in
/-- The squared `L²` norm as an integral of the squared pointwise norm. -/
private theorem norm_Lp_sq (f : Lp 𝕜 2 μ) :
    ‖f‖ ^ 2 = ∫ a, ‖(f : X → 𝕜) a‖ ^ 2 ∂μ := by
  have h : (inner 𝕜 f f : 𝕜) = ((∫ a, ‖(f : X → 𝕜) a‖ ^ 2 ∂μ : ℝ) : 𝕜) := by
    rw [L2.inner_def, ← integral_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    simp only [inner_self_eq_norm_sq_to_K]
    push_cast
    ring
  rw [norm_sq_eq_re_inner (𝕜 := 𝕜) f, h, RCLike.ofReal_re]

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] [IsFiniteMeasure μ] in
/-- The `L²` norm of the class of a square-integrable function. -/
private theorem norm_toLp_eq_sqrt {F : X → 𝕜} (hF : MemLp F 2 μ) :
    ‖hF.toLp F‖ = Real.sqrt (∫ y, ‖F y‖ ^ 2 ∂μ) := by
  have h : ‖hF.toLp F‖ ^ 2 = ∫ y, ‖F y‖ ^ 2 ∂μ := by
    rw [norm_Lp_sq]
    exact integral_congr_ae ((hF.coeFn_toLp).mono fun y hy => by simp only [hy])
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

omit [MetricSpace X] [CompactSpace X] [BorelSpace X] [IsFiniteMeasure μ] in
/-- Cauchy–Schwarz for a single integral pairing:
`‖∫ F g dμ‖ ≤ ‖F‖_{L²} ‖g‖_{L²}`. -/
private theorem norm_integral_mul_le {F : X → 𝕜} (hF : MemLp F 2 μ) (g : Lp 𝕜 2 μ) :
    ‖∫ y, F y * (g : X → 𝕜) y ∂μ‖ ≤ Real.sqrt (∫ y, ‖F y‖ ^ 2 ∂μ) * ‖g‖ := by
  have hS : IsL2Symbol μ (fun _ : Unit => F) := fun _ => hF
  have h := norm_integralOp_le (fun _ : Unit => F) hS g ()
  have hnorm : ‖symbolConjLp μ (fun _ : Unit => F) hS ()‖
      = Real.sqrt (∫ y, ‖F y‖ ^ 2 ∂μ) := by
    rw [symbolConjLp, norm_toLp_eq_sqrt]
    simp
  rwa [hnorm] at h

omit [MeasurableSpace X] [BorelSpace X] in
/-- Uniform bound on a continuous kernel over the compact square. -/
private theorem exists_bnd {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x y : X, ‖K x y‖ ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn
    (f := fun p : X × X => K p.1 p.2) hKc.continuousOn
  exact ⟨max M 0, le_max_right _ _,
    fun x y => le_trans (hM (x, y) (Set.mem_univ _)) (le_max_left _ _)⟩

/-- Continuity of the squared `L²` norm of the sections of a continuous kernel. -/
private theorem continuous_integral_normSq_section {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2) :
    Continuous fun x : X => ∫ y, ‖K x y‖ ^ 2 ∂μ := by
  obtain ⟨M, hM0, hM⟩ := exists_bnd hKc
  refine continuous_of_dominated (bound := fun _ : X => M ^ 2) ?_ ?_ (integrable_const _) ?_
  · exact fun x => ((hKc.comp' (continuous_const.prodMk continuous_id)).norm.pow
      2).aestronglyMeasurable
  · intro x
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hM x y) 2
  · filter_upwards with y
    exact ((hKc.comp' (continuous_id.prodMk continuous_const)).norm.pow 2)

/-- `‖T_K‖` is bounded by the `L²(μ × μ)` norm of the kernel. -/
theorem norm_mercerCLM_le {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2) :
    ‖mercerCLM μ hKc‖
      ≤ Real.sqrt (∫ x, ∫ y, ‖K x y‖ ^ 2 ∂μ ∂μ) := by
  have hsec : ∀ x : X, (0 : ℝ) ≤ ∫ y, ‖K x y‖ ^ 2 ∂μ :=
    fun x => integral_nonneg fun y => by positivity
  have hA : (0 : ℝ) ≤ ∫ x, ∫ y, ‖K x y‖ ^ 2 ∂μ ∂μ := integral_nonneg hsec
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun g => ?_
  have hint : Integrable (fun x : X => (∫ y, ‖K x y‖ ^ 2 ∂μ) * ‖g‖ ^ 2) μ := by
    obtain ⟨M, hM0, hM⟩ := exists_bnd hKc
    refine Integrable.mono' (g := fun _ : X => ((μ Set.univ).toReal * M ^ 2) * ‖g‖ ^ 2)
      (integrable_const _)
      ((continuous_integral_normSq_section (μ := μ) hKc).aestronglyMeasurable.mul_const _) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc ∫ y, ‖K x y‖ ^ 2 ∂μ ≤ ∫ _y : X, M ^ 2 ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => by positivity)
            (integrable_const _)
            (Filter.Eventually.of_forall fun y => pow_le_pow_left₀ (norm_nonneg _) (hM x y) 2)
      _ = (μ Set.univ).toReal * M ^ 2 := by rw [integral_const, smul_eq_mul, measureReal_def]
  have hsq : ‖mercerCLM μ hKc g‖ ^ 2 ≤ (∫ x, ∫ y, ‖K x y‖ ^ 2 ∂μ ∂μ) * ‖g‖ ^ 2 := by
    rw [norm_Lp_sq]
    have h1 : ∫ x, ‖(mercerCLM μ hKc g : X → 𝕜) x‖ ^ 2 ∂μ
        = ∫ x, ‖integralOp μ K g x‖ ^ 2 ∂μ :=
      integral_congr_ae ((mercerCLM_coeFn_ae hKc g).mono fun x hx => by simp only [hx])
    rw [h1]
    calc ∫ x, ‖integralOp μ K g x‖ ^ 2 ∂μ
        ≤ ∫ x, (∫ y, ‖K x y‖ ^ 2 ∂μ) * ‖g‖ ^ 2 ∂μ := by
          refine integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun x => by positivity) hint
            (Filter.Eventually.of_forall fun x => ?_)
          have h : ‖integralOp μ K g x‖ ≤ Real.sqrt (∫ y, ‖K x y‖ ^ 2 ∂μ) * ‖g‖ :=
            norm_integral_mul_le (isL2Symbol_of_continuous hKc x) g
          have hs := Real.sq_sqrt (hsec x)
          change ‖integralOp μ K g x‖ ^ 2 ≤ (∫ y, ‖K x y‖ ^ 2 ∂μ) * ‖g‖ ^ 2
          calc ‖integralOp μ K g x‖ ^ 2
              ≤ (Real.sqrt (∫ y, ‖K x y‖ ^ 2 ∂μ) * ‖g‖) ^ 2 :=
                pow_le_pow_left₀ (norm_nonneg _) h 2
            _ = (∫ y, ‖K x y‖ ^ 2 ∂μ) * ‖g‖ ^ 2 := by rw [mul_pow, hs]
      _ = (∫ x, ∫ y, ‖K x y‖ ^ 2 ∂μ ∂μ) * ‖g‖ ^ 2 := integral_mul_const _ _
  calc ‖mercerCLM μ hKc g‖ = Real.sqrt (‖mercerCLM μ hKc g‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((∫ x, ∫ y, ‖K x y‖ ^ 2 ∂μ ∂μ) * ‖g‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (∫ x, ∫ y, ‖K x y‖ ^ 2 ∂μ ∂μ) * ‖g‖ := by
        rw [Real.sqrt_mul hA, Real.sqrt_sq (norm_nonneg _)]

/-- Functions in the range of `T_K` (pointwise version) are continuous. -/
theorem continuous_integralOp_of_continuous {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2) (g : Lp 𝕜 2 μ) :
    Continuous (integralOp μ K g) := by
  obtain ⟨M, hM0, hM⟩ := exists_bnd hKc
  have hgi : Integrable (g : X → 𝕜) μ := (Lp.memLp g).integrable (by norm_num)
  refine continuous_of_dominated (bound := fun y => M * ‖(g : X → 𝕜) y‖) ?_ ?_ ?_ ?_
  · exact fun x =>
      ((hKc.comp' (continuous_const.prodMk continuous_id)).aestronglyMeasurable).mul
        (Lp.aestronglyMeasurable g)
  · intro x
    filter_upwards with y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hM x y) (norm_nonneg _)
  · exact hgi.norm.const_mul M
  · filter_upwards with y
    exact (hKc.comp' (continuous_id.prodMk continuous_const)).mul continuous_const

/-- Two continuous symbols that are uniformly `η`-close have `μ(X)·η`-close integral
operators (pointwise on `L²`). -/
private theorem norm_mercerCLM_sub_apply_le {K₁ K₂ : X → X → 𝕜}
    (h₁ : Continuous fun p : X × X => K₁ p.1 p.2)
    (h₂ : Continuous fun p : X × X => K₂ p.1 p.2)
    {η : ℝ} (hη0 : 0 ≤ η) (hη : ∀ x y, ‖K₁ x y - K₂ x y‖ ≤ η) (g : Lp 𝕜 2 μ) :
    ‖mercerCLM μ h₁ g - mercerCLM μ h₂ g‖ ≤ (μ Set.univ).toReal * η * ‖g‖ := by
  have hμ0 : (0 : ℝ) ≤ (μ Set.univ).toReal := ENNReal.toReal_nonneg
  have hpt : ∀ᵐ x ∂μ, ‖((mercerCLM μ h₁ g - mercerCLM μ h₂ g : Lp 𝕜 2 μ) : X → 𝕜) x‖
      ≤ Real.sqrt ((μ Set.univ).toReal) * η * ‖g‖ := by
    filter_upwards [Lp.coeFn_sub (mercerCLM μ h₁ g) (mercerCLM μ h₂ g),
      mercerCLM_coeFn_ae h₁ g, mercerCLM_coeFn_ae h₂ g] with x hx hx1 hx2
    rw [hx]
    simp only [Pi.sub_apply, hx1, hx2]
    have hF : MemLp (fun y => K₁ x y - K₂ x y) 2 μ :=
      (isL2Symbol_of_continuous h₁ x).sub (isL2Symbol_of_continuous h₂ x)
    have hd : integralOp μ K₁ g x - integralOp μ K₂ g x
        = ∫ y, (K₁ x y - K₂ x y) * (g : X → 𝕜) y ∂μ := by
      have i1 : Integrable (fun y => K₁ x y * (g : X → 𝕜) y) μ :=
        (isL2Symbol_of_continuous h₁ x).integrable_mul (Lp.memLp _)
      have i2 : Integrable (fun y => K₂ x y * (g : X → 𝕜) y) μ :=
        (isL2Symbol_of_continuous h₂ x).integrable_mul (Lp.memLp _)
      rw [integralOp, integralOp, ← integral_sub i1 i2]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
    rw [hd]
    refine le_trans (norm_integral_mul_le hF g) ?_
    have hb : ∫ y, ‖K₁ x y - K₂ x y‖ ^ 2 ∂μ ≤ (μ Set.univ).toReal * η ^ 2 := by
      calc ∫ y, ‖K₁ x y - K₂ x y‖ ^ 2 ∂μ ≤ ∫ _y : X, η ^ 2 ∂μ :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => by positivity)
              (integrable_const _)
              (Filter.Eventually.of_forall fun y => pow_le_pow_left₀ (norm_nonneg _) (hη x y) 2)
        _ = (μ Set.univ).toReal * η ^ 2 := by
            rw [integral_const, smul_eq_mul, measureReal_def]
    have h2 : Real.sqrt ((μ Set.univ).toReal * η ^ 2)
        = Real.sqrt ((μ Set.univ).toReal) * η := by
      rw [Real.sqrt_mul hμ0, Real.sqrt_sq hη0]
    have h1 := (Real.sqrt_le_sqrt hb).trans_eq h2
    nlinarith [norm_nonneg g, Real.sqrt_nonneg (∫ y, ‖K₁ x y - K₂ x y‖ ^ 2 ∂μ)]
  have hsq : ‖mercerCLM μ h₁ g - mercerCLM μ h₂ g‖ ^ 2
      ≤ ((μ Set.univ).toReal * η * ‖g‖) ^ 2 := by
    rw [norm_Lp_sq]
    calc ∫ x, ‖((mercerCLM μ h₁ g - mercerCLM μ h₂ g : Lp 𝕜 2 μ) : X → 𝕜) x‖ ^ 2 ∂μ
        ≤ ∫ _x : X, (Real.sqrt ((μ Set.univ).toReal) * η * ‖g‖) ^ 2 ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
            (integrable_const _) (hpt.mono fun x hx => by
              exact pow_le_pow_left₀ (norm_nonneg _) hx 2)
      _ = (μ Set.univ).toReal * (Real.sqrt ((μ Set.univ).toReal) * η * ‖g‖) ^ 2 := by
          rw [integral_const, smul_eq_mul, measureReal_def]
      _ = ((μ Set.univ).toReal * η * ‖g‖) ^ 2 := by
          have hs : Real.sqrt ((μ Set.univ).toReal) ^ 2 = (μ Set.univ).toReal :=
            Real.sq_sqrt hμ0
          linear_combination ((μ Set.univ).toReal * η ^ 2 * ‖g‖ ^ 2) * hs
  calc ‖mercerCLM μ h₁ g - mercerCLM μ h₂ g‖
      = Real.sqrt (‖mercerCLM μ h₁ g - mercerCLM μ h₂ g‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (((μ Set.univ).toReal * η * ‖g‖) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = (μ Set.univ).toReal * η * ‖g‖ :=
        Real.sqrt_sq (mul_nonneg (mul_nonneg hμ0 hη0) (norm_nonneg _))

/-- **`T_K` is a positive operator** when `K` is a Mercer kernel. -/
theorem isPositive_mercerCLM {K : X → X → 𝕜} (hK : IsMercerKernel 𝕜 K) :
    (mercerCLM μ hK.continuous).IsPositive := by
  sorry

/-- **Converse**: for `μ` of full support, a continuous Hermitian function with positive
integral operator is positive semidefinite, hence a Mercer kernel.  (Averaging the
quadratic form over shrinking neighborhoods of the points.) -/
theorem isMercerKernel_of_isPositive {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2)
    -- USER-INPUT: Hermitian symmetry of `K`
    (hsym : ∀ x y, conj (K x y) = K y x)
    -- USER-INPUT: the measure has full support
    [μ.IsOpenPosMeasure]
    -- USER-INPUT: positivity of the integral operator
    (hpos : (mercerCLM μ hKc).IsPositive) :
    IsMercerKernel 𝕜 K := by
  sorry

/-- **Equicontinuity of the image of the unit ball**: `{T_K g : ‖g‖ ≤ 1}` is uniformly
equicontinuous on `X` (via uniform continuity of `K` on the compact square). -/
theorem equicontinuous_integralOp {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2) :
    Equicontinuous fun g : Metric.closedBall (0 : Lp 𝕜 2 μ) 1 =>
      integralOp μ K (g : Lp 𝕜 2 μ) := by
  have hL2 := isL2Symbol_of_continuous (μ := μ) hKc
  intro x₀
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  have hC0 : (0 : ℝ) ≤ Real.sqrt ((μ Set.univ).toReal) := Real.sqrt_nonneg _
  have hη0 : (0 : ℝ) < ε / (Real.sqrt ((μ Set.univ).toReal) + 1) := by positivity
  have huc : UniformContinuous fun p : X × X => K p.1 p.2 :=
    CompactSpace.uniformContinuous_of_continuous hKc
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuous_iff.mp huc _ hη0
  refine ⟨δ, hδ0, fun x hx g => ?_⟩
  set η := ε / (Real.sqrt ((μ Set.univ).toReal) + 1) with hηdef
  -- the sections differ by less than `η` uniformly in `y`
  have hpt : ∀ y : X, ‖K x₀ y - K x y‖ ≤ η := by
    intro y
    have hd : dist ((x₀, y) : X × X) (x, y) < δ := by
      rw [Prod.dist_eq]
      simpa [dist_comm] using hx
    have := hδ hd
    rw [dist_eq_norm] at this
    exact this.le
  have hFm : MemLp (fun y => K x₀ y - K x y) 2 μ := (hL2 x₀).sub (hL2 x)
  have hgle : ‖(g : Lp 𝕜 2 μ)‖ ≤ 1 := by
    have := g.2
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this
  -- the difference of the two values is a single integral pairing
  have hsub : integralOp μ K (g : Lp 𝕜 2 μ) x₀ - integralOp μ K (g : Lp 𝕜 2 μ) x
      = ∫ y, (K x₀ y - K x y) * ((g : Lp 𝕜 2 μ) : X → 𝕜) y ∂μ := by
    have h₀ : Integrable (fun y => K x₀ y * ((g : Lp 𝕜 2 μ) : X → 𝕜) y) μ :=
      (hL2 x₀).integrable_mul (Lp.memLp _)
    have h₁ : Integrable (fun y => K x y * ((g : Lp 𝕜 2 μ) : X → 𝕜) y) μ :=
      (hL2 x).integrable_mul (Lp.memLp _)
    rw [integralOp, integralOp, ← integral_sub h₀ h₁]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
  -- Cauchy–Schwarz plus the uniform bound on the sections
  have hnormle : ‖∫ y, (K x₀ y - K x y) * ((g : Lp 𝕜 2 μ) : X → 𝕜) y ∂μ‖
      ≤ Real.sqrt ((μ Set.univ).toReal) * η := by
    refine le_trans (norm_integral_mul_le hFm _) ?_
    have hb : ∫ y, ‖K x₀ y - K x y‖ ^ 2 ∂μ ≤ (μ Set.univ).toReal * η ^ 2 := by
      calc ∫ y, ‖K x₀ y - K x y‖ ^ 2 ∂μ ≤ ∫ _y : X, η ^ 2 ∂μ :=
            integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => by positivity)
              (integrable_const _)
              (Filter.Eventually.of_forall fun y =>
                pow_le_pow_left₀ (norm_nonneg _) (hpt y) 2)
        _ = (μ Set.univ).toReal * η ^ 2 := by
            rw [integral_const, smul_eq_mul, measureReal_def]
    have h1 : Real.sqrt (∫ y, ‖K x₀ y - K x y‖ ^ 2 ∂μ)
        ≤ Real.sqrt ((μ Set.univ).toReal * η ^ 2) := Real.sqrt_le_sqrt hb
    have h2 : Real.sqrt ((μ Set.univ).toReal * η ^ 2)
        = Real.sqrt ((μ Set.univ).toReal) * η := by
      rw [Real.sqrt_mul ENNReal.toReal_nonneg, Real.sqrt_sq hη0.le]
    nlinarith [Real.sqrt_nonneg (∫ y, ‖K x₀ y - K x y‖ ^ 2 ∂μ), norm_nonneg (g : Lp 𝕜 2 μ)]
  have hfin : dist (integralOp μ K (g : Lp 𝕜 2 μ) x₀) (integralOp μ K (g : Lp 𝕜 2 μ) x)
      ≤ Real.sqrt ((μ Set.univ).toReal) * η := by
    rw [dist_eq_norm, hsub]
    exact hnormle
  refine lt_of_le_of_lt hfin ?_
  rw [hηdef]
  rw [mul_div_assoc']
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [hε, hC0]

/-- Pointwise boundedness of the image of the unit ball:
`‖T_K g (x)‖ ≤ √(∫ ‖K(x,y)‖² dμ(y))` for `‖g‖ ≤ 1`. -/
theorem norm_integralOp_le_of_mem_ball {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2) {g : Lp 𝕜 2 μ}
    (hg : ‖g‖ ≤ 1) (x : X) :
    ‖integralOp μ K g x‖ ≤ Real.sqrt (∫ y, ‖K x y‖ ^ 2 ∂μ) := by
  refine le_trans (norm_integral_mul_le (isL2Symbol_of_continuous hKc x) g) ?_
  nlinarith [Real.sqrt_nonneg (∫ y, ‖K x y‖ ^ 2 ∂μ), norm_nonneg g]

end OperatorProperties

end StatLean.NonparametricStatistics
