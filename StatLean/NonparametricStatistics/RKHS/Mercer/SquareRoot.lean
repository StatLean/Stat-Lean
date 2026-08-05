import StatLean.NonparametricStatistics.RKHS.Mercer.Theorem
import StatLean.NonparametricStatistics.RKHS.RangeSpace
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The square root of a Mercer operator and the RKHS `H(K)`

Let `K` be a Mercer kernel with eigensystem `{(eₙ, λₙ)}` against a full-support finite
Borel measure `μ`.  The **square-root symbol** `S(x,y) = ∑ₙ √λₙ eₙ(x) conj (eₙ(y))`
(convergent in `L²` sense in each variable, though generally not continuous) defines a
bounded positive integral operator `T_S` with `T_S² = T_K`, and it exhibits the measure-
independent RKHS `H(K)` as a range space:

* `range T_S = H(K)` (as sets of functions on `X`), and `T_S` is an isometry of
  `(ker T_K)ᗮ` onto `H(K)`;
* `{√λₙ eₙ}` is an orthonormal basis of `H(K)`;
* `H(K)` consists exactly of the sums `∑ₙ aₙ eₙ` with `∑ₙ |aₙ|²/λₙ < ∞`.

Also here: `T_K²` is the integral operator with symbol the box product `K □ K`, and
`(∫ K(t,t) dμ)·K − K □ K` is again a Mercer kernel, whence `range T_K ⊆ H(K)`.

**Bibliographic comments.** The square-root factorization of Mercer operators and the
spectral description of `H(K)` are classical; see H. König, *Eigenvalue Distribution of
Compact Operators* (Birkhäuser, 1986), and E. Parzen, *Statistical inference on time
series by Hilbert space methods* (1959) for the statistical reading.
-/

open RKHS ComplexConjugate MeasureTheory
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X]
variable {μ : Measure X} [IsFiniteMeasure μ]

section BoxSquare

omit [MeasurableSpace X] [BorelSpace X] in
/-- Uniform bound on a continuous kernel over the compact square. -/
private theorem exists_bnd {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x y : X, ‖K x y‖ ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn
    (f := fun p : X × X => K p.1 p.2) hKc.continuousOn
  exact ⟨max M 0, le_max_right _ _,
    fun x y => le_trans (hM (x, y) (Set.mem_univ _)) (le_max_left _ _)⟩

/-- The box square of a continuous symbol on a compact space is continuous. -/
theorem continuous_boxProd {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2) :
    Continuous fun p : X × X => boxProd μ K K p.1 p.2 := by
  obtain ⟨M, hM0, hM⟩ := exists_bnd hKc
  refine continuous_of_dominated (bound := fun _ : X => M * M) ?_ ?_ (integrable_const _) ?_
  · intro p
    exact (((hKc.comp' (continuous_const.prodMk continuous_id))).mul
      (hKc.comp' (continuous_id.prodMk continuous_const))).aestronglyMeasurable
  · intro p
    filter_upwards with t
    rw [norm_mul]
    exact mul_le_mul (hM _ _) (hM _ _) (norm_nonneg _) hM0
  · filter_upwards with t
    exact (hKc.comp' (continuous_fst.prodMk continuous_const)).mul
      (hKc.comp' (continuous_const.prodMk continuous_snd))


/-- **`T_K²` is the integral operator with symbol `K □ K`.** -/
theorem mercerCLM_comp_self {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2) :
    (mercerCLM μ hKc).comp (mercerCLM μ hKc)
      = mercerCLM (K := boxProd μ K K) μ (continuous_boxProd (μ := μ) hKc) := by
  obtain ⟨M, hM0, hM⟩ := exists_bnd hKc
  refine ContinuousLinearMap.ext fun g => ?_
  refine Lp.ext ?_
  filter_upwards [mercerCLM_coeFn_ae hKc (mercerCLM μ hKc g),
    mercerCLM_coeFn_ae (K := boxProd μ K K) (continuous_boxProd (μ := μ) hKc) g] with x h1 h2
  rw [ContinuousLinearMap.comp_apply, h1, h2]
  have hg1 : Integrable (fun z => (g : X → 𝕜) z) μ := (Lp.memLp g).integrable (by norm_num)
  have hstep1 : integralOp μ K (mercerCLM μ hKc g) x
      = ∫ y, K x y * (∫ z, K y z * (g : X → 𝕜) z ∂μ) ∂μ := by
    rw [integralOp]
    refine integral_congr_ae ?_
    filter_upwards [mercerCLM_coeFn_ae hKc g] with y hy
    rw [hy, integralOp]
  have hint : Integrable (Function.uncurry fun y z => K x y * K y z * (g : X → 𝕜) z)
      (μ.prod μ) := by
    have hg2 : Integrable (fun p : X × X => (g : X → 𝕜) p.2) (μ.prod μ) :=
      MeasureTheory.Integrable.comp_snd hg1 μ
    refine hg2.bdd_mul (c := M * M) ?_ ?_
    · exact ((hKc.comp' (continuous_const.prodMk continuous_fst)).mul
        (hKc.comp' (continuous_fst.prodMk continuous_snd))).aestronglyMeasurable
    · filter_upwards with p
      rw [norm_mul]
      exact mul_le_mul (hM _ _) (hM _ _) (norm_nonneg _) hM0
  have hswap : ∫ y, K x y * (∫ z, K y z * (g : X → 𝕜) z ∂μ) ∂μ
      = ∫ z, (∫ y, K x y * K y z ∂μ) * (g : X → 𝕜) z ∂μ := by
    have h1' : ∫ y, K x y * (∫ z, K y z * (g : X → 𝕜) z ∂μ) ∂μ
        = ∫ y, ∫ z, K x y * K y z * (g : X → 𝕜) z ∂μ ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      have e := integral_const_mul (μ := μ) (K x y) (fun z => K y z * (g : X → 𝕜) z)
      change K x y * (∫ z, K y z * (g : X → 𝕜) z ∂μ) = ∫ z, K x y * K y z * (g : X → 𝕜) z ∂μ
      rw [← e]
      exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
    rw [h1', integral_integral_swap hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    have e := integral_mul_const (μ := μ) ((g : X → 𝕜) z) (fun y => K x y * K y z)
    change (∫ y, K x y * K y z * (g : X → 𝕜) z ∂μ) = (∫ y, K x y * K y z ∂μ) * (g : X → 𝕜) z
    rw [← e]
  rw [hstep1, hswap, integralOp]
  rfl

/-- A continuous function on a compact space is integrable against a finite measure. -/
private theorem integrable_of_cont {f : X → 𝕜} (hf : Continuous f) : Integrable f μ := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact memLp_one_iff_integrable.mp
    (MemLp.of_bound hf.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun x => hM x (Set.mem_univ _)))

/-- **`(∫ K(t,t) dμ) · K − K □ K` is a Mercer kernel** (Cholesky-style domination of the
box square by the trace multiple of `K`). -/
theorem isMercerKernel_trace_smul_sub_boxProd {K : X → X → 𝕜}
    (hK : IsMercerKernel 𝕜 K) :
    IsMercerKernel 𝕜 fun x y =>
      ((∫ t, RCLike.re (K t t) ∂μ : ℝ) : 𝕜) * K x y - boxProd μ K K x y := by
  have hcont : Continuous fun p : X × X =>
      ((∫ t, RCLike.re (K t t) ∂μ : ℝ) : 𝕜) * K p.1 p.2 - boxProd μ K K p.1 p.2 :=
    (continuous_const.mul hK.continuous).sub (continuous_boxProd (μ := μ) hK.continuous)
  -- the diagonal of `K` is real, so the trace constant is the integral of `K t t`
  have hreal : ∀ t : X, ((RCLike.re (K t t) : ℝ) : 𝕜) = K t t := fun t =>
    RCLike.conj_eq_iff_re.mp (hK.isKernelFun.conj_symm t t)
  have htrace : ((∫ t, RCLike.re (K t t) ∂μ : ℝ) : 𝕜) = ∫ t, K t t ∂μ := by
    rw [← integral_ofReal]
    exact integral_congr_ae (Filter.Eventually.of_forall hreal)
  -- the kernel is a `t`-integral of the elementary Cholesky kernels
  have hpt : ∀ x y : X,
      ((∫ t, RCLike.re (K t t) ∂μ : ℝ) : 𝕜) * K x y - boxProd μ K K x y
        = ∫ t, (K t t * K x y - K x t * K t y) ∂μ := by
    intro x y
    have i1 : Integrable (fun t => K t t * K x y) μ :=
      integrable_of_cont ((hK.continuous.comp' (continuous_id.prodMk continuous_id)).mul
        continuous_const)
    have i2 : Integrable (fun t => K x t * K t y) μ :=
      integrable_of_cont ((hK.continuous.comp' (continuous_const.prodMk continuous_id)).mul
        (hK.continuous.comp' (continuous_id.prodMk continuous_const)))
    rw [integral_sub i1 i2, htrace, boxProd, integral_mul_const]
  refine ⟨hcont, ⟨fun x y => ?_, fun n x a => ?_⟩⟩
  · rw [hpt, hpt, ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [map_sub, map_mul, hK.isKernelFun.conj_symm]
    ring
  · obtain ⟨H₀, _, _, _, _, hKH⟩ := hK.isKernelFun.exists_rkhs
    have hker : ∀ p q : X, K p q = ⟪kernelFun H₀ p, kernelFun H₀ q⟫_𝕜 := by
      intro p q
      rw [← hKH, scalarKernel_eq_inner]
    set v : H₀ := ∑ j, a j • kernelFun H₀ (x j) with hv
    have hsum1 : (∑ i, ∑ j, conj (a i) * a j * K (x i) (x j)) = ⟪v, v⟫_𝕜 := by
      have key : (∑ i, ∑ j, conj (a i) * a j * ⟪kernelFun H₀ (x i), kernelFun H₀ (x j)⟫_𝕜)
          = ⟪∑ i, a i • kernelFun H₀ (x i), ∑ j, a j • kernelFun H₀ (x j)⟫_𝕜 := by
        rw [sum_inner]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [inner_smul_left, inner_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [inner_smul_right]; ring
      simp_rw [hker]
      rw [key, hv]
    have hsum2 : ∀ t : X, (∑ i, ∑ j, conj (a i) * a j * (K (x i) t * K t (x j)))
        = ⟪v, kernelFun H₀ t⟫_𝕜 * ⟪kernelFun H₀ t, v⟫_𝕜 := by
      intro t
      have key : ⟪v, kernelFun H₀ t⟫_𝕜 * ⟪kernelFun H₀ t, v⟫_𝕜
          = (∑ i, conj (a i) * ⟪kernelFun H₀ (x i), kernelFun H₀ t⟫_𝕜) *
            (∑ j, a j * ⟪kernelFun H₀ t, kernelFun H₀ (x j)⟫_𝕜) := by
        rw [hv, sum_inner, inner_sum]
        congr 1
        · exact Finset.sum_congr rfl fun i _ => inner_smul_left _ _ _
        · exact Finset.sum_congr rfl fun j _ => inner_smul_right _ _ _
      rw [key, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hker, hker]
      ring
    have hcomb : ∀ t : X,
        (∑ i, ∑ j, conj (a i) * a j * (K t t * K (x i) (x j) - K (x i) t * K t (x j)))
          = ((‖kernelFun H₀ t‖ ^ 2 * ‖v‖ ^ 2 - ‖⟪kernelFun H₀ t, v⟫_𝕜‖ ^ 2 : ℝ) : 𝕜) := by
      intro t
      have hstep : (∑ i, ∑ j, conj (a i) * a j * (K t t * K (x i) (x j) - K (x i) t * K t (x j)))
          = K t t * (∑ i, ∑ j, conj (a i) * a j * K (x i) (x j))
            - ∑ i, ∑ j, conj (a i) * a j * (K (x i) t * K t (x j)) := by
        calc (∑ i, ∑ j, conj (a i) * a j * (K t t * K (x i) (x j) - K (x i) t * K t (x j)))
            = ∑ i, ∑ j, (K t t * (conj (a i) * a j * K (x i) (x j))
                - conj (a i) * a j * (K (x i) t * K t (x j))) :=
              Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
          _ = ∑ i, (K t t * (∑ j, conj (a i) * a j * K (x i) (x j))
                - ∑ j, conj (a i) * a j * (K (x i) t * K t (x j))) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Finset.sum_sub_distrib, Finset.mul_sum]
          _ = _ := by rw [Finset.sum_sub_distrib, Finset.mul_sum]
      rw [hstep, hsum1, hsum2 t]
      have h1 : K t t = ((‖kernelFun H₀ t‖ : 𝕜)) ^ 2 := by
        rw [← hKH]; exact scalarKernel_self H₀ t
      have h2 : ⟪v, v⟫_𝕜 = ((‖v‖ : 𝕜)) ^ 2 := inner_self_eq_norm_sq_to_K (𝕜 := 𝕜) v
      have h3 : ⟪v, kernelFun H₀ t⟫_𝕜 * ⟪kernelFun H₀ t, v⟫_𝕜
          = ((‖⟪kernelFun H₀ t, v⟫_𝕜‖ : 𝕜)) ^ 2 := by
        rw [← inner_conj_symm v (kernelFun H₀ t), RCLike.conj_mul]
      rw [h1, h2, h3]
      push_cast
      ring
    -- integrate the elementary quadratic forms
    have hintbl : ∀ i j : Fin n,
        Integrable (fun t => conj (a i) * a j *
          (K t t * K (x i) (x j) - K (x i) t * K t (x j))) μ := by
      intro i j
      refine (integrable_of_cont ?_).const_mul _
      exact ((hK.continuous.comp' (continuous_id.prodMk continuous_id)).mul
        continuous_const).sub
        ((hK.continuous.comp' (continuous_const.prodMk continuous_id)).mul
          (hK.continuous.comp' (continuous_id.prodMk continuous_const)))
    have hfinal : (∑ i, ∑ j, conj (a i) * a j *
        (((∫ t, RCLike.re (K t t) ∂μ : ℝ) : 𝕜) * K (x i) (x j) - boxProd μ K K (x i) (x j)))
        = ((∫ t, (‖kernelFun H₀ t‖ ^ 2 * ‖v‖ ^ 2
            - ‖⟪kernelFun H₀ t, v⟫_𝕜‖ ^ 2) ∂μ : ℝ) : 𝕜) := by
      have e1 : ∀ i j : Fin n, conj (a i) * a j *
          (((∫ t, RCLike.re (K t t) ∂μ : ℝ) : 𝕜) * K (x i) (x j) - boxProd μ K K (x i) (x j))
          = ∫ t, conj (a i) * a j *
              (K t t * K (x i) (x j) - K (x i) t * K t (x j)) ∂μ := by
        intro i j
        rw [hpt, integral_const_mul]
      rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => e1 i j]
      rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
        (integral_finset_sum Finset.univ fun j _ => hintbl i j).symm]
      rw [← integral_finset_sum Finset.univ
        fun i _ => integrable_finset_sum Finset.univ fun j _ => hintbl i j]
      rw [← integral_ofReal]
      exact integral_congr_ae (Filter.Eventually.of_forall hcomb)
    rw [hfinal, RCLike.ofReal_re]
    refine integral_nonneg fun t => ?_
    simp only [Pi.zero_apply]
    have hcs := norm_inner_le_norm (𝕜 := 𝕜) (kernelFun H₀ t) v
    have hsq := mul_self_le_mul_self (norm_nonneg (⟪kernelFun H₀ t, v⟫_𝕜)) hcs
    nlinarith [hsq, norm_nonneg (kernelFun H₀ t), norm_nonneg v]


end BoxSquare

section SquareRoot

variable {K : X → X → 𝕜} {hKc : Continuous fun p : X × X => K p.1 p.2}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
variable [RKHS 𝕜 H X 𝕜]

variable (d : MercerEigensystem μ K hKc)

/-- The **square-root symbol** `S(x, y) = ∑ₙ √λₙ eₙ(x) conj (eₙ(y))` of a Mercer
eigensystem (pointwise unordered sum; `0` where the series fails to converge — it
converges for a.e. pair, and everywhere in the `y`-section `L²` sense used below). -/
noncomputable def sqrtSymbol : X → X → 𝕜 := fun x y =>
  ∑' n, ((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * (d.eigfun n x * conj (d.eigfun n y))

/-- The square-root symbol has square-integrable sections:
`∫ ‖S(x,y)‖² dμ(y) = ∑ₙ λₙ ‖eₙ(x)‖² = K(x,x)`. -/
-- OPEN.  Every statement of this section is downstream of the (still open) kernel
-- expansion `MercerEigensystem.hasSum_kernel` in `Mercer/Theorem.lean`: without it the
-- eigen-family `{eₙ}` is not known to expand `K`, so nothing pins down `sqrtSymbol`.
-- Here specifically: `∫ ‖S(x,y)‖² dμ(y) = ∑ₙ λₙ ‖eₙ(x)‖²` by Parseval against the
-- orthonormal family `d.orthonormal`, and the right-hand side is `re K(x,x)` by the
-- diagonal case of `hasSum_kernel`.  (Measurability of `sqrtSymbol d x` also has to be
-- extracted from the `tsum`, e.g. as an a.e.-limit of the continuous partial sums.)
theorem isL2Symbol_sqrtSymbol (hK : IsMercerKernel 𝕜 K) [μ.IsOpenPosMeasure] :
    IsL2Symbol μ (sqrtSymbol d) := by
  sorry

/-- The image of the square-root operator is square-integrable. -/
theorem memLp_integralOp_sqrtSymbol (hK : IsMercerKernel 𝕜 K) [μ.IsOpenPosMeasure]
    (g : Lp 𝕜 2 μ) :
    MemLp (integralOp μ (sqrtSymbol d) g) 2 μ := by
  -- OPEN.  Once `isL2Symbol_sqrtSymbol` is available this is `norm_integralOp_le`
  -- (IntegralOperator) plus `Lp.norm_le_of_ae_bound`, exactly as in
  -- `memLp_integralOp_of_continuous` (Mercer/Defs) — but the pointwise bound
  -- `‖symbolConjLp S x‖ ≤ √(re K(x,x))` again needs the diagonal expansion.
  sorry

variable (hK : IsMercerKernel 𝕜 K) [μ.IsOpenPosMeasure]

/-- **The square root of the Mercer operator**: the bounded integral operator with
symbol `sqrtSymbol d`, i.e. `T_S g = ∑ₙ √λₙ ⟪eₙ, g⟫ eₙ`. -/
noncomputable def sqrtCLM : Lp 𝕜 2 μ →L[𝕜] Lp 𝕜 2 μ :=
  LinearMap.mkContinuousOfExistsBound
    { toFun := fun g => (memLp_integralOp_sqrtSymbol d hK g).toLp _
      -- OPEN (all three): the linearity fields are `integralOp_eq_inner` plus
      -- `inner_add_right`/`inner_smul_right` verbatim as in `mercerCLM` (Mercer/Defs);
      -- the bound is `‖T_S g‖ ≤ √(sup_x re K(x,x)) · √μ(X) · ‖g‖`.  Both are blocked
      -- only by `isL2Symbol_sqrtSymbol` above.
      map_add' := by sorry
      map_smul' := by sorry }
    (by sorry)

/-- Diagonalization of the square root: `T_S g = ∑ₙ √λₙ ⟪eₙ, g⟫ eₙ`. -/
theorem sqrtCLM_hasSum (g : Lp 𝕜 2 μ) :
    HasSum
      (fun n => ((Real.sqrt (d.eigval n) : ℝ) : 𝕜) •
        (⟪ContinuousMap.toLp 2 μ 𝕜 (d.eigfun n), g⟫_𝕜 •
          ContinuousMap.toLp 2 μ 𝕜 (d.eigfun n)))
      (sqrtCLM d hK g) := by
  -- OPEN.  Same shape as the `key` HasSum inside `isPositive_mercerCLM`
  -- (Mercer/Basic, PROVED): finite truncations of `sqrtSymbol` give the finite sums, and
  -- `norm_mercerCLM_le_of_bounded` (Mercer/Compact) transfers the limit — except that
  -- the truncation error of `sqrtSymbol` is NOT uniform (the square-root symbol need not
  -- be continuous), so the transfer has to be run in `L²` via `d.orthonormal`.
  sorry

/-- The square root is a positive operator. -/
theorem sqrtCLM_isPositive : (sqrtCLM d hK).IsPositive := by
  -- OPEN.  Immediate from `sqrtCLM_hasSum`: `⟪g, T_S g⟫ = ∑ₙ √λₙ ‖⟪eₙ, g⟫‖² ≥ 0`, and
  -- symmetry by the same uniqueness-of-sums argument used in `isPositive_mercerCLM`.
  sorry

/-- **`T_S` squares to `T_K`**: `T_S ∘ T_S = T_K`. -/
theorem sqrtCLM_comp_self : (sqrtCLM d hK).comp (sqrtCLM d hK) = mercerCLM μ hKc := by
  -- OPEN.  From `sqrtCLM_hasSum` twice and `d.opExpansion`: both sides send `g` to
  -- `∑ₙ λₙ ⟪eₙ, g⟫ eₙ`.  Needs `HasSum.unique` in `L²` plus orthonormality.
  sorry

/-- **`range T_S = H(K)`**: the square-root operator maps `L²(X, μ)` onto exactly the
functions of the (measure-independent!) RKHS of `K`. -/
theorem range_integralOp_sqrtSymbol_eq
    -- USER-INPUT: `H` has reproducing kernel `K`
    (hKH : scalarKernel H = K) :
    Set.range (integralOp μ (sqrtSymbol d))
      = Set.range fun f : H => (f : X → 𝕜) := by
  -- OPEN.  Route: `S □ S* = K` (compute from `sqrtCLM_comp_self` and Hermitian symmetry
  -- of `S`), so `RangeSpace.lean`'s range space of the symbol `S` is an RKHS with kernel
  -- `K`; `Uniqueness.range_coe_eq_of_scalarKernel_eq` then transports the range to `H`.
  sorry

/-- **`T_S` is an isometry of `(ker T_K)ᗮ` onto `H(K)`**: for `g ⊥ ker T_K`, the
function `T_S g` is realized in `H` with equal norm. -/
theorem sqrtCLM_isometry_on_ker_orthogonal
    -- USER-INPUT: `H` has reproducing kernel `K`
    (hKH : scalarKernel H = K)
    {g : Lp 𝕜 2 μ} (hg : g ∈ (LinearMap.ker (mercerCLM μ hKc).toLinearMap)ᗮ) :
    ∃ f : H, (f : X → 𝕜) = integralOp μ (sqrtSymbol d) g ∧ ‖f‖ = ‖g‖ := by
  -- OPEN.  Same route as `range_integralOp_sqrtSymbol_eq`, plus the fact that the range
  -- space's norm agrees with `‖g‖` on `(ker T_S)ᗮ = (ker T_K)ᗮ` (`rangeSpace_*`).
  sorry

/-- **`{√λₙ eₙ}` is an orthonormal basis of `H(K)`**: the rescaled eigenfunctions are
realized in `H`, are orthonormal there, and their span is dense. -/
theorem exists_orthonormalBasis_sqrt_eigfun
    -- USER-INPUT: `H` has reproducing kernel `K`
    (hKH : scalarKernel H = K) :
    ∃ b : d.ι → H,
      (∀ n, (b n : X → 𝕜) = fun x =>
        ((Real.sqrt (d.eigval n) : ℝ) : 𝕜) * d.eigfun n x) ∧
      Orthonormal 𝕜 b ∧
      (Submodule.span 𝕜 (Set.range b)).topologicalClosure = ⊤ := by
  -- OPEN.  With `hasSum_kernel` the family `{√λₙ eₙ}` expands `K` pointwise, so
  -- `ParsevalFrame`/`Papadakis` recognizes it as a Parseval frame of `H`; orthonormality
  -- upgrades it to an orthonormal basis.  Blocked on getting the members into `H`, i.e.
  -- on `range_integralOp_sqrtSymbol_eq`.
  sorry

/-- **Spectral membership test for `H(K)`**: a function lies in `H(K)` iff it is a
pointwise sum `∑ₙ aₙ eₙ` with `∑ₙ |aₙ|²/λₙ < ∞`. -/
theorem mem_range_coe_iff_summable
    -- USER-INPUT: `H` has reproducing kernel `K`
    (hKH : scalarKernel H = K) (g₀ : X → 𝕜) :
    (∃ f : H, (f : X → 𝕜) = g₀)
      ↔ ∃ a : d.ι → 𝕜,
          Summable (fun n => ‖a n‖ ^ 2 / d.eigval n) ∧
          ∀ x, HasSum (fun n => a n * d.eigfun n x) (g₀ x) := by
  -- OPEN.  Immediate from `exists_orthonormalBasis_sqrt_eigfun`: expand `f` in the
  -- orthonormal basis `{√λₙ eₙ}` and set `aₙ := √λₙ ⟪bₙ, f⟫`, so that
  -- `∑ₙ ‖aₙ‖²/λₙ = ‖f‖²`.
  sorry

/-- `range T_K ⊆ H(K)`: the (non-square-rooted) Mercer operator maps into the RKHS. -/
theorem range_mercerCLM_subset
    -- USER-INPUT: `H` has reproducing kernel `K`
    (hKH : scalarKernel H = K) (g : Lp 𝕜 2 μ) :
    ∃ f : H, (f : X → 𝕜) = integralOp μ K g := by
  -- OPEN.  `T_K = T_S ∘ T_S` (`sqrtCLM_comp_self`), so `range T_K ⊆ range T_S = H(K)`
  -- by `range_integralOp_sqrtSymbol_eq`.  Alternatively, directly from
  -- `isMercerKernel_trace_smul_sub_boxProd` (PROVED above) via the Aronszajn domination
  -- criterion `K □ K ⪯ (∫ K(t,t) dμ) · K`, which is the measure-free route.
  sorry

end SquareRoot

end StatLean.NonparametricStatistics
