import StatLean.NonparametricStatistics.RKHS.Mercer.Compact
import StatLean.NonparametricStatistics.RKHS.Mercer.OperatorLemmas
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Mercer's theorem

For a Mercer kernel `K` on a compact metric space `X` and a finite Borel measure `μ` of
full support, the integral operator `T_K` on `L²(X, μ)` admits a countable orthonormal
system of *continuous* eigenfunctions `e_n` with positive eigenvalues `λ_n` such that

* `T_K g = ∑ₙ λₙ ⟪eₙ, g⟫ eₙ` for every `g ∈ L²`;
* `K(x, y) = ∑ₙ λₙ eₙ(x) conj (eₙ(y))`, converging absolutely and uniformly on `X × X`.

The eigen-data is packaged in the structure `MercerEigensystem`.  Existence is obtained
from the spectral theorem for compact self-adjoint operators
(`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`) applied to the
compact positive operator `T_K` (`isCompactOperator_mercerCLM`,
`isPositive_mercerCLM`): eigenspaces for distinct nonzero eigenvalues are
finite-dimensional and mutually orthogonal, eigenfunctions of nonzero eigenvalues have
continuous representatives (`e = λ⁻¹ T_K e` and `T_K` has continuous range), and the
uniform kernel expansion follows from the positivity of the residual kernels and Dini's
theorem (`tendstoUniformly_scalarKernel`).

**Bibliographic comments.** J. Mercer, *Functions of positive and negative type and
their connection with the theory of integral equations*, Philos. Trans. Roy. Soc. A
**209** (1909), 415–446; modern treatments in F. Smithies, *Integral Equations* (1958),
Ch. 7, and H. König, *Eigenvalue Distribution of Compact Operators* (Birkhäuser, 1986).
-/

open RKHS ComplexConjugate MeasureTheory
open scoped InnerProductSpace ENNReal

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X]

/-- **A Mercer eigensystem** for the kernel `K` against the measure `μ`: a countable
orthonormal family of continuous eigenfunctions of the integral operator `T_K` with
positive eigenvalues, through which `T_K` diagonalizes. -/
structure MercerEigensystem (μ : Measure X) [IsFiniteMeasure μ] (K : X → X → 𝕜)
    (hKc : Continuous fun p : X × X => K p.1 p.2) where
  /-- Index type of the eigensystem. -/
  ι : Type
  /-- The eigensystem is countable. -/
  countable : Countable ι
  /-- The eigenfunctions, as continuous functions on `X`. -/
  eigfun : ι → C(X, 𝕜)
  /-- The eigenvalues. -/
  eigval : ι → ℝ
  /-- Only the strictly positive part of the spectrum is enumerated.  Constitutive:
  the kernel of `T_K` contributes nothing to the expansion. -/
  eigval_pos : ∀ n, 0 < eigval n
  /-- The eigenfunctions are orthonormal in `L²(X, μ)`. -/
  orthonormal : Orthonormal 𝕜 fun n => ContinuousMap.toLp 2 μ 𝕜 (eigfun n)
  /-- The pointwise eigenfunction equation `(T_K eₙ)(x) = λₙ eₙ(x)` — everywhere, not
  just a.e., by continuity and full support. -/
  eigen_eq : ∀ n x,
    integralOp μ K (ContinuousMap.toLp 2 μ 𝕜 (eigfun n)) x = (eigval n : 𝕜) * eigfun n x
  /-- Diagonalization of `T_K`: `T_K g = ∑ₙ λₙ ⟪eₙ, g⟫ eₙ` for every `g ∈ L²(X, μ)`. -/
  opExpansion : ∀ g : Lp 𝕜 2 μ,
    HasSum
      (fun n => (eigval n : 𝕜) •
        (⟪ContinuousMap.toLp 2 μ 𝕜 (eigfun n), g⟫_𝕜 • ContinuousMap.toLp 2 μ 𝕜 (eigfun n)))
      (mercerCLM μ hKc g)

variable {μ : Measure X} [IsFiniteMeasure μ]

/-- `L²` of a finite Borel measure on a compact metric space is separable. -/
private theorem separableSpace_Lp (𝕜 : Type*) [RCLike 𝕜] {X : Type*} [MetricSpace X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ] :
    TopologicalSpace.SeparableSpace (Lp 𝕜 2 μ) := by
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  infer_instance


/-- An orthonormal family in a separable inner product space has a countable index type. -/
private theorem countable_of_orthonormal {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [TopologicalSpace.SeparableSpace E] {ι : Type*} {v : ι → E}
    (hv : Orthonormal 𝕜 v) : Countable ι := by
  have hdist : ∀ i j : ι, i ≠ j → (1 : ℝ) ≤ dist (v i) (v j) := by
    intro i j hij
    have h : ‖v i - v j‖ ^ 2 = 2 := by
      rw [@norm_sub_sq 𝕜, hv.1 i, hv.1 j, hv.2 hij]
      norm_num
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (v i - v j), h]
  refine Pairwise.countable_of_isOpen_disjoint
    (s := fun i => Metric.ball (v i) (1 / 2)) ?_ (fun i => Metric.isOpen_ball)
    (fun i => ⟨v i, Metric.mem_ball_self (by norm_num)⟩)
  intro i j hij
  exact Metric.ball_disjoint_ball (by linarith [hdist i j hij])


open Module.End in
/-- Spectral data of a compact positive operator on a separable Hilbert space. -/
private theorem exists_eigen_data {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (T : E →L[𝕜] E) (hTc : IsCompactOperator T) (hTp : T.IsPositive) :
    ∃ (ι : Type) (v : ι → E) (lam : ι → ℝ),
      Countable ι ∧ (∀ n, 0 < lam n) ∧ Orthonormal 𝕜 v ∧
      (∀ n, T (v n) = (lam n : 𝕜) • v n) ∧
      ∀ g : E, HasSum (fun n => (lam n : 𝕜) • (⟪v n, g⟫_𝕜 • v n)) (T g) := by
  classical
  have hTs : (T : E →ₗ[𝕜] E).IsSymmetric := hTp.isSymmetric
  set Pos : Type := {r : ℝ // 0 < r ∧ HasEigenvalue (T : E →ₗ[𝕜] E) ((r : ℝ) : 𝕜)} with hPos
  set W : Pos → Submodule 𝕜 E := fun p => eigenspace (T : E →ₗ[𝕜] E) (((p : ℝ) : 𝕜)) with hW
  haveI hfd : ∀ p : Pos, FiniteDimensional 𝕜 (W p) := by
    intro p
    exact ContinuousLinearMap.finite_dimensional_eigenspace hTc _
      (RCLike.ofReal_ne_zero.mpr p.2.1.ne')
  set b : (p : Pos) → OrthonormalBasis (Fin (Module.finrank 𝕜 (W p))) 𝕜 (W p) :=
    fun p => stdOrthonormalBasis 𝕜 (W p) with hb
  set ι : Type := Σ p : Pos, Fin (Module.finrank 𝕜 (W p)) with hι
  set v : ι → E := fun n => ((b n.1 n.2 : W n.1) : E) with hv
  set lam : ι → ℝ := fun n => (n.1 : ℝ) with hlam
  -- orthonormality of the eigenvector family
  have hON : Orthonormal 𝕜 v := by
    constructor
    · rintro ⟨p, i⟩
      exact (b p).orthonormal.1 i
    · rintro ⟨p, i⟩ ⟨q, j⟩ hij
      by_cases hpq : p = q
      · subst hpq
        have hij' : i ≠ j := fun h => hij (by rw [h])
        have := (b p).orthonormal.2 hij'
        simpa using this
      · have hne : (((p : ℝ) : 𝕜)) ≠ (((q : ℝ) : 𝕜)) := fun h =>
          hpq (Subtype.ext (RCLike.ofReal_inj.mp h))
        exact hTs.orthogonalFamily_eigenspaces hne (b p i) (b q j)
  -- the eigenvalue equation
  have heig : ∀ n, T (v n) = ((lam n : ℝ) : 𝕜) • v n := by
    rintro ⟨p, i⟩
    exact mem_eigenspace_iff.mp (b p i).2
  -- the kernel of `T` and a Hilbert basis of it
  obtain ⟨N, hN⟩ : ∃ N : Submodule 𝕜 E, N = LinearMap.ker (T : E →ₗ[𝕜] E) := ⟨_, rfl⟩
  haveI hNc : CompleteSpace N := by rw [hN]; infer_instance
  obtain ⟨w, e, he⟩ := @exists_hilbertBasis 𝕜 _ N _ _ hNc
  set vAll : ι ⊕ w → E := Sum.elim v (fun k => ((e k : N) : E)) with hvAll
  -- membership facts
  have hvW : ∀ n : ι, v n ∈ W n.1 := fun n => (b n.1 n.2).2
  have heN : ∀ k : w, ((e k : N) : E) ∈ N := fun k => (e k).2
  have hkerN : ∀ k : w, T (((e k : N)) : E) = 0 := by
    intro k
    have h1 : ((e k : N) : E) ∈ LinearMap.ker (T : E →ₗ[𝕜] E) := by
      rw [← hN]; exact heN k
    exact h1
  have hONall : Orthonormal 𝕜 vAll := by
    constructor
    · rintro (n | k)
      · exact hON.1 n
      · exact e.orthonormal.1 k
    · rintro (n | k) (m | l) hne
      · exact hON.2 (fun h => hne (by rw [h]))
      · have h0 : (((n.1 : ℝ)) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr n.1.2.1.ne'
        have hmem : ((e l : N) : E) ∈ eigenspace (T : E →ₗ[𝕜] E) 0 := by
          rw [eigenspace_zero, ← hN]; exact heN l
        exact hTs.orthogonalFamily_eigenspaces h0 ⟨v n, hvW n⟩ ⟨_, hmem⟩
      · have h0 : (0 : 𝕜) ≠ (((m.1 : ℝ)) : 𝕜) :=
          (RCLike.ofReal_ne_zero.mpr m.1.2.1.ne').symm
        have hmem : ((e k : N) : E) ∈ eigenspace (T : E →ₗ[𝕜] E) 0 := by
          rw [eigenspace_zero, ← hN]; exact heN k
        exact hTs.orthogonalFamily_eigenspaces h0 ⟨_, hmem⟩ ⟨v m, hvW m⟩
      · exact e.orthonormal.2 (fun h => hne (by rw [h]))
  -- the combined family spans a dense subspace
  have hbot : (Submodule.span 𝕜 (Set.range vAll))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro g hg
    have hperp : ∀ i, ⟪vAll i, g⟫_𝕜 = 0 := fun i =>
      (Submodule.mem_orthogonal _ _).mp hg _ (Submodule.subset_span ⟨i, rfl⟩)
    -- `g` is orthogonal to the whole kernel
    have hgN : ∀ y : N, ⟪(y : E), g⟫_𝕜 = 0 := by
      have hMle : (Submodule.span 𝕜 (Set.range (e : w → N))).topologicalClosure
          ≤ LinearMap.ker (((innerSL 𝕜 g).comp N.subtypeL : ↥N →L[𝕜] 𝕜) : ↥N →ₗ[𝕜] 𝕜) := by
        refine Submodule.topologicalClosure_minimal _ ?_
          (ContinuousLinearMap.isClosed_ker _)
        refine Submodule.span_le.mpr ?_
        rintro _ ⟨k, rfl⟩
        have hz : ⟪((e k : N) : E), g⟫_𝕜 = 0 := hperp (Sum.inr k)
        simp only [SetLike.mem_coe, LinearMap.mem_ker]
        show ⟪g, ((e k : N) : E)⟫_𝕜 = 0
        rw [← inner_conj_symm, hz, map_zero]
      intro y
      have h2 := hMle (e.dense_span.ge (Submodule.mem_top (x := y)))
      rw [LinearMap.mem_ker] at h2
      have h3 : ⟪g, (y : E)⟫_𝕜 = 0 := h2
      rw [← inner_conj_symm, h3, map_zero]
    -- `g` is orthogonal to every eigenspace
    have hgE : ∀ (c : 𝕜) (y : E), y ∈ eigenspace (T : E →ₗ[𝕜] E) c → ⟪y, g⟫_𝕜 = 0 := by
      intro c y hy
      rcases eq_or_ne c 0 with rfl | hc
      · rw [eigenspace_zero, ← hN] at hy
        exact hgN ⟨y, hy⟩
      · by_cases hev : eigenspace (T : E →ₗ[𝕜] E) c = ⊥
        · rw [hev, Submodule.mem_bot] at hy
          simp [hy]
        · have hHE : HasEigenvalue (T : E →ₗ[𝕜] E) c := hev
          have hcr : (((RCLike.re c : ℝ)) : 𝕜) = c :=
            RCLike.conj_eq_iff_re.mp (hTs.conj_eigenvalue_eq_self hHE)
          have hnn : ∀ x : E, 0 ≤ RCLike.re ⟪x, (T : E →ₗ[𝕜] E) x⟫_𝕜 := by
            intro x
            rw [← hTs x x]
            exact hTp.2 x
          have hge : (0 : ℝ) ≤ RCLike.re c :=
            eigenvalue_nonneg_of_nonneg (by rw [hcr]; exact hHE) hnn
          have hrne : RCLike.re c ≠ 0 := by
            intro h0
            exact hc (by rw [← hcr, h0, RCLike.ofReal_zero])
          have hrpos : 0 < RCLike.re c := lt_of_le_of_ne hge (Ne.symm hrne)
          set p : Pos := ⟨RCLike.re c, hrpos, by rw [hcr]; exact hHE⟩ with hp
          have hyW : y ∈ W p := by rw [hW]; simpa [hp, hcr] using hy
          have hexp := (b p).sum_repr ⟨y, hyW⟩
          have hy' : y = ∑ i, ((b p).repr ⟨y, hyW⟩ i) • v ⟨p, i⟩ := by
            have := congrArg (fun z : W p => (z : E)) hexp
            simpa using this.symm
          rw [hy', sum_inner]
          refine Finset.sum_eq_zero fun i _ => ?_
          have hI : ⟪v ⟨p, i⟩, g⟫_𝕜 = 0 := hperp (Sum.inl ⟨p, i⟩)
          rw [inner_smul_left, hI, mul_zero]
    -- conclude via the spectral theorem
    have hle : (⨆ c, eigenspace (T : E →ₗ[𝕜] E) c) ≤ (𝕜 ∙ g)ᗮ := by
      refine iSup_le fun c => ?_
      intro y hy
      rw [Submodule.mem_orthogonal]
      intro u hu
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [inner_smul_left]
      have : ⟪g, y⟫_𝕜 = 0 := by
        rw [← inner_conj_symm, hgE c y hy, map_zero]
      rw [this, mul_zero]
    have hmem : g ∈ (⨆ c, eigenspace (T : E →ₗ[𝕜] E) c)ᗮ :=
      Submodule.orthogonal_le hle
        (Submodule.le_orthogonal_orthogonal _ (Submodule.mem_span_singleton_self g))
    rw [ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot hTc hTs] at hmem
    simpa using hmem
  set bAll : HilbertBasis (ι ⊕ w) 𝕜 E := HilbertBasis.mkOfOrthogonalEqBot hONall hbot with hbAll
  have hcoe : ⇑bAll = vAll := HilbertBasis.coe_mkOfOrthogonalEqBot _ _
  refine ⟨ι, v, lam, countable_of_orthonormal hON, fun n => n.1.2.1, hON, heig, ?_⟩
  intro g
  have hrep : HasSum (fun i => ⟪vAll i, g⟫_𝕜 • vAll i) g := by
    have h := bAll.hasSum_repr g
    simp only [hcoe, HilbertBasis.repr_apply_apply] at h
    exact h
  have hTsum := hrep.mapL T
  simp only [map_smul] at hTsum
  have hvan : ∀ x ∉ Set.range (Sum.inl : ι → ι ⊕ w),
      (fun i => ⟪vAll i, g⟫_𝕜 • T (vAll i)) x = 0 := by
    rintro (n | k) hx
    · exact absurd ⟨n, rfl⟩ hx
    · simp [hvAll, hkerN k]
  have := (Sum.inl_injective (β := w)).hasSum_iff (f := fun i => ⟪vAll i, g⟫_𝕜 • T (vAll i))
    (a := T g) hvan
  rw [← this] at hTsum
  convert hTsum using 2 with n
  have h1 : vAll (Sum.inl n) = v n := rfl
  rw [Function.comp_apply, h1, heig n, smul_comm]


/-- **Mercer's theorem, existence of the eigensystem**: every Mercer kernel against a
finite Borel measure of full support admits a Mercer eigensystem. -/
theorem exists_mercerEigensystem {K : X → X → 𝕜} (hK : IsMercerKernel 𝕜 K)
    -- USER-INPUT: the measure has full support
    [μ.IsOpenPosMeasure] :
    Nonempty (MercerEigensystem μ K hK.continuous) := by
  haveI := separableSpace_Lp 𝕜 μ
  obtain ⟨ι, v, lam, hcount, hpos, hON, heig, hexp⟩ :=
    exists_eigen_data (mercerCLM μ hK.continuous) (isCompactOperator_mercerCLM hK)
      (isPositive_mercerCLM hK)
  have hlne : ∀ n, ((lam n : ℝ) : 𝕜) ≠ 0 := fun n => RCLike.ofReal_ne_zero.mpr (hpos n).ne'
  -- the continuous representative `λ⁻¹ T_K eₙ` of the eigenvector `eₙ`
  set F : ι → C(X, 𝕜) := fun n =>
    ⟨fun x => ((lam n : ℝ) : 𝕜)⁻¹ * integralOp μ K (v n) x,
      continuous_const.mul (continuous_integralOp_of_continuous hK.continuous (v n))⟩ with hF
  have htoLp : ∀ n, ContinuousMap.toLp 2 μ 𝕜 (F n) = v n := by
    intro n
    have h4 : ((mercerCLM μ hK.continuous (v n) : Lp 𝕜 2 μ) : X → 𝕜)
        =ᵐ[μ] ((((lam n : ℝ) : 𝕜) • v n : Lp 𝕜 2 μ) : X → 𝕜) := by rw [heig n]
    refine Lp.ext ?_
    filter_upwards [ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (μ := μ) (𝕜 := 𝕜) (F n),
      mercerCLM_coeFn_ae hK.continuous (v n), h4,
      Lp.coeFn_smul (((lam n : ℝ) : 𝕜)) (v n)] with x h1 h2 h3 h5
    rw [h1]
    change ((lam n : ℝ) : 𝕜)⁻¹ * integralOp μ K (v n) x = _
    rw [← h2, h3, h5]
    change ((lam n : ℝ) : 𝕜)⁻¹ * (((lam n : ℝ) : 𝕜) * ((v n : X → 𝕜) x)) = _
    rw [inv_mul_cancel_left₀ (hlne n)]
  have hfun : (fun n => ContinuousMap.toLp 2 μ 𝕜 (F n)) = v := funext htoLp
  refine ⟨⟨ι, hcount, F, lam, hpos, by rw [hfun]; exact hON, ?_, ?_⟩⟩
  · intro n x
    rw [htoLp n]
    change _ = ((lam n : ℝ) : 𝕜) * (((lam n : ℝ) : 𝕜)⁻¹ * integralOp μ K (v n) x)
    rw [mul_inv_cancel_left₀ (hlne n)]
  · intro g
    simp only [htoLp]
    exact hexp g

section Residual

variable {K : X → X → 𝕜} {hKc : Continuous fun p : X × X => K p.1 p.2}

/-- Coefficientwise description of a finite `L²` combination. -/
private theorem coeFn_finset_sum_smul' {ι : Type*} (s : Finset ι) (c : ι → 𝕜)
    (F : ι → Lp 𝕜 2 μ) :
    ((∑ i ∈ s, c i • F i : Lp 𝕜 2 μ) : X → 𝕜)
      =ᵐ[μ] fun x => ∑ i ∈ s, c i * (F i : X → 𝕜) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Lp.coeFn_zero 𝕜 2 μ
  | insert a t ha ih =>
      rw [Finset.sum_insert ha]
      filter_upwards [Lp.coeFn_add (c a • F a) (∑ i ∈ t, c i • F i),
        Lp.coeFn_smul (c a) (F a), ih] with x h1 h2 h3
      rw [h1]
      simp only [Pi.add_apply, h2, h3, Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_insert ha]

/-- The residual symbol of a Mercer eigensystem after removing a finite set of modes. -/
private noncomputable def residualSymbol (d : MercerEigensystem μ K hKc) (s : Finset d.ι) :
    X → X → 𝕜 :=
  fun x y => K x y - ∑ n ∈ s, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y))

private theorem continuous_residualSymbol (d : MercerEigensystem μ K hKc) (s : Finset d.ι) :
    Continuous fun p : X × X => residualSymbol d s p.1 p.2 :=
  hKc.sub (continuous_finset_sum s fun n _ =>
    continuous_const.mul (((d.eigfun n).continuous.comp continuous_fst).mul
      (RCLike.continuous_conj.comp ((d.eigfun n).continuous.comp continuous_snd))))

private theorem symbolConjLp_residual (d : MercerEigensystem μ K hKc) (s : Finset d.ι) (x : X) :
    symbolConjLp μ (residualSymbol d s)
        (isL2Symbol_of_continuous (continuous_residualSymbol d s)) x
      = symbolConjLp μ K (isL2Symbol_of_continuous hKc) x
        - ∑ n ∈ s, ((d.eigval n : 𝕜) * conj (d.eigfun n x)) •
            ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n) := by
  refine Lp.ext ?_
  filter_upwards [MemLp.coeFn_toLp (μ := μ) (p := 2)
      ((IsL2Symbol.conj _ (isL2Symbol_of_continuous (continuous_residualSymbol d s))) x),
    MemLp.coeFn_toLp (μ := μ) (p := 2)
      ((IsL2Symbol.conj _ (isL2Symbol_of_continuous hKc)) x),
    Lp.coeFn_sub (symbolConjLp μ K (isL2Symbol_of_continuous hKc) x)
      (∑ n ∈ s, ((d.eigval n : 𝕜) * conj (d.eigfun n x)) •
        ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)),
    coeFn_finset_sum_smul' s (fun n => (d.eigval n : 𝕜) * conj (d.eigfun n x))
      (fun n => ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)),
    (Filter.eventually_all_finset s).2 (fun n _ =>
      ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (μ := μ) (𝕜 := 𝕜) (d.eigfun n))]
    with y h1 h2 h3 h4 h5
  rw [h3]
  simp only [symbolConjLp, Pi.sub_apply]
  rw [h1, h2, h4]
  simp only [residualSymbol, map_sub, map_sum, map_mul, RCLike.conj_conj]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [h5 n hn, RCLike.conj_ofReal]
  ring

private theorem integralOp_residual (d : MercerEigensystem μ K hKc) (s : Finset d.ι)
    (g : Lp 𝕜 2 μ) (x : X) :
    integralOp μ (residualSymbol d s) g x
      = integralOp μ K g x
        - ∑ n ∈ s, (d.eigval n : 𝕜) *
            (d.eigfun n x * ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜) := by
  rw [integralOp_eq_inner _ (isL2Symbol_of_continuous (continuous_residualSymbol d s)),
    integralOp_eq_inner _ (isL2Symbol_of_continuous hKc), symbolConjLp_residual,
    inner_sub_left, sum_inner]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [inner_smul_left, map_mul, RCLike.conj_ofReal, RCLike.conj_conj]
  ring

private theorem mercerCLM_residual (d : MercerEigensystem μ K hKc) (s : Finset d.ι)
    (g : Lp 𝕜 2 μ) :
    mercerCLM μ (continuous_residualSymbol d s) g
      = mercerCLM μ hKc g
        - ∑ n ∈ s, ((d.eigval n : 𝕜) *
            ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜) •
              ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n) := by
  refine Lp.ext ?_
  filter_upwards [mercerCLM_coeFn_ae (continuous_residualSymbol d s) g,
    mercerCLM_coeFn_ae hKc g,
    Lp.coeFn_sub (mercerCLM μ hKc g)
      (∑ n ∈ s, ((d.eigval n : 𝕜) * ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜) •
        ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)),
    coeFn_finset_sum_smul' s
      (fun n => (d.eigval n : 𝕜) * ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜)
      (fun n => ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)),
    (Filter.eventually_all_finset s).2 (fun n _ =>
      ContinuousMap.coeFn_toLp (E := 𝕜) (p := 2) (μ := μ) (𝕜 := 𝕜) (d.eigfun n))]
    with x h1 h2 h3 h4 h5
  rw [h1, h3, Pi.sub_apply, h2, h4, integralOp_residual]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [h5 n hn]
  ring

/-- The quadratic form of `T_K` expands over the eigensystem with nonnegative terms. -/
private theorem hasSum_re_quadratic (d : MercerEigensystem μ K hKc) (g : Lp 𝕜 2 μ) :
    HasSum
      (fun n => d.eigval n *
        ‖⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜‖ ^ 2)
      (RCLike.re ⟪g, mercerCLM μ hKc g⟫_𝕜) := by
  refine (((d.opExpansion g).mapL (innerSL 𝕜 g)).map
    (RCLike.reCLM (K := 𝕜)).toLinearMap.toAddMonoidHom RCLike.reCLM.continuous).congr_fun
    fun n => ?_
  show d.eigval n * ‖⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜‖ ^ 2
      = RCLike.re ⟪g, (d.eigval n : 𝕜) •
          (⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜 •
            ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n))⟫_𝕜
  rw [inner_smul_right, inner_smul_right,
    ← inner_conj_symm g (ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n)),
    RCLike.mul_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]

private theorem isPositive_residual (hK : IsMercerKernel 𝕜 K)
    (d : MercerEigensystem μ K hKc) (s : Finset d.ι) :
    (mercerCLM μ (continuous_residualSymbol d s)).IsPositive := by
  have hTsym : ∀ a b : Lp 𝕜 2 μ,
      ⟪mercerCLM μ hKc a, b⟫_𝕜 = ⟪a, mercerCLM μ hKc b⟫_𝕜 :=
    fun a b => (isPositive_mercerCLM hK).1 a b
  constructor
  · intro h g
    show ⟪mercerCLM μ (continuous_residualSymbol d s) h, g⟫_𝕜
      = ⟪h, mercerCLM μ (continuous_residualSymbol d s) g⟫_𝕜
    rw [mercerCLM_residual, mercerCLM_residual, inner_sub_left, inner_sub_right, sum_inner,
      inner_sum, hTsym h g]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [inner_smul_left, inner_smul_right, map_mul (starRingEnd 𝕜), RCLike.conj_ofReal,
      inner_conj_symm]
    ring
  · intro g
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, mercerCLM_residual, inner_sub_left,
      sum_inner, map_sub, map_sum]
    have hkey := hasSum_re_quadratic d g
    have hre : RCLike.re ⟪mercerCLM μ hKc g, g⟫_𝕜 = RCLike.re ⟪g, mercerCLM μ hKc g⟫_𝕜 :=
      inner_re_symm _ _
    rw [hre]
    have hterm : ∀ n : d.ι,
        RCLike.re (⟪((d.eigval n : 𝕜) *
          ⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜) •
            ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜)
          = d.eigval n * ‖⟪ContinuousMap.toLp (E := 𝕜) 2 μ 𝕜 (d.eigfun n), g⟫_𝕜‖ ^ 2 := by
      intro n
      rw [inner_smul_left, map_mul (starRingEnd 𝕜), RCLike.conj_ofReal, mul_assoc,
        RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]
    simp only [hterm]
    have := sum_le_hasSum s
      (fun n _ => mul_nonneg (d.eigval_pos n).le (by positivity)) hkey
    linarith

/-- **Bessel-type bound**: the truncated diagonal sums are dominated by the kernel
diagonal.  This is the analytic heart of Mercer's theorem. -/
private theorem eig_diag_bound (hK : IsMercerKernel 𝕜 K) [μ.IsOpenPosMeasure]
    (d : MercerEigensystem μ K hKc) (s : Finset d.ι) (x : X) :
    ∑ n ∈ s, d.eigval n * ‖d.eigfun n x‖ ^ 2 ≤ RCLike.re (K x x) := by
  have hsym : ∀ a b : X, conj (residualSymbol d s a b) = residualSymbol d s b a := by
    intro a b
    simp only [residualSymbol, map_sub, map_sum, map_mul, RCLike.conj_conj,
      RCLike.conj_ofReal, hK.isKernelFun.conj_symm]
    congr 1
    exact Finset.sum_congr rfl fun n _ => by ring
  have hM := isMercerKernel_of_isPositive (continuous_residualSymbol d s) hsym
    (isPositive_residual hK d s)
  have h1 := hM.isKernelFun.re_sum_nonneg 1 (fun _ => x) (fun _ => 1)
  simp only [Fin.sum_univ_one, map_one, one_mul] at h1
  have h2 : RCLike.re (residualSymbol d s x x)
      = RCLike.re (K x x) - ∑ n ∈ s, d.eigval n * ‖d.eigfun n x‖ ^ 2 := by
    simp only [residualSymbol, map_sub, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [RCLike.mul_conj, ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]
  rw [h2] at h1
  linarith

/-- Finite Cauchy–Schwarz for the eigen-expansion. -/
private theorem sq_norm_sum_eig_le (d : MercerEigensystem μ K hKc) (t : Finset d.ι) (x y : X) :
    ‖∑ n ∈ t, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y))‖ ^ 2
      ≤ (∑ n ∈ t, d.eigval n * ‖d.eigfun n x‖ ^ 2) *
        (∑ n ∈ t, d.eigval n * ‖d.eigfun n y‖ ^ 2) := by
  have hsq : ∀ n : d.ι, ∀ z : X,
      (Real.sqrt (d.eigval n) * ‖d.eigfun n z‖) ^ 2 = d.eigval n * ‖d.eigfun n z‖ ^ 2 := by
    intro n z
    rw [mul_pow, Real.sq_sqrt (d.eigval_pos n).le]
  have h1 : ‖∑ n ∈ t, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y))‖
      ≤ ∑ n ∈ t, (Real.sqrt (d.eigval n) * ‖d.eigfun n x‖) *
          (Real.sqrt (d.eigval n) * ‖d.eigfun n y‖) := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n _ => ?_)
    rw [norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_ofReal,
      abs_of_pos (d.eigval_pos n)]
    have hs : Real.sqrt (d.eigval n) * Real.sqrt (d.eigval n) = d.eigval n :=
      Real.mul_self_sqrt (d.eigval_pos n).le
    have he : Real.sqrt (d.eigval n) * ‖d.eigfun n x‖ *
        (Real.sqrt (d.eigval n) * ‖d.eigfun n y‖)
        = d.eigval n * (‖d.eigfun n x‖ * ‖d.eigfun n y‖) := by
      rw [show Real.sqrt (d.eigval n) * ‖d.eigfun n x‖ *
        (Real.sqrt (d.eigval n) * ‖d.eigfun n y‖)
        = (Real.sqrt (d.eigval n) * Real.sqrt (d.eigval n)) *
          (‖d.eigfun n x‖ * ‖d.eigfun n y‖) from by ring, hs]
    exact le_of_eq he.symm
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq t
      (fun n => Real.sqrt (d.eigval n) * ‖d.eigfun n x‖)
      (fun n => Real.sqrt (d.eigval n) * ‖d.eigfun n y‖)
  simp only [hsq] at h2
  have h0 : (0 : ℝ) ≤ ∑ n ∈ t, (Real.sqrt (d.eigval n) * ‖d.eigfun n x‖) *
      (Real.sqrt (d.eigval n) * ‖d.eigfun n y‖) :=
    Finset.sum_nonneg fun n _ => by positivity
  nlinarith [norm_nonneg (∑ n ∈ t, (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y)))]

/-- The diagonal series of a Mercer eigensystem is summable. -/
private theorem summable_eig_diag (hK : IsMercerKernel 𝕜 K) [μ.IsOpenPosMeasure]
    (d : MercerEigensystem μ K hKc) (x : X) :
    Summable fun n => d.eigval n * ‖d.eigfun n x‖ ^ 2 :=
  summable_of_sum_le (fun n => mul_nonneg (d.eigval_pos n).le (sq_nonneg _))
    (fun s => eig_diag_bound hK d s x)

/-- The off-diagonal series of a Mercer eigensystem is summable. -/
private theorem summable_eig_prod (hK : IsMercerKernel 𝕜 K) [μ.IsOpenPosMeasure]
    (d : MercerEigensystem μ K hKc) (x y : X) :
    Summable fun n => (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y)) := by
  refine Summable.of_norm_bounded
    (((summable_eig_diag hK d x).add (summable_eig_diag hK d y)).div_const 2) fun n => ?_
  rw [norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_ofReal, abs_of_pos (d.eigval_pos n)]
  nlinarith [sq_nonneg (‖d.eigfun n x‖ - ‖d.eigfun n y‖), (d.eigval_pos n).le,
    norm_nonneg (d.eigfun n x), norm_nonneg (d.eigfun n y)]

end Residual

/-- **Mercer's theorem, kernel expansion**: `K(x, y) = ∑ₙ λₙ eₙ(x) conj (eₙ(y))`
pointwise (unordered absolute convergence). -/
theorem MercerEigensystem.hasSum_kernel {K : X → X → 𝕜}
    {hKc : Continuous fun p : X × X => K p.1 p.2}
    -- USER-INPUT: positivity of the kernel (with `hKc`, a Mercer kernel)
    (hK : IsMercerKernel 𝕜 K)
    [μ.IsOpenPosMeasure]
    (d : MercerEigensystem μ K hKc) (x y : X) :
    HasSum (fun n => (d.eigval n : 𝕜) * (d.eigfun n x * conj (d.eigfun n y))) (K x y) := by
  -- OPEN.  Route (independent of `exists_mercerEigensystem`): for a finite `s ⊆ ι` the
  -- residual symbol `K_s := K − ∑_{n ∈ s} λₙ eₙ ⊗ conj eₙ` is continuous, Hermitian, and
  -- its integral operator is `T_K` minus the spectral truncation, which is positive by
  -- `d.opExpansion`; hence `isMercerKernel_of_isPositive` (Mercer/Basic, PROVED) makes
  -- `K_s` a Mercer kernel and its diagonal is `≥ 0`, i.e.
  -- `∑_{n ∈ s} λₙ ‖eₙ x‖² ≤ re K(x,x)`.  Missing: the residual operators' norms tend to
  -- `0` (this is where the spectral theorem re-enters — it is exactly the statement that
  -- the eigen-expansion exhausts `(ker T_K)ᗮ`, which `opExpansion` gives in `L²` but
  -- which must be converted into `‖T_{K_s}‖ → 0`), plus the final step "a continuous
  -- kernel whose integral operator vanishes is `0` pointwise" (again
  -- `isMercerKernel_of_isPositive`'s averaging argument, applied to `±K_∞`).
  sorry

/-- **Mercer's theorem, uniform convergence**: the finite partial sums of the
eigen-expansion converge to `K` uniformly on `X × X`. -/
theorem MercerEigensystem.tendstoUniformly_kernel {K : X → X → 𝕜}
    {hKc : Continuous fun p : X × X => K p.1 p.2}
    (hK : IsMercerKernel 𝕜 K)
    [μ.IsOpenPosMeasure]
    (d : MercerEigensystem μ K hKc) :
    TendstoUniformly
      (fun s : Finset d.ι => fun p : X × X =>
        ∑ n ∈ s, (d.eigval n : 𝕜) * (d.eigfun n p.1 * conj (d.eigfun n p.2)))
      (fun p => K p.1 p.2) Filter.atTop := by
  -- OPEN.  Given `hasSum_kernel`, this is the same Dini-plus-Cauchy–Schwarz pattern as
  -- `tendstoUniformly_scalarKernel` (Mercer/Basic, PROVED): the diagonal partial sums
  -- `∑_{n ∈ s} λₙ ‖eₙ x‖²` are continuous, monotone in `s`, and converge pointwise to the
  -- continuous limit `re K(x,x)`, so `Monotone.tendstoUniformly_of_forall_tendsto`
  -- applies; the off-diagonal is then controlled by `sq_norm_sum_le` applied to the
  -- family `√λₙ eₙ`.
  sorry

/-- The eigenvalues of a Mercer eigensystem are square-summable (they are dominated by
the trace `∫ K(x,x) dμ`; in fact they are summable). -/
theorem MercerEigensystem.summable_eigval {K : X → X → 𝕜}
    {hKc : Continuous fun p : X × X => K p.1 p.2}
    (hK : IsMercerKernel 𝕜 K)
    [μ.IsOpenPosMeasure]
    (d : MercerEigensystem μ K hKc) :
    Summable d.eigval := by
  -- OPEN.  Follows from `hasSum_eigval` below (or directly from the residual positivity
  -- of `hasSum_kernel`: `∑_{n ∈ s} λₙ ‖eₙ x‖² ≤ re K(x,x)`, integrated over `x` with
  -- `‖eₙ‖_{L²} = 1`, bounds the partial sums by `∫ re K(x,x) dμ`).
  sorry

/-- The trace formula: `∑ₙ λₙ = ∫ K(x, x) dμ(x)`. -/
theorem MercerEigensystem.hasSum_eigval {K : X → X → 𝕜}
    {hKc : Continuous fun p : X × X => K p.1 p.2}
    (hK : IsMercerKernel 𝕜 K)
    [μ.IsOpenPosMeasure]
    (d : MercerEigensystem μ K hKc) :
    HasSum d.eigval (∫ x, RCLike.re (K x x) ∂μ) := by
  -- OPEN.  Integrate the uniform diagonal expansion of `tendstoUniformly_kernel` over
  -- `x`, swapping the integral with the uniform limit (`TendstoUniformlyOn` on the
  -- finite-measure space `X`), and use `∫ ‖eₙ‖² dμ = 1` from `d.orthonormal`.
  sorry

end StatLean.NonparametricStatistics
