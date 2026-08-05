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
-- OPEN.  All three operator inputs are now available: `isCompactOperator_mercerCLM`
-- (Mercer/Compact), `isPositive_mercerCLM` (Mercer/Basic, hence `IsSymmetric` via
-- `ContinuousLinearMap.IsPositive.1`), and `continuous_integralOp_of_continuous`
-- (Mercer/Basic) for the continuous representative of an eigenfunction
-- (`e = λ⁻¹ • T_K e`, upgraded from a.e. to everywhere by `μ.IsOpenPosMeasure`).
-- Missing ingredients, in order of difficulty:
-- (a) *countability of the nonzero spectrum*: for a compact self-adjoint `T` and each
--     `k : ℕ` the set of eigenvalues with `|λ| > 1/k` carries only finitely many
--     mutually orthogonal eigenvectors (else `‖T eₙ − T eₘ‖² = λₙ² + λₘ² ≥ 2/k²`
--     contradicts total boundedness of the image of the unit ball).  Mathlib's
--     `Mathlib/Analysis/InnerProductSpace/Spectrum.lean` has
--     `ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot` and
--     finite-dimensionality of the nonzero eigenspaces, but no countability statement;
--     it has to be built here from `IsCompactOperator.isCompact_closure_image_ball`.
-- (b) the index type of `MercerEigensystem` lives in `Type` (universe 0), so the
--     `Σ (λ : nonzero eigenvalues), Fin (dim (eigenspace λ))` bookkeeping needs an
--     explicit encoding into `ℕ × ℕ`-style data, not just a sigma type over the
--     (large) eigenvalue set.
-- (c) `opExpansion` needs a Hilbert basis of `L²` refining the eigenspaces
--     (eigenvectors over `ι` together with any ONB of `ker T_K`), obtained from (a)
--     plus `HilbertBasis.hasSum_repr` and `ContinuousLinearMap.hasSum`.
theorem exists_mercerEigensystem {K : X → X → 𝕜} (hK : IsMercerKernel 𝕜 K)
    -- USER-INPUT: the measure has full support
    [μ.IsOpenPosMeasure] :
    Nonempty (MercerEigensystem μ K hK.continuous) := by
  sorry

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
