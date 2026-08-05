import StatLean.NonparametricStatistics.RKHS.Mercer.Compact
import StatLean.NonparametricStatistics.RKHS.Mercer.OperatorLemmas
import Mathlib.Analysis.InnerProductSpace.Spectrum

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
open scoped InnerProductSpace

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
