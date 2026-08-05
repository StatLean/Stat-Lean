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
  sorry

/-- The eigenvalues of a Mercer eigensystem are square-summable (they are dominated by
the trace `∫ K(x,x) dμ`; in fact they are summable). -/
theorem MercerEigensystem.summable_eigval {K : X → X → 𝕜}
    {hKc : Continuous fun p : X × X => K p.1 p.2}
    (hK : IsMercerKernel 𝕜 K)
    [μ.IsOpenPosMeasure]
    (d : MercerEigensystem μ K hKc) :
    Summable d.eigval := by
  sorry

/-- The trace formula: `∑ₙ λₙ = ∫ K(x, x) dμ(x)`. -/
theorem MercerEigensystem.hasSum_eigval {K : X → X → 𝕜}
    {hKc : Continuous fun p : X × X => K p.1 p.2}
    (hK : IsMercerKernel 𝕜 K)
    [μ.IsOpenPosMeasure]
    (d : MercerEigensystem μ K hKc) :
    HasSum d.eigval (∫ x, RCLike.re (K x x) ∂μ) := by
  sorry

end StatLean.NonparametricStatistics
