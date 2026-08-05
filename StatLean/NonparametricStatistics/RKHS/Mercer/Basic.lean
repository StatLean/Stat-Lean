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

/-- Pointwise bound over the kernel diagonal supremum: for `f` in the RKHS of a Mercer
kernel, `‖f x‖ ≤ √(sup_t K(t,t)) · ‖f‖`. -/
theorem norm_apply_le_sSup {K : X → X → 𝕜} (hK : IsMercerKernel 𝕜 K)
    -- USER-INPUT: `H` has reproducing kernel `K`
    (hKH : scalarKernel H = K) (f : H) (x : X) :
    ‖f x‖ ≤ Real.sqrt (⨆ t : X, RCLike.re (K t t)) * ‖f‖ := by
  sorry

/-- The `L²(μ)` norm of an RKHS member is controlled by its sup norm:
`∫ ‖f x‖² dμ ≤ μ(X) · (sup_x ‖f x‖)²` — the members of a Mercer RKHS embed in `L²`. -/
theorem integral_normSq_le {K : X → X → 𝕜} (hK : IsMercerKernel 𝕜 K)
    -- USER-INPUT: `H` has reproducing kernel `K`
    (hKH : scalarKernel H = K) (f : H) :
    ∫ x, ‖f x‖ ^ 2 ∂μ ≤ (μ Set.univ).toReal * (⨆ x : X, ‖f x‖) ^ 2 := by
  sorry

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

/-- Dini upgrade on the diagonal: the partial sums of `∑ᵢ ‖eᵢ x‖²` converge to the
continuous limit `re K(x,x)` uniformly on the compact space `X`. -/
theorem tendstoUniformly_diag {K : X → X → 𝕜} (hK : IsMercerKernel 𝕜 K)
    -- USER-INPUT: `H` has reproducing kernel `K`
    (hKH : scalarKernel H = K) {ι : Type*} (e : HilbertBasis ι 𝕜 H) :
    TendstoUniformly
      (fun s : Finset ι => fun x : X => ∑ i ∈ s, ‖(e i : H) x‖ ^ 2)
      (fun x => RCLike.re (K x x)) Filter.atTop := by
  sorry

/-- **Uniform absolute convergence of the basis expansion of a Mercer kernel**: the
partial sums of `∑ᵢ conj (eᵢ y) eᵢ x` converge to `K` uniformly on `X × X`. -/
theorem tendstoUniformly_scalarKernel {K : X → X → 𝕜} (hK : IsMercerKernel 𝕜 K)
    -- USER-INPUT: `H` has reproducing kernel `K`
    (hKH : scalarKernel H = K) {ι : Type*} (e : HilbertBasis ι 𝕜 H) :
    TendstoUniformly
      (fun s : Finset ι => fun p : X × X => ∑ i ∈ s, conj ((e i : H) p.2) * (e i : H) p.1)
      (fun p => K p.1 p.2) Filter.atTop := by
  sorry

/-- Tail bound by Cauchy–Schwarz: partial sums of the expansion off the diagonal are
dominated through the diagonal tails,
`‖∑_{i ∈ s} conj (eᵢ y) eᵢ x‖² ≤ (∑_{i ∈ s} ‖eᵢ x‖²) (∑_{i ∈ s} ‖eᵢ y‖²)`. -/
theorem sq_norm_sum_le {ι : Type*} (e : HilbertBasis ι 𝕜 H) (s : Finset ι) (x y : X) :
    ‖∑ i ∈ s, conj ((e i : H) y) * (e i : H) x‖ ^ 2
      ≤ (∑ i ∈ s, ‖(e i : H) x‖ ^ 2) * (∑ i ∈ s, ‖(e i : H) y‖ ^ 2) := by
  sorry

end UniformConvergence

section OperatorProperties

/-- `‖T_K‖` is bounded by the `L²(μ × μ)` norm of the kernel. -/
theorem norm_mercerCLM_le {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2) :
    ‖mercerCLM μ hKc‖
      ≤ Real.sqrt (∫ x, ∫ y, ‖K x y‖ ^ 2 ∂μ ∂μ) := by
  sorry

/-- Functions in the range of `T_K` (pointwise version) are continuous. -/
theorem continuous_integralOp_of_continuous {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2) (g : Lp 𝕜 2 μ) :
    Continuous (integralOp μ K g) := by
  sorry

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
  sorry

/-- Pointwise boundedness of the image of the unit ball:
`‖T_K g (x)‖ ≤ √(∫ ‖K(x,y)‖² dμ(y))` for `‖g‖ ≤ 1`. -/
theorem norm_integralOp_le_of_mem_ball {K : X → X → 𝕜}
    (hKc : Continuous fun p : X × X => K p.1 p.2) {g : Lp 𝕜 2 μ}
    (hg : ‖g‖ ≤ 1) (x : X) :
    ‖integralOp μ K g x‖ ≤ Real.sqrt (∫ y, ‖K x y‖ ^ 2 ∂μ) := by
  sorry

end OperatorProperties

end StatLean.NonparametricStatistics
