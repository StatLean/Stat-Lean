import StatLean.NonparametricStatistics.RKHS.Mercer.Basic
import Mathlib.Analysis.Normed.Operator.Compact

/-!
# Compactness of the Mercer integral operator

The integral operator of a Mercer kernel is a compact operator on `L²(X, μ)`.  Route:
truncating the uniformly convergent basis expansion of `K`
(`tendstoUniformly_scalarKernel`) yields finite-rank integral operators converging to
`T_K` in operator norm, and the space of compact operators is closed
(`isCompactOperator_of_tendsto`).

**Bibliographic comments.** Compactness of integral operators with continuous kernels
is due to D. Hilbert (1904) and E. Schmidt (1907); the finite-rank approximation
argument is standard, cf. F. Smithies, *Integral Equations* (CUP, 1958), Ch. 7.
-/

open RKHS ComplexConjugate MeasureTheory
open scoped InnerProductSpace

namespace StatLean.NonparametricStatistics

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable [MeasurableSpace X] [BorelSpace X]
variable {μ : Measure X} [IsFiniteMeasure μ]

/-- Integral operators of kernels that are uniformly small have small operator norm:
`‖T_S‖ ≤ μ(X) · sup ‖S‖` for continuous symbols on a compact space. -/
theorem norm_mercerCLM_le_of_bounded {S : X → X → 𝕜}
    (hSc : Continuous fun p : X × X => S p.1 p.2) {C : ℝ}
    -- USER-INPUT: uniform bound on the symbol
    (hC : ∀ x y, ‖S x y‖ ≤ C) :
    ‖mercerCLM μ hSc‖ ≤ (μ Set.univ).toReal * C := by
  sorry

/-- The integral operator of a finite-rank symbol `∑_{i ∈ s} fᵢ(x) conj (gᵢ(y))` has
finite-dimensional range, hence is a compact operator. -/
theorem isCompactOperator_mercerCLM_finiteRank {ι : Type*} (s : Finset ι)
    (f g : ι → C(X, 𝕜))
    -- LEAN-ONLY: continuity of the finite-rank symbol; derivable, kept to name the operator
    (hc : Continuous fun p : X × X => ∑ i ∈ s, f i p.1 * conj (g i p.2)) :
    IsCompactOperator
      (mercerCLM (K := fun x y => ∑ i ∈ s, f i x * conj (g i y)) μ hc) := by
  sorry

/-- **The Mercer integral operator is compact.** -/
theorem isCompactOperator_mercerCLM {K : X → X → 𝕜} (hK : IsMercerKernel 𝕜 K) :
    IsCompactOperator (mercerCLM μ hK.continuous) := by
  sorry

end StatLean.NonparametricStatistics
