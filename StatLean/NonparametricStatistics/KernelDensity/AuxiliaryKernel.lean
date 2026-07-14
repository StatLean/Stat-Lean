import StatLean.NonparametricStatistics.KernelDensity.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Existence of bounded compactly supported kernels of arbitrary order

For every `ℓ` there is a kernel of order `ℓ` that is bounded and supported in `[−1, 1]`.

This existence result is the auxiliary device behind the uniform bound on Hölder densities
(`KernelDensity/UniformDensityBound.lean`): applying the bias inequality with bandwidth `1`
and such a kernel `K*` yields `p(x) ≤ C₂* + sup|K*|` uniformly over the density class.

**Proof formalization notes.** Instead of the classical Legendre-polynomial construction, use
a superposition of boxes: with `K₀ = ½·𝟙_{[−1,1]}` and distinct scales `a_r ∈ (0, 1]`,
`r = 0, …, ℓ`, set `K(u) = ∑ r, c_r·a_r⁻¹·K₀(u/a_r)`. Odd moments vanish by symmetry; the even
moments of `a⁻¹K₀(·/a)` are `a^{2q}/(2q+1)`, so the moment conditions become a linear system
in `c` whose matrix is (a rescaling of) a Vandermonde matrix in the distinct values `a_r²` —
invertible by `Matrix.det_vandermonde_ne_zero_iff`. Choosing `c` as the solution of the system
with right-hand side `e₀` gives `∫K = 1` and vanishing moments up to order... to cover both
parities cleanly it suffices to solve for even moments `0, 2, …, 2⌈ℓ/2⌉` (odd moments are
automatically `0`), i.e. take `⌈ℓ/2⌉ + 1` boxes. Boundedness and support are clear from the
construction.

**Bibliographic comments.** Kernels of arbitrary order are classically constructed from
orthogonal polynomial systems (cf. G. Szegő, *Orthogonal Polynomials*, 4th ed., AMS, 1975);
the box-superposition construction used here is a folklore alternative.
-/

namespace StatLean.NonparametricStatistics

/-- **Existence of a bounded, compactly supported kernel of order `ℓ`**: there are `K` and
`Kmax` with `K` of order `ℓ`, `|K| ≤ Kmax`, and `K = 0` outside `[−1, 1]`. -/
theorem exists_bounded_kernel_of_order (ℓ : ℕ) :
    ∃ (K : ℝ → ℝ) (Kmax : ℝ), 0 < Kmax ∧ IsKernelOfOrder K ℓ ∧
      (∀ u, |K u| ≤ Kmax) ∧ ∀ u, u ∉ Set.Icc (-1 : ℝ) 1 → K u = 0 := by
  sorry

end StatLean.NonparametricStatistics
