import Mathlib.Probability.ProbabilityMassFunction.Constructions
import StatLean.ExperimentalDesign.ForMathlib.PMFExpectation

/-!
# Product designs: independent randomization across strata

Blocked experiments and stratified surveys randomize **independently within each
block/stratum**.  The common probabilistic core is the finite product design: given
per-stratum designs `D b : PMF (Ω b)` over finitely many strata `b : B`, the product
design on `∀ b, Ω b` has mass `∏ b, D b (ω b)`.  This file constructs it and proves
the independence calculus that every blockwise moment computation reduces to:
factorization of expectations, marginals, vanishing covariance across strata, and
additivity of variances of stratum-wise sums:
$$\mathbb E\Bigl[\prod_b f_b(\omega_b)\Bigr] = \prod_b \mathbb E_{D_b}[f_b], \qquad
  \operatorname{Var}\Bigl(\sum_b f_b(\omega_b)\Bigr)
    = \sum_b \operatorname{Var}_{D_b}(f_b).$$

## Main results

* `productDesign`, `productDesign_apply` — the construction.
* `pmfExpect_productDesign_comp` — marginals.
* `pmfExpect_productDesign_prod` — factorization over strata.
* `pmfCov_productDesign_of_ne` — independence across strata.
* `pmfVar_productDesign_comp`, `pmfVar_productDesign_sum` — variance calculus.

**Reference.** R. Mead, *The Design of Experiments*, CUP, 1988, §9.4:
"randomisation is independent in different blocks" — the property that kills the
cross-block terms in the randomisation-theory variance computations; §9.6 (practical
randomisation block by block).  (`Mead §9.4`, `Mead §9.6`.)

**Proof formalization notes.**
* Normalisation of the product mass is the finite Fubini identity
  `∑_{ω : ∀ b, Ω b} ∏ b, D b (ω b) = ∏ b, ∑_{x : Ω b}, D b x = 1` in `ℝ≥0∞`
  (`Finset.prod_univ_sum` shape), stated separately as `sum_prod_pmf` so the
  `PMF.ofFintype` obligation is a named lemma.
* All moment identities then follow from the same Fubini rearrangement in `ℝ`; the
  cross-stratum covariance vanishes because expectations factor.
* `pmfVar_productDesign_sum` combines `pmfVar_sum` with the vanishing off-diagonal
  covariances; it is the "no cross-block terms" step of `Mead §9.4`.
-/

open scoped ENNReal

namespace StatLean.ExperimentalDesign

variable {B : Type*} [Fintype B] [DecidableEq B]
variable {Ω : B → Type*} [∀ b, Fintype (Ω b)] [∀ b, DecidableEq (Ω b)]

/-- Normalisation of the product mass: the total mass of `ω ↦ ∏ b, D b (ω b)` is
one (finite Fubini in `ℝ≥0∞`). -/
theorem sum_prod_pmf (D : ∀ b, PMF (Ω b)) :
    ∑ ω : ∀ b, Ω b, ∏ b, D b (ω b) = 1 := by
  sorry

/-- The **product design**: independent randomization across the strata, with mass
`∏ b, D b (ω b)` (`Mead §9.4`, independence of randomisation in different blocks). -/
noncomputable def productDesign (D : ∀ b, PMF (Ω b)) : PMF (∀ b, Ω b) :=
  PMF.ofFintype (fun ω => ∏ b, D b (ω b)) (sum_prod_pmf D)

@[simp]
theorem productDesign_apply (D : ∀ b, PMF (Ω b)) (ω : ∀ b, Ω b) :
    productDesign D ω = ∏ b, D b (ω b) := by
  sorry

/-- **Marginals of the product design**: a statistic of one stratum has its
single-stratum expectation. -/
theorem pmfExpect_productDesign_comp (D : ∀ b, PMF (Ω b)) (b₀ : B)
    (f : Ω b₀ → ℝ) :
    pmfExpect (productDesign D) (fun ω => f (ω b₀)) = pmfExpect (D b₀) f := by
  sorry

/-- **Factorization over strata**: the expectation of a product of per-stratum
statistics is the product of expectations. -/
theorem pmfExpect_productDesign_prod (D : ∀ b, PMF (Ω b))
    (f : ∀ b, Ω b → ℝ) :
    pmfExpect (productDesign D) (fun ω => ∏ b, f b (ω b))
      = ∏ b, pmfExpect (D b) (f b) := by
  sorry

/-- **Independence across strata**: statistics of distinct strata are
uncorrelated. -/
theorem pmfCov_productDesign_of_ne (D : ∀ b, PMF (Ω b)) {b b' : B}
    -- LEAN-ONLY: distinct strata; within one stratum the covariance is unconstrained
    (hbb' : b ≠ b') (f : Ω b → ℝ) (g : Ω b' → ℝ) :
    pmfCov (productDesign D) (fun ω => f (ω b)) (fun ω => g (ω b')) = 0 := by
  sorry

/-- The variance of a single-stratum statistic under the product design is its
single-stratum variance. -/
theorem pmfVar_productDesign_comp (D : ∀ b, PMF (Ω b)) (b₀ : B)
    (f : Ω b₀ → ℝ) :
    pmfVar (productDesign D) (fun ω => f (ω b₀)) = pmfVar (D b₀) f := by
  sorry

/-- **Additivity of variance over strata** (`Mead §9.4`, no cross-block terms):
the variance of a sum of per-stratum statistics is the sum of the per-stratum
variances. -/
theorem pmfVar_productDesign_sum (D : ∀ b, PMF (Ω b)) (f : ∀ b, Ω b → ℝ) :
    pmfVar (productDesign D) (fun ω => ∑ b, f b (ω b))
      = ∑ b, pmfVar (D b) (f b) := by
  sorry

end StatLean.ExperimentalDesign
