import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Kullback–Leibler divergence — book form and tensorization (Wainwright §15.1.3)

Wainwright's KL divergence `D(ℚ ‖ ℙ) = ∫ q log(q/p) dν` (Eq. (15.7)) coincides with Mathlib's
`InformationTheory.klDiv ℚ ℙ` on probability measures (the argument we integrate against — `q`,
the density of `ℚ` — is the *first* argument in both conventions). We therefore reuse `klDiv`
directly and add only the Wainwright-facing algebra:

* `klDiv_prod_eq_add` — additivity over products (Eq. (15.11a), two-factor), from the Mathlib
  chain rule `klDiv_compProd_eq_add`.
* `klDiv_pi_eq_nsmul` — the i.i.d. `n`-fold tensorization `D(ℙ^{1:n} ‖ ℚ^{1:n}) = n·D(ℙ ‖ ℚ)`
  (Eq. (15.11b)).
* `sum_klDiv_mixture_le` — the mixture `Q̄ = (1/M) Σⱼ ℙⱼ` minimizes the average KL divergence
  `Q ↦ Σⱼ D(ℙⱼ ‖ Q)` (Exercise 15.11), used in the Yang–Barron bound (Eq. (15.52)).

Nonnegativity (Gibbs, Eq. (15.7) discussion) is automatic since `klDiv` is `ℝ≥0∞`-valued.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace StatLean.Minimaxity

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- **Additivity of KL over products** (Wainwright Eq. (15.11a), two-factor case):
`D(ℙ₁⊗ℙ₂ ‖ ℚ₁⊗ℚ₂) = D(ℙ₁ ‖ ℚ₁) + D(ℙ₂ ‖ ℚ₂)`. Follows from the Mathlib chain rule
`klDiv_compProd_eq_add` applied to the product written as a composition–product with a
constant kernel.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Eq. (15.11a). -/
theorem klDiv_prod_eq_add
    (μ₁ ν₁ : Measure α) (μ₂ ν₂ : Measure β)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₂] :
    klDiv (μ₁.prod μ₂) (ν₁.prod ν₂) = klDiv μ₁ ν₁ + klDiv μ₂ ν₂ := by
  sorry

/-- **I.i.d. tensorization of KL** (Wainwright Eq. (15.11b)):
`D(ℙ^{1:n} ‖ ℚ^{1:n}) = n · D(ℙ ‖ ℚ)` for the `n`-fold product measures.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Eq. (15.11b). -/
theorem klDiv_pi_eq_nsmul (n : ℕ) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    klDiv (Measure.pi fun _ : Fin n => μ) (Measure.pi fun _ : Fin n => ν)
      = n • klDiv μ ν := by
  sorry

/-- **The mixture minimizes the average KL divergence** (Wainwright Exercise 15.11):
for any distribution `Q`, the uniform mixture `Q̄ = (1/M) Σⱼ ℙⱼ` satisfies
`Σⱼ D(ℙⱼ ‖ Q̄) ≤ Σⱼ D(ℙⱼ ‖ Q)`. Used to obtain the Yang–Barron mutual-information bound.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.6, Exercise 15.11. -/
theorem sum_klDiv_mixture_le {M : ℕ} (P : Fin M → Measure α) (Q : Measure α)
    [∀ j, IsProbabilityMeasure (P j)] [IsProbabilityMeasure Q] :
    ∑ j, klDiv (P j) ((M : ℝ≥0∞)⁻¹ • ∑ k, P k) ≤ ∑ j, klDiv (P j) Q := by
  sorry

end StatLean.Minimaxity
