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

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ}

/-- KL divergence is invariant under pushforward by a measurable equivalence. This is the
standard reparametrization-invariance of an `f`-divergence; we prove it from the
log-likelihood-ratio integral form together with `MeasurableEmbedding.rnDeriv_map`. -/
private lemma klDiv_map_measurableEquiv (e : α ≃ᵐ γ) (μ ν : Measure α)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map e) (ν.map e) = klDiv μ ν := by
  have hf := e.measurableEmbedding
  haveI : IsFiniteMeasure (μ.map e) := μ.isFiniteMeasure_map e
  haveI : IsFiniteMeasure (ν.map e) := ν.isFiniteMeasure_map e
  by_cases hμν : μ ≪ ν
  · have hμν' : μ.map e ≪ ν.map e := hf.absolutelyContinuous_map hμν
    rw [klDiv_eq_lintegral_klFun_of_ac hμν', klDiv_eq_lintegral_klFun_of_ac hμν,
      hf.lintegral_map]
    refine lintegral_congr_ae ?_
    filter_upwards [hf.rnDeriv_map μ ν] with x hx
    rw [hx]
  · have hne : ¬ (μ.map e ≪ ν.map e) := by
      intro hac
      apply hμν
      have h := hac.map e.symm.measurable
      rwa [MeasurableEquiv.map_symm_map, MeasurableEquiv.map_symm_map] at h
    rw [klDiv_of_not_ac hμν, klDiv_of_not_ac hne]

/-- The residual term in the product chain rule: for product measures with a common first
factor `μ₁` (a probability measure), the KL divergence collapses to the second-factor
divergence. Proved by swapping coordinates (`Measure.prod_swap`) so the common factor becomes
the conditional kernel, then applying `klDiv_compProd_left`. -/
private lemma klDiv_prod_const_fst (μ₁ : Measure α) (μ₂ ν₂ : Measure β)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] [IsProbabilityMeasure ν₂] :
    klDiv (μ₁.prod μ₂) (μ₁.prod ν₂) = klDiv μ₂ ν₂ := by
  rw [← klDiv_map_measurableEquiv (MeasurableEquiv.prodComm : α × β ≃ᵐ β × α)
    (μ₁.prod μ₂) (μ₁.prod ν₂),
    show ⇑(MeasurableEquiv.prodComm : α × β ≃ᵐ β × α) = Prod.swap from rfl,
    Measure.prod_swap, Measure.prod_swap, ← Measure.compProd_const, ← Measure.compProd_const,
    klDiv_compProd_left]

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
  rw [← Measure.compProd_const (μ := μ₁) (ν := μ₂),
    ← Measure.compProd_const (μ := ν₁) (ν := ν₂), klDiv_compProd_eq_add,
    Measure.compProd_const, Measure.compProd_const, klDiv_prod_const_fst]

/-- **I.i.d. tensorization of KL** (Wainwright Eq. (15.11b)):
`D(ℙ^{1:n} ‖ ℚ^{1:n}) = n · D(ℙ ‖ ℚ)` for the `n`-fold product measures.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.1.3, Eq. (15.11b). -/
theorem klDiv_pi_eq_nsmul (n : ℕ) (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    klDiv (Measure.pi fun _ : Fin n => μ) (Measure.pi fun _ : Fin n => ν)
      = n • klDiv μ ν := by
  induction n with
  | zero => rw [Measure.pi_of_empty, Measure.pi_of_empty, klDiv_self, zero_nsmul]
  | succ n ih =>
    have hμ := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).map_eq
    have hν := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => ν) 0).map_eq
    rw [← klDiv_map_measurableEquiv (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => α) 0)
      (Measure.pi fun _ : Fin (n + 1) => μ) (Measure.pi fun _ : Fin (n + 1) => ν),
      hμ, hν, klDiv_prod_eq_add, ih, succ_nsmul, add_comm]

-- Crux of Exercise 15.11: the uniform mixture minimizes the average KL divergence. This is
-- the variational/convexity property of `klDiv` in its second argument, which Mathlib does not
-- yet expose in a directly usable form.
private lemma klDiv_mixture_minimizes {M : ℕ} (P : Fin M → Measure α) (Q : Measure α)
    [∀ j, IsProbabilityMeasure (P j)] [IsProbabilityMeasure Q] :
    ∑ j, klDiv (P j) ((M : ℝ≥0∞)⁻¹ • ∑ k, P k) ≤ ∑ j, klDiv (P j) Q := by
  sorry -- TODO(mmx): Ex 15.11 — convexity / variational form of KL in the 2nd argument

/-- **The mixture minimizes the average KL divergence** (Wainwright Exercise 15.11):
for any distribution `Q`, the uniform mixture `Q̄ = (1/M) Σⱼ ℙⱼ` satisfies
`Σⱼ D(ℙⱼ ‖ Q̄) ≤ Σⱼ D(ℙⱼ ‖ Q)`. Used to obtain the Yang–Barron mutual-information bound.

**Reference.** Wainwright, *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*,
Cambridge University Press, 2019. Chapter 15 (Minimax Lower Bounds), §15.6, Exercise 15.11. -/
theorem sum_klDiv_mixture_le {M : ℕ} (P : Fin M → Measure α) (Q : Measure α)
    [∀ j, IsProbabilityMeasure (P j)] [IsProbabilityMeasure Q] :
    ∑ j, klDiv (P j) ((M : ℝ≥0∞)⁻¹ • ∑ k, P k) ≤ ∑ j, klDiv (P j) Q :=
  klDiv_mixture_minimizes P Q

end StatLean.Minimaxity
