import StatLean.ConcentrationInequalities.VC.LawOfLargeNumbersCountable
import Mathlib.Order.SymmDiff

/-!
# VC generalization bound for empirical risk minimization

Boolean learning: target `T = 𝟙_Θ`, hypotheses `f = 𝟙_S` for `S` in a class
$\mathcal{C}$ with $\mathrm{vc}(\mathcal{C}) \le d$. The risk is
$R(f) = \mathbb{E}(f(X) - T(X))^2 = \mu(S \,\Delta\, \Theta)$ and the
empirical risk is $R_n(f) = \mu_n(S \,\Delta\, \Theta)$. For the empirical
risk minimizer $f^*_n$,
$$ \mathbb{E}\, R(f^*_n) \;\le\; \inf_{f \in \mathcal{F}} R(f)
   \;+\; 10800 \sqrt{d/n}. $$

**Reference.** Roman Vershynin, *High-Dimensional Probability*, 2nd ed.,
Cambridge University Press, §8.4.3, Theorem 8.4.5; Exercise 8.29 (invariance
of VC dimension under the loss transformation); Eq. (8.40) (excess-risk
bound).

**Proof formalization notes.** For Boolean `f, T`: `(f − T)² = 𝟙_{S ∆ Θ}`
pointwise, so the loss class is the symmetric-difference image
`(· ∆ Θ) '' 𝒞` — Exercise 8.29 (we prove it: shattering is preserved under
the labeling bijection `T ↦ T ∆ (Λ ∩ Θ)`). Frozen numeral
`10800 = 2 × 5400` (Eq. (8.40) excess risk ≤ 2·sup-deviation, then
`vc_lln_countable` on the loss class at the same `d`). Hypothesis notes:
`hERM` (the minimizer property) and `Sn` are **data** (USER-INPUT — the
book's Definition 8.4.3 presupposes an ERM); `hRmeas` is LEAN-ONLY
selection regularity (the book's `E R(f*_n)` silently assumes the risk of
the selected hypothesis is measurable in the sample); `Countable 𝒞` is
LEAN-ONLY per the batch sup policy. Work-item single named-sorry fallback:
`vcDim_symmDiff_image` (Exercise 8.29); the excess-risk chain
(`excess_risk_le_two_mul_sup`) and the integral assembly must close.

**Bibliographic comments.** Theorem 8.4.5 is the classical
Vapnik–Chervonenkis generalization bound in the in-expectation form of HDP
§8.4; the reduction of Boolean squared loss to symmetric differences is
folklore (see HDP Exercise 8.29 and the Notes to Chapter 8).
-/

open MeasureTheory ProbabilityTheory symmDiff
open scoped ENNReal NNReal BigOperators

namespace StatLean.ConcentrationInequalities

variable {Ω : Type*}

/-- Shattering is invariant under symmetric difference with a fixed target
(HDP Exercise 8.29 core): the labeling bijection `T ↦ T ∆ (Λ ∩ Θ)` matches
traces of `C` with traces of `(· ∆ Θ) '' C`. -/
theorem shatters_symmDiff_image {C : Set (Set Ω)} (Θ : Set Ω)
    (Λ : Finset Ω) :
    Shatters ((· ∆ Θ) '' C) Λ ↔ Shatters C Λ := by sorry

/-- **Exercise 8.29** (HDP §8.4.3, we prove it): the loss class of a Boolean
class has the same VC dimension, `vc({(f − T)² : f ∈ ℱ}) = vc(ℱ)`. This
work item's single named-sorry fallback. -/
theorem vcDim_symmDiff_image {C : Set (Set Ω)} (Θ : Set Ω) :
    vcDim ((· ∆ Θ) '' C) = vcDim C := by sorry

/-- Pointwise excess-risk bound (HDP §8.4.3, Eq. (8.40)):
`R(f*_n) ≤ R(f₀) + 2 sup_{f ∈ ℱ} |R_n(f) − R(f)|` for any ERM `Sn` and any
competitor `S₀`, at a fixed sample. -/
lemma excess_risk_le_two_mul_sup [MeasurableSpace Ω] {C : Set (Set Ω)}
    -- LEAN-ONLY: nonempty class so the sup is genuine
    (hCne : C.Nonempty)
    {Θ Sn S₀ : Set Ω}
    -- USER-INPUT: the selected hypothesis lies in the class; HDP Def 8.4.3
    (hSn : Sn ∈ C)
    -- USER-INPUT: the competitor lies in the class; HDP Thm 8.4.5
    (hS₀ : S₀ ∈ C)
    {n : ℕ} (x : Fin n → Ω) {μ : Measure Ω} [IsProbabilityMeasure μ]
    -- USER-INPUT: empirical-risk minimality of Sn at this sample;
    -- HDP Definition 8.4.3 (ERM is data)
    (hERM : ∀ S ∈ C, empFrac x (Sn ∆ Θ) ≤ empFrac x (S ∆ Θ)) :
    μ.real (Sn ∆ Θ) ≤ μ.real (S₀ ∆ Θ) +
      2 * ⨆ S ∈ C, |empFrac x (S ∆ Θ) - μ.real (S ∆ Θ)| := by sorry

/-- **Theorem 8.4.5 (VC generalization bound)** (HDP §8.4.3; frozen numeral
`10800 = 2 × 5400`, formula in the module notes): the expected risk of the
empirical risk minimizer is within `10800·√d/√n` of the best risk in the
class. -/
theorem vc_generalization {Ξ : Type*} [MeasurableSpace Ξ] [MeasurableSpace Ω]
    {P : Measure Ξ} [IsProbabilityMeasure P] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℕ → Ξ → Ω}
    -- LEAN-ONLY: measurability of the data stream; regularity
    (hXmeas : ∀ i, Measurable (X i))
    -- USER-INPUT: jointly independent sample; HDP Thm 8.4.5
    (hindep : iIndepFun X P)
    -- USER-INPUT: each X i has law μ; HDP Thm 8.4.5 (map form)
    (hlaw : ∀ i, P.map (X i) = μ)
    {C : Set (Set Ω)}
    -- LEAN-ONLY: countable class per the batch sup policy (documented)
    (hCc : C.Countable)
    -- LEAN-ONLY: nonempty class
    (hCne : C.Nonempty)
    -- LEAN-ONLY: measurable members
    (hCmeas : ∀ S ∈ C, MeasurableSet S)
    {Θ : Set Ω}
    -- USER-INPUT: measurable Boolean target; HDP §8.4 setting
    (hΘ : MeasurableSet Θ)
    {d : ℕ}
    -- USER-INPUT: VC dimension bound on the hypothesis class; HDP Thm 8.4.5
    (hd : vcDim C ≤ (d : ℕ∞))
    -- USER-INPUT: 1 ≤ d; HDP §8.4.3
    (hd1 : 1 ≤ d)
    {n : ℕ}
    -- USER-INPUT: at least one sample point; HDP §8.4.3 (implicit)
    (hn : 1 ≤ n)
    (Sn : Ξ → Set Ω)
    -- USER-INPUT: the learner's output lies in the class; HDP Def 8.4.3
    (hSn_mem : ∀ ξ, Sn ξ ∈ C)
    -- USER-INPUT: empirical-risk minimality (ERM is data); HDP Def 8.4.3
    (hERM : ∀ ξ, ∀ S ∈ C, empFrac (fun i : Fin n => X i ξ) (Sn ξ ∆ Θ) ≤
      empFrac (fun i : Fin n => X i ξ) (S ∆ Θ))
    -- LEAN-ONLY: selection regularity — the sample-indexed risk of the
    -- chosen hypothesis is a.e.-strongly-measurable (the book's E R(f*_n)
    -- presupposes this); no scope change
    (hRmeas : MeasureTheory.AEStronglyMeasurable
      (fun ξ => μ.real (Sn ξ ∆ Θ)) P)
    {S₀ : Set Ω}
    -- USER-INPUT: competitor hypothesis realizing (or approximating) the
    -- best risk; HDP Thm 8.4.5
    (hS₀ : S₀ ∈ C) :
    ∫ ξ, μ.real (Sn ξ ∆ Θ) ∂P ≤
      μ.real (S₀ ∆ Θ) + 10800 * Real.sqrt d / Real.sqrt n := by sorry

end StatLean.ConcentrationInequalities
