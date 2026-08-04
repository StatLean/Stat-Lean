import StatLean.StatisticalModels.Survival.Cox.Defs

/-!
# Cox model identifiability — `(β, Λ₀)` is determined by the structure

**S5.3.** If a covariate-indexed family carries the proportional-hazards structure for two
parameter pairs, and the covariate design is rich enough (a base point plus covariate
differences spanning `ℝᵖ`), then the regression coefficients and the baseline agree:
the Cox parametrization is identified — exactly, by pure measure algebra, with no estimation
theory. Combined with the Core layer this makes `(β, Λ₀) ↦` model law injective on rich
designs; the semiparametric target `β = Prod.fst` is identified.

**Reference.** `Cox72 §2` (the scale ambiguity between `β`-intercepts and the baseline is
resolved exactly by covariate variation); A. A. Tsiatis, *Semiparametric Theory and Missing
Data*, Springer, 2006, Ch. 5 (verify §).

**Proof formalization notes.** From the two structures, `e^{⟪β,z⟫} • Λ₀ = e^{⟪β',z⟫} • Λ₀'`
for every design covariate `z`. Evaluating on a σ-finiteness-supplied set of finite positive
`Λ₀`-mass turns proportionality into the scalar identity
`e^{⟪β−β', z⟫} = c` on the design; against a base point, the linear functional
`⟪β − β', ·⟫` is constant on a spanning set of differences, forcing `β = β'` (injectivity of
`exp` + linearity), and then `Λ₀ = Λ₀'`. The scalar-extraction step is isolated as
`smul_measure_cancel` (a reusable brick).

**Bibliographic comments.** Identifiability of `(β, Λ₀)` under covariate variation is
folklore made precise in the semiparametric-efficiency literature (Tsiatis Ch. 5;
Begun–Hall–Huang–Wellner, *Ann. Statist.* **11** (1983) for the information geometry).
-/

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

namespace StatLean.StatisticalModels.Survival

variable {p : ℕ}

/-- Scalar extraction brick: equal positive scalings of a nonzero σ-finite measure have
equal scales. -/
theorem smul_measure_cancel {Λ : Measure ℝ} [SigmaFinite Λ] (hΛ : Λ ≠ 0) {c c' : ℝ≥0∞}
    -- LEAN-ONLY: finite nonzero scales (the Cox coefficients e^{⟪β,z⟫} are such)
    (hc : c ≠ 0) (hc' : c ≠ ⊤) (h : c • Λ = c' • Λ) : c = c' := by
  sorry

/-- **S5.3, Cox identifiability** (`Cox72 §2`; Tsiatis Ch. 5): two proportional-hazards
structures on one covariate-indexed family, over a design containing a base point whose
differences span `ℝᵖ`, have equal coefficients and equal baselines. -/
theorem coxParameters_eq_of_isProportionalHazards
    {P : EuclideanSpace ℝ (Fin p) → Measure ℝ} {β β' : EuclideanSpace ℝ (Fin p)}
    {Λ₀ Λ₀' : Measure ℝ} {Z : Set (EuclideanSpace ℝ (Fin p))}
    {z₀ : EuclideanSpace ℝ (Fin p)}
    -- USER-INPUT: both structures hold on the design; Cox72 §2
    (h : ∀ z ∈ Z, cumHazard (P z) = ENNReal.ofReal (Real.exp ⟪β, z⟫_ℝ) • Λ₀)
    (h' : ∀ z ∈ Z, cumHazard (P z) = ENNReal.ofReal (Real.exp ⟪β', z⟫_ℝ) • Λ₀')
    -- USER-INPUT: design richness — base point + spanning differences; Cox72 §2
    (hz₀ : z₀ ∈ Z)
    (hspan : Submodule.span ℝ ((fun z => z - z₀) '' Z) = ⊤)
    -- USER-INPUT: nondegenerate baseline; Cox72 §2
    (hΛ : Λ₀ ≠ 0)
    -- LEAN-ONLY: σ-finite baselines (to extract a finite positive-mass witness)
    [SigmaFinite Λ₀] [SigmaFinite Λ₀'] :
    β = β' ∧ Λ₀ = Λ₀' := by
  sorry

end StatLean.StatisticalModels.Survival
