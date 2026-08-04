import StatLean.StatisticalModels.Coarsening.Defs

/-!
# Coarsening basics — Bool integration bricks, MCAR ⇒ MAR, propensity range

Small reusable facts for the missing-data slice: two-point integration over `Bool` (the
workhorse for every propensity computation), the taxonomy inclusion MCAR ⇒ MAR, the range of
the propensity, and probability preservation of the full/observed-data constructions.

**Reference.** D. B. Rubin, *Biometrika* **63** (1976), §2 (`Rubin76`): MCAR is the special
case of MAR with a data-free mechanism.

**Proof formalization notes.** `Bool` integrals are finite sums (`lintegral_fintype` /
`integral_fintype` with `Bool` enumeration); the MCAR ⇒ MAR proof exhibits the constant
kernel as `(Kernel.const 𝓧 ν).comap Prod.fst` (a `Kernel.ext` computation). Probability of
`fullLaw`/`observedLaw` is `compProd` + `map` preservation (the coarsening map is measurable
— product projections and an `if` on the Boolean coordinate).

**Bibliographic comments.** See `Coarsening.Defs`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatLean.StatisticalModels.Coarsening

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- Two-point lower integral over `Bool`. -/
theorem lintegral_bool (ν : Measure Bool) (f : Bool → ℝ≥0∞) :
    ∫⁻ b, f b ∂ν = f true * ν {true} + f false * ν {false} := by
  sorry

/-- Two-point Bochner integral over `Bool`. -/
theorem integral_bool (ν : Measure Bool) [IsFiniteMeasure ν] (f : Bool → ℝ) :
    ∫ b, f b ∂ν = (ν {true}).toReal * f true + (ν {false}).toReal * f false := by
  sorry

/-- The coarsening map is measurable. -/
theorem measurable_missingObserve :
    Measurable (missingObserve (𝓧 := 𝓧)) := by
  sorry

/-- **MCAR ⇒ MAR** (Rubin76 §2): a data-free mechanism trivially factors through the
covariate. -/
theorem IsMCAR.isMAR {ρ : Kernel (𝓧 × ℝ) Bool} (h : IsMCAR ρ) : IsMAR ρ := by
  sorry

/-- The propensity is nonnegative. -/
theorem propensity_nonneg (ρ' : Kernel 𝓧 Bool) (x : 𝓧) : 0 ≤ propensity ρ' x := by
  sorry

/-- The propensity of a Markov mechanism is at most one. -/
theorem propensity_le_one (ρ' : Kernel 𝓧 Bool) [IsMarkovKernel ρ'] (x : 𝓧) :
    propensity ρ' x ≤ 1 := by
  sorry

instance (Q : Measure (𝓧 × ℝ)) (ρ : Kernel (𝓧 × ℝ) Bool)
    [IsProbabilityMeasure Q] [IsMarkovKernel ρ] : IsProbabilityMeasure (fullLaw Q ρ) := by
  sorry

instance (Q : Measure (𝓧 × ℝ)) (ρ : Kernel (𝓧 × ℝ) Bool)
    [IsProbabilityMeasure Q] [IsMarkovKernel ρ] : IsProbabilityMeasure (observedLaw Q ρ) := by
  sorry

end StatLean.StatisticalModels.Coarsening
