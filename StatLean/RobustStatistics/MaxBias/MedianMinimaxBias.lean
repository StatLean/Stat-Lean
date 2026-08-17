import StatLean.RobustStatistics.MaxBias.MaxBiasLocation
import StatLean.RobustStatistics.Core.Equivariance
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The minimax-bias property of the median (Huber)

The classical capstone of maximum-bias theory (`MMY §3.8.5`, after Huber (1964)): over
a symmetric *unimodal* center `F₀`, **no location-equivariant functional has smaller
maximum bias than the median**. The witness pair is explicit: `F₊` keeps the density
`(1−ε)f₀` up to the median's own maximum bias `b_ε` (`MMY (3.68)`) and pastes the
shifted density `(1−ε)f₀(· − 2b_ε)` beyond it; `F₋` is `F₊` shifted left by `2b_ε`.
Both are `ε`-contaminations of `F₀` — nonnegativity of the contaminating density is
exactly unimodality, its total mass is exactly the quantile equation — and location
equivariance forces `T(F₊) − T(F₋) = 2b_ε`, so one of the two values is at least `b_ε`
in absolute value.

* `minimaxWitnessDensity` — the contaminating density `g` of `MMY §3.8.5`.
* `minimaxWitnessDensity_nonneg` / `integral_minimaxWitnessDensity` — `g` is a density.
* `medianMinimaxPlus_eq_contaminate` — `F₊ ∈ F(F₀, ε)`.
* `medianMinimaxMinus_eq_contaminate` — `F₋ = F₊(· + 2b_ε) ∈ F(F₀, ε)`.
* `locationEquivariant_maxBias_ge_median` — the pigeonhole conclusion.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera,
*Robust Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.)
§3.8.5 ("The minimax bias property of the median"), using (3.68); the result is
P. J. Huber, *Robust estimation of a location parameter*, Ann. Math. Statist. 35
(1964) (bib note).
-/

open MeasureTheory Filter Topology

namespace StatLean.RobustStatistics

/-- The symmetric unimodal center as a Lebesgue density measure: `P₀ = f₀ · Leb`. -/
noncomputable def densityMeasure (f₀ : ℝ → ℝ) : Measure ℝ :=
  MeasureTheory.volume.withDensity fun x => ENNReal.ofReal (f₀ x)

/-- **The minimax witness density** (`MMY §3.8.5`, the display for `g`):
`g(x) = ((1−ε)/ε) (f₀(x − 2b_ε) − f₀(x))` for `x > b_ε` and `0` otherwise. -/
noncomputable def minimaxWitnessDensity (f₀ : ℝ → ℝ) (bε ε : ℝ) (x : ℝ) : ℝ :=
  if bε < x then (1 - ε) / ε * (f₀ (x - 2 * bε) - f₀ x) else 0

/-- **The witness density is nonnegative** (`MMY §3.8.5`, "it is nonnegative, since
`x ∈ (b_ε, 2b_ε)` implies `|x − 2b_ε| ≤ |x|`, and the unimodality of `f₀` yields
`f₀(x − 2b_ε) ≥ f₀(x)`; the same happens if `x > 2b_ε`"). -/
theorem minimaxWitnessDensity_nonneg {f₀ : ℝ → ℝ} {bε ε : ℝ}
    -- USER-INPUT: symmetric unimodal density; MMY §3.8.5 ("f₀(x) a nonincreasing
    -- function of |x|")
    (hsym : ∀ x, f₀ (-x) = f₀ x)
    (huni : ∀ a b : ℝ, 0 ≤ a → a ≤ b → f₀ b ≤ f₀ a)
    (hbε : 0 ≤ bε) (hε : 0 < ε) (hε1 : ε < 1) (x : ℝ) :
    0 ≤ minimaxWitnessDensity f₀ bε ε x := by
  sorry

/-- **The witness density has total mass one** (`MMY §3.8.5`, "its integral equals one,
since by (3.68), `∫_{b_ε}^∞ (f₀(x − 2b_ε) − f₀(x)) dx = 2F₀(b_ε) − 1 = ε/(1−ε)`"). -/
theorem integral_minimaxWitnessDensity {f₀ : ℝ → ℝ} {bε ε : ℝ}
    -- LEAN-ONLY: measurability + integrability of the density; regularity
    (hmeas : Measurable f₀) (hint : Integrable f₀)
    (hnonneg : ∀ x, 0 ≤ f₀ x)
    -- USER-INPUT: f₀ is a probability density; MMY §3.8.5
    (hone : ∫ x, f₀ x = 1)
    (hsym : ∀ x, f₀ (-x) = f₀ x)
    (huni : ∀ a b : ℝ, 0 ≤ a → a ≤ b → f₀ b ≤ f₀ a)
    (hbε : 0 ≤ bε) (hε : 0 < ε) (hε1 : ε < 1)
    -- USER-INPUT: b_ε solves the median's maximum-bias quantile equation; MMY (3.68)
    (hquant : ∫ x in Set.Iic bε, f₀ x = 1 / (2 * (1 - ε))) :
    ∫ x, minimaxWitnessDensity f₀ bε ε x = 1 := by
  sorry

/-- **`F₊` is an `ε`-contamination of `F₀`** (`MMY §3.8.5`, "`f₊` belongs to
`F(F₀, ε)`; in fact it can be written as `f₊ = (1−ε)f₀ + εg`"): the paste-and-shift
density equals the mixture of `P₀` with the witness. -/
theorem medianMinimaxPlus_eq_contaminate {f₀ : ℝ → ℝ} {bε ε : ℝ}
    (hmeas : Measurable f₀) (hint : Integrable f₀) (hnonneg : ∀ x, 0 ≤ f₀ x)
    (hone : ∫ x, f₀ x = 1)
    (hsym : ∀ x, f₀ (-x) = f₀ x)
    (huni : ∀ a b : ℝ, 0 ≤ a → a ≤ b → f₀ b ≤ f₀ a)
    (hbε : 0 ≤ bε) (hε : 0 < ε) (hε1 : ε < 1)
    (hquant : ∫ x in Set.Iic bε, f₀ x = 1 / (2 * (1 - ε))) :
    densityMeasure (fun x => if x ≤ bε then (1 - ε) * f₀ x
        else (1 - ε) * f₀ (x - 2 * bε))
      = contaminate (densityMeasure f₀)
          (densityMeasure (minimaxWitnessDensity f₀ bε ε)) ε := by
  sorry

/-- **`F₋` is also an `ε`-contamination of `F₀`** (`MMY §3.8.5`, "define
`F₋(x) = F₊(x + 2b_ε)`, which also belongs to `F(F₀, ε)` by the same argument"): the
left shift of `F₊` by `2b_ε` lies in the gross-error neighbourhood of `P₀`. -/
theorem medianMinimaxMinus_mem_nbhd {f₀ : ℝ → ℝ} {bε ε : ℝ}
    (hmeas : Measurable f₀) (hint : Integrable f₀) (hnonneg : ∀ x, 0 ≤ f₀ x)
    (hone : ∫ x, f₀ x = 1)
    (hsym : ∀ x, f₀ (-x) = f₀ x)
    (huni : ∀ a b : ℝ, 0 ≤ a → a ≤ b → f₀ b ≤ f₀ a)
    (hbε : 0 ≤ bε) (hε : 0 < ε) (hε1 : ε < 1)
    (hquant : ∫ x in Set.Iic bε, f₀ x = 1 / (2 * (1 - ε))) :
    (densityMeasure (fun x => if x ≤ bε then (1 - ε) * f₀ x
        else (1 - ε) * f₀ (x - 2 * bε))).map (· + (-(2 * bε)))
      ∈ grossErrorNbhd (densityMeasure f₀) ε := by
  sorry

/-- **The minimax-bias property of the median** (`MMY §3.8.5`; Huber (1964)): for a
symmetric unimodal center `F₀` and any functional `T` that is location equivariant on a
domain containing the witness pair, some member of the `ε`-gross-error neighbourhood of
`F₀` has `|T| ≥ b_ε` — the median's own maximum bias (`MMY (3.68)`,
`MaxBias/MaxBiasLocation.lean`). Equivariance gives `T(F₊) − T(F₋) = 2b_ε`, "and hence
`|T(F₊)|` and `|T(F₋)|` cannot both be less than `b_ε`". -/
theorem locationEquivariant_maxBias_ge_median {f₀ : ℝ → ℝ} {bε ε : ℝ}
    {T : Measure ℝ → ℝ} {𝒟 : Set (Measure ℝ)}
    (hmeas : Measurable f₀) (hint : Integrable f₀) (hnonneg : ∀ x, 0 ≤ f₀ x)
    (hone : ∫ x, f₀ x = 1)
    -- USER-INPUT: symmetric unimodal center; MMY §3.8.5
    (hsym : ∀ x, f₀ (-x) = f₀ x)
    (huni : ∀ a b : ℝ, 0 ≤ a → a ≤ b → f₀ b ≤ f₀ a)
    (hbε : 0 ≤ bε) (hε : 0 < ε) (hε1 : ε < 1)
    -- USER-INPUT: b_ε solves the median's maximum-bias quantile equation; MMY (3.68)
    (hquant : ∫ x in Set.Iic bε, f₀ x = 1 / (2 * (1 - ε)))
    -- USER-INPUT: T is location equivariant on a domain containing the witness; MMY
    -- §3.8.5 ("let θ̂ be any location equivariant estimator")
    (hT : IsLocationEquivariantOn T 𝒟)
    (hD : densityMeasure (fun x => if x ≤ bε then (1 - ε) * f₀ x
        else (1 - ε) * f₀ (x - 2 * bε)) ∈ 𝒟) :
    ∃ F ∈ grossErrorNbhd (densityMeasure f₀) ε, bε ≤ |T F| := by
  sorry

end StatLean.RobustStatistics
