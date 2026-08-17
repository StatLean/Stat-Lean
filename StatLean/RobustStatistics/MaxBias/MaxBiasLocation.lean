import StatLean.RobustStatistics.MEstimation.MLocationFunctional
import StatLean.RobustStatistics.MEstimation.AsymptoticBreakdown
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The maximum asymptotic bias of location M-estimators — the sharp `b_ε` bound

Between the infinitesimal (influence function) and the catastrophic (breakdown point)
regimes sits the **maximum-bias curve** `MB(ε)` (`MMY §3.3`): the worst asymptotic bias
an estimator suffers over the full `ε`-contamination neighbourhood. For a location
M-estimator with nondecreasing bounded odd score `ψ`, `k = ψ(∞)`, symmetric center `P`,
and increasing population "shift score" `g(b) = ∫ ψ(x + b) dP`, the maximum bias is the
solution `b_ε` of

  `g(b) = k ε / (1 − ε)`    (`MMY (3.66)`),

every contaminated root lies in `[−b_ε, b_ε]` (`MMY (3.67)` manipulation), and
point-mass contamination pushed to `±∞` attains the bound. For the median (`ψ = sign`,
`k = 1`) the equation solves to the quantile formula

  `b_ε = F₀⁻¹( 1/(2(1 − ε)) )`    (`MMY (3.68)`),

stated here as the identity `g(b) = 2 F₀(b) − 1` for atomless `P`.

* `shiftScore` — `g(b) = ∫ ψ(x + b) dP`, with its oddness from symmetry.
* `mLocationRoot_abs_le_maxBias` — the sharp bound (`MMY §3.8.4`, proof of (3.66)).
* `maxBias_attained` — attainment in the limit `G = δ_{x₀}`, `x₀ → ∞`.
* `shiftScore_sign` — the median's `g(b) = 2 F₀(b) − 1` (`MMY (3.68)` route).

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera,
*Robust Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.)
§3.3 (the neighbourhood `F_{ε,θ}` and `MB`), §3.8.4 (eqs. (3.66)–(3.68) with proofs).
The minimax-bias optimality of the median over location-equivariant functionals is the
companion file `MaxBias/MedianMinimaxBias.lean` (`MMY §3.8.5`).
-/

open MeasureTheory Filter Topology

namespace StatLean.RobustStatistics

/-- **The shift score** `g(b) = ∫ ψ(x + b) dP` (`MMY §3.8.4`, "define for brevity the
function `g(b) = E_{F₀} ψ(x + b)`"): the population score of `MLocationFunctional`
evaluated at `−b`, `g(b) = mLocationScore ψ P (−b)`. -/
noncomputable def shiftScore (ψ : ℝ → ℝ) (P : Measure ℝ) (b : ℝ) : ℝ :=
  mLocationScore ψ P (-b)

/-- The shift score is odd for an odd score and a symmetric center (`MMY §3.8.4`,
"which is odd"): if `P` is invariant under negation and `ψ(−u) = −ψ(u)`, then
`g(−b) = −g(b)`. -/
theorem shiftScore_neg {ψ : ℝ → ℝ} {P : Measure ℝ} [IsProbabilityMeasure P] {b : ℝ}
    -- USER-INPUT: odd score; MMY §3.8.4 (k₁ = k₂ = k)
    (hψ_odd : ∀ u, ψ (-u) = -ψ u)
    -- USER-INPUT: symmetric center, F₀ symmetric about zero; MMY §3.8.4
    (hsym : P.map Neg.neg = P)
    -- LEAN-ONLY: measurability of ψ, to transport the integral; regularity
    (hψ_meas : Measurable ψ) :
    shiftScore ψ P (-b) = -shiftScore ψ P b := by
  sorry

/-- **The sharp maximum-bias bound** (`MMY §3.8.4`, the proof of (3.66) via (3.67)):
let `ψ` be nondecreasing, bounded by `k`, and odd; let `P` be symmetric with strictly
increasing shift score `g`, and let `b_ε` solve `g(b_ε) = kε/(1−ε)` (`MMY (3.66)`).
Then for `ε < 1/2`, every root `θ` of every `ε`-contaminated M-equation satisfies
`|θ| ≤ b_ε`: from `(1−ε) g(−θ) + ε E_G ψ(x − θ) = 0` (`MMY (3.67)`) and `|E_G ψ| ≤ k`,
`|g(θ)| ≤ kε/(1−ε) = g(b_ε)`, and strict monotonicity concludes.

This refines Round-1's `mLocationRoot_bounded_of_contamination` (`MMY (3.21)`), which
produced *some* bound `B`; here the bound is the exact maximum-bias value `b_ε`. -/
theorem mLocationRoot_abs_le_maxBias {ψ : ℝ → ℝ} {P : Measure ℝ}
    [IsProbabilityMeasure P] {k ε bε : ℝ}
    -- USER-INPUT: nondecreasing odd score bounded by k = ψ(∞); MMY §3.8.4
    (hψm : Monotone ψ) (hψ_odd : ∀ u, ψ (-u) = -ψ u) (hψb : ∀ u, |ψ u| ≤ k)
    (hk : 0 < k)
    -- USER-INPUT: symmetric center; MMY §3.8.4 ("F₀ is symmetric about zero")
    (hsym : P.map Neg.neg = P)
    -- USER-INPUT: strictly increasing shift score; MMY §3.8.4 ("it will be assumed
    -- that g is increasing; this holds either if ψ is increasing, or if F₀ has
    -- positive density everywhere")
    (hg : StrictMono (shiftScore ψ P))
    -- USER-INPUT: contamination level; MMY §3.8.4 ("let ε < 0.5")
    (hε0 : 0 ≤ ε) (hε : ε < 1 / 2)
    -- USER-INPUT: b_ε solves the maximum-bias equation; MMY (3.66)
    (hbε : shiftScore ψ P bε = k * ε / (1 - ε)) :
    ∀ (Q : Measure ℝ), IsProbabilityMeasure Q → ∀ θ : ℝ,
      IsMLocationRoot ψ (contaminate P Q ε) θ → |θ| ≤ bε := by
  sorry

/-- **The maximum bias is attained in the limit** (`MMY §3.8.4`, "by letting
`G = δ_{x₀}` in (3.67) with `x₀ → ±∞`, we see that the bound is attained"): for a
*continuous* score, point-mass contamination far enough out produces roots within any
`η` of `b_ε`. -/
theorem maxBias_attained {ψ : ℝ → ℝ} {P : Measure ℝ}
    [IsProbabilityMeasure P] {k ε bε : ℝ}
    -- USER-INPUT: continuous nondecreasing odd score with limit k at +∞; MMY §3.8.4
    -- (continuity is the Thm 10.1-style regularity used for root existence)
    (hψc : Continuous ψ) (hψm : Monotone ψ) (hψ_odd : ∀ u, ψ (-u) = -ψ u)
    (htop : Tendsto ψ atTop (𝓝 k)) (hk : 0 < k)
    -- USER-INPUT: symmetric center; MMY §3.8.4
    (hsym : P.map Neg.neg = P)
    -- USER-INPUT: strictly increasing continuous shift score; MMY §3.8.4
    (hg : StrictMono (shiftScore ψ P))
    -- USER-INPUT: contamination level, nondegenerate; MMY §3.8.4
    (hε0 : 0 < ε) (hε : ε < 1 / 2)
    -- USER-INPUT: b_ε solves the maximum-bias equation; MMY (3.66)
    (hbε : shiftScore ψ P bε = k * ε / (1 - ε)) :
    ∀ η : ℝ, 0 < η → ∃ (x₀ θ : ℝ),
      IsMLocationRoot ψ (contaminate P (Measure.dirac x₀) ε) θ ∧ bε - η < θ := by
  sorry

/-- **The median's shift score, general form**: for atomless `P`,
`g(b) = ∫ sign(x + b) dP = 1 − 2 P(−∞, −b]` — no symmetry needed at this stage. -/
theorem shiftScore_sign {P : Measure ℝ} [IsProbabilityMeasure P] {b : ℝ}
    -- USER-INPUT: atomless center (the sign integrand's null discontinuity); MMY
    -- §3.8.4 (implicit: F₀ has a density)
    (hatom : ∀ t : ℝ, P {t} = 0) :
    shiftScore Real.sign P b = 1 - 2 * P.real (Set.Iic (-b)) := by
  sorry

/-- **The median's shift score is the centered CDF** (`MMY §3.8.4`, "for the median,
`ψ(x) = sgn(x)` and `k = 1`, and a simple calculation shows (recalling the symmetry of
`F₀`) that `g(b) = 2F₀(b) − 1`"): symmetry turns `1 − 2F₀(−b)` into `2F₀(b) − 1`. -/
theorem shiftScore_sign_of_symm {P : Measure ℝ} [IsProbabilityMeasure P] {b : ℝ}
    (hatom : ∀ t : ℝ, P {t} = 0)
    -- USER-INPUT: symmetric center; MMY §3.8.4 ("recalling the symmetry of F₀")
    (hsym : P.map Neg.neg = P) :
    shiftScore Real.sign P b = 2 * P.real (Set.Iic b) - 1 := by
  sorry

/-- **The median's maximum-bias equation is the quantile equation** (`MMY (3.68)`):
for an atomless symmetric center, `b` solves the `k = 1` maximum-bias equation
`g(b) = ε/(1−ε)` iff `F₀(b) = 1/(2(1−ε))`. -/
theorem sign_maxBias_iff {P : Measure ℝ} [IsProbabilityMeasure P] {ε b : ℝ}
    (hatom : ∀ t : ℝ, P {t} = 0)
    -- USER-INPUT: symmetric center; MMY §3.8.4
    (hsym : P.map Neg.neg = P) (hε : ε < 1) :
    shiftScore Real.sign P b = 1 * ε / (1 - ε) ↔
      P.real (Set.Iic b) = 1 / (2 * (1 - ε)) := by
  sorry

end StatLean.RobustStatistics
