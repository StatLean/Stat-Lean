import StatLean.RobustStatistics.MEstimation.MLocationFunctional
import StatLean.RobustStatistics.MEstimation.AsymptoticBreakdown
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Scale M-functionals — the log-scale reduction and the breakdown point `min(δ, 1−δ)`

A scale M-estimate solves `(1/n) ∑ ρ(xᵢ/σ̂) = δ` (`MMY §2.5`, eq. (2.49)); its population
version solves `∫ ρ(x/σ) dP = δ`. Robustness of a scale estimator means staying away
from *both* boundary pieces of `Θ = (0, ∞)`: contamination can cause **explosion**
(`σ → ∞`, outliers) or **implosion** (`σ → 0`, inliers). The organizing device — `MMY
§3.2.2` — is that a scale M-estimator is a *location* M-estimator "in the log scale":
with `y = log|x|`, `μ = log σ`, `ψ(t) = ρ(eᵗ) − δ`, the scale equation becomes the
location equation, and the Round-1 location breakdown pair (`MMY (3.21)`/(3.22)) with
`k₁ = δ`, `k₂ = 1 − δ` yields the scale breakdown point

  `ε* = min(δ, 1 − δ)`   (`MMY (3.23)`),

with `δ` the explosion BP and `1 − δ` the implosion BP.

* `IsMScaleRoot` — the population scale M-equation (`MMY (2.49)`, population form).
* `logAbs`, `scaleScorePsi` — the log-scale transport data.
* `isMScaleRoot_iff_logScale` — the reduction (`MMY §3.2.2`, the display).
* `mScaleRoot_bounded_of_contamination` — no explosion, no implosion below
  `min(δ, 1−δ)` (`MMY (3.23)`, stability direction).
* `mScaleRoot_explodes` / `mScaleRoot_implodes` — sharpness beyond the BP.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera,
*Robust Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.)
§2.5 (eq. (2.49)), §2.6 (dispersion conditions (2.58)), §3.2.2 (the log-scale
reduction; eq. (3.23)). The population MAD (`MMY (2.62)`) is the scale M-functional of
the *discontinuous* loss `ρ = 1{|x| ≥ 1}` at `δ = 1/2`; it is outside the continuous-`ρ`
hypotheses used here and is treated only through its finite-sample breakdown
(`Scale/DispersionBreakdown.lean`).
-/

open MeasureTheory Filter Topology

namespace StatLean.RobustStatistics

/-- **The population scale M-root** (`MMY §2.5`, eq. (2.49), population form): `σ > 0`
solves `∫ ρ(x/σ) dP = δ`. The Bochner-junk caveat of `IsMLocationRoot` applies:
consumers carry integrability of `ρ(·/σ)` explicitly. -/
def IsMScaleRoot (ρ : ℝ → ℝ) (δ : ℝ) (P : Measure ℝ) (σ : ℝ) : Prop :=
  0 < σ ∧ ∫ x, ρ (x / σ) ∂P = δ

/-- The log-modulus data map `x ↦ log |x|` of the `MMY §3.2.2` reduction. Junk note:
`Real.log 0 = 0`, so the map sends the atom at `0` to `0`; all statements below carry
`P {0} = 0` and are unaffected. -/
noncomputable def logAbs (x : ℝ) : ℝ := Real.log |x|

/-- The transported score `ψ(t) = ρ(eᵗ) − δ` of the `MMY §3.2.2` reduction. -/
noncomputable def scaleScorePsi (ρ : ℝ → ℝ) (δ : ℝ) (t : ℝ) : ℝ := ρ (Real.exp t) - δ

/-- **The log-scale reduction** (`MMY §3.2.2`, the display `ρ(x/σ) − δ = ψ(y − μ)`):
for an even loss, `σ` is a scale M-root of `P` iff `log σ` is a *location* M-root of the
transported score under the pushforward `P.map logAbs`. This is the engine that turns
Round-1 location theorems into scale theorems. -/
theorem isMScaleRoot_iff_logScale {ρ : ℝ → ℝ} {δ : ℝ} {P : Measure ℝ}
    [IsProbabilityMeasure P] {σ : ℝ} (hσ : 0 < σ)
    -- USER-INPUT: even loss; MMY §3.2.2 ("since ρ is even")
    (hρ_even : ∀ x, ρ (-x) = ρ x)
    -- LEAN-ONLY: measurability of ρ, to transport the integral; regularity
    (hρ_meas : Measurable ρ)
    -- USER-INPUT: no atom at 0 (so |x| > 0 a.e. and the log is honest); MMY §3.2.2
    -- (implicit in y = log|x|)
    (hP0 : P {0} = 0)
    -- USER-INPUT: the loss is integrable at scale σ; MMY (2.49) context
    (hint : Integrable (fun x => ρ (x / σ)) P) :
    IsMScaleRoot ρ δ P σ ↔
      IsMLocationRoot (scaleScorePsi ρ δ) (P.map logAbs) (Real.log σ) := by
  sorry

/-- The transported score of a bounded even loss is monotone with limits `−δ` at `−∞`
and `1 − δ` at `+∞` (`MMY §3.2.2` with `ρ(0) = 0`, `ρ(∞) = 1`): the location breakdown
data `k₁ = δ`, `k₂ = 1 − δ` of `MMY (3.23)`. -/
theorem scaleScorePsi_monotone_limits {ρ : ℝ → ℝ} {δ : ℝ}
    -- USER-INPUT: the loss is a bounded ρ-function: even, nondecreasing on [0,∞),
    -- ρ(0) = 0, ρ(∞) = 1; MMY §2.5 / Definition 2.1
    (hρ_mono : MonotoneOn ρ (Set.Ici 0)) (hρ0 : ρ 0 = 0)
    (hρ_lim : Tendsto ρ atTop (𝓝 1)) :
    Monotone (scaleScorePsi ρ δ) ∧
      Tendsto (scaleScorePsi ρ δ) atBot (𝓝 (-δ)) ∧
      Tendsto (scaleScorePsi ρ δ) atTop (𝓝 (1 - δ)) := by
  sorry

/-- **Scale M-roots resist contamination below `min(δ, 1−δ)`** (`MMY (3.23)`, stability
direction): for a bounded even loss and `ε < min(δ, 1−δ)`, all scale M-roots of all
`ε`-contaminations of `P` lie in a fixed interval `[σ_lo, σ_hi] ⊂ (0, ∞)` — neither
explosion nor implosion. Proved through the log-scale reduction and Round-1's
`mLocationRoot_bounded_of_contamination` (`MMY (3.21)`) with `k₁ = δ`, `k₂ = 1 − δ`,
noting `min(δ, 1−δ)/(δ + (1−δ)) = min(δ, 1−δ)`. -/
theorem mScaleRoot_bounded_of_contamination {ρ : ℝ → ℝ} {δ ε : ℝ} {P : Measure ℝ}
    [IsProbabilityMeasure P]
    -- USER-INPUT: bounded even ρ-function; MMY §2.5 / Definition 2.1
    (hρ_even : ∀ x, ρ (-x) = ρ x) (hρ_mono : MonotoneOn ρ (Set.Ici 0))
    (hρ0 : ρ 0 = 0) (hρ_lim : Tendsto ρ atTop (𝓝 1))
    -- LEAN-ONLY: measurability of ρ; regularity
    (hρ_meas : Measurable ρ)
    -- USER-INPUT: target level strictly inside (0,1); MMY §2.5 (0 < δ < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    -- USER-INPUT: no atom at 0; MMY §3.2.2 (implicit in the log scale)
    (hP0 : P {0} = 0)
    -- USER-INPUT: contamination level below the scale breakdown point; MMY (3.23)
    (hε0 : 0 ≤ ε) (hε : ε < min δ (1 - δ)) :
    ∃ σlo σhi : ℝ, 0 < σlo ∧
      ∀ (Q : Measure ℝ), IsProbabilityMeasure Q → Q {0} = 0 → ∀ σ : ℝ,
        IsMScaleRoot ρ δ (contaminate P Q ε) σ → σ ∈ Set.Icc σlo σhi := by
  sorry

/-- **Explosion beyond `δ`** (`MMY (3.23)` sharpness, explosion side; `MMY §3.2.2`:
"δ and 1 − δ are, respectively, the BPs for explosion and for implosion"): for
contamination level `ε > δ`, point-mass contamination arbitrarily far out produces
scale M-roots beyond any bound — through the log-scale reduction this is Round-1's
`mLocationRoot_contamination_unbounded` (`MMY (3.22)`) at `k₁ = δ`, `k₂ = 1 − δ`. -/
theorem mScaleRoot_explodes {ρ : ℝ → ℝ} {δ ε : ℝ} {P : Measure ℝ}
    [IsProbabilityMeasure P]
    -- USER-INPUT: bounded even continuous ρ-function; MMY §2.5 + Thm 10.1 regularity
    (hρ_even : ∀ x, ρ (-x) = ρ x) (hρ_mono : MonotoneOn ρ (Set.Ici 0))
    (hρ0 : ρ 0 = 0) (hρ_lim : Tendsto ρ atTop (𝓝 1)) (hρc : Continuous ρ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hP0 : P {0} = 0)
    -- USER-INPUT: contamination level beyond the explosion BP; MMY (3.23)
    (hε : δ < ε) (hε1 : ε < 1) :
    ∀ B : ℝ, ∃ (x₀ σ : ℝ), B < σ ∧
      IsMScaleRoot ρ δ (contaminate P (Measure.dirac x₀) ε) σ := by
  sorry

/-- **Implosion beyond `1 − δ`** (`MMY (3.23)` sharpness, implosion side): for
contamination level `ε > 1 − δ`, point-mass contamination by *inliers* at some small
`s > 0` produces scale M-roots below any positive bound.

Why `s > 0` and not `s = 0`: with the whole contaminating mass exactly at `0` the
contaminated equation reads `(1−ε) ∫ρ(x/σ) dP = δ`, whose left side is `< δ` for every
`σ > 0` when `ε > 1 − δ` — the root set is *empty*, which is breakdown by vacuity, not
by implosion. Placing the inliers at `s > 0` restores a root (IVT) and drives it below
`b` as `s → 0`. -/
theorem mScaleRoot_implodes {ρ : ℝ → ℝ} {δ ε : ℝ} {P : Measure ℝ}
    [IsProbabilityMeasure P]
    -- USER-INPUT: bounded even continuous ρ-function; MMY §2.5 + Thm 10.1 regularity
    (hρ_even : ∀ x, ρ (-x) = ρ x) (hρ_mono : MonotoneOn ρ (Set.Ici 0))
    (hρ0 : ρ 0 = 0) (hρ_lim : Tendsto ρ atTop (𝓝 1)) (hρc : Continuous ρ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hP0 : P {0} = 0)
    -- USER-INPUT: contamination level beyond the implosion BP; MMY (3.23)
    (hε : 1 - δ < ε) (hε1 : ε < 1) :
    ∀ b : ℝ, 0 < b → ∃ (s σ : ℝ), 0 < s ∧ 0 < σ ∧ σ < b ∧
      IsMScaleRoot ρ δ (contaminate P (Measure.dirac s) ε) σ := by
  sorry

end StatLean.RobustStatistics
