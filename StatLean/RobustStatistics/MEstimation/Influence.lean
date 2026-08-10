import StatLean.RobustStatistics.Core.InfluenceFunction
import StatLean.RobustStatistics.MEstimation.MLocationFunctional
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# The influence function of location M-functionals — the flagship formula

For a location M-functional defined by `E_P ψ(x - T(P)) = 0`, the influence function at
contamination point `x₀` is (`MMY §3.1`, eq. (3.7); proof in §3.8.1)

$$\operatorname{IF}(x_0; T, P) = \frac{\psi(x_0 - \theta_0)}{A}, \qquad
  A = \int \psi'(x - \theta_0)\,dP(x),$$

so a *bounded score forces a bounded influence function* — the theorem chain
`ψ bounded ⟹ IF bounded` that separates Huber estimation from the mean.

The book's derivation (`MMY §3.8.1`, eq. (3.58)–(3.59)) differentiates the contaminated
estimating identity along the mixture path and notes "it is taken for granted that
`∂θ_ε/∂ε` exists and `θ_ε → θ_0`"; the rigorous proof is delegated to Huber–Ronchetti.
The Lean statements mirror that structure honestly: the *root path* `θ` and its one-sided
differentiability at `0` are explicit inputs, and the theorem computes the derivative's
unique possible value. The Lipschitz version `mLocationRoot_influence_of_lipschitz`
requires `ψ` differentiable only `P`-almost everywhere along the shifted data, which is
exactly what the kinked Huber score satisfies when `P` has no atoms at `θ₀ ± c`.

* `mLocationRoot_influence_of_lipschitz` — the IF formula for Lipschitz scores with a.e.
  derivatives (engine).
* `mLocationRoot_influence` — the smooth-score corollary (`ψ'` everywhere).
* `mLocationFunctional_hasInfluenceAt` — packaged as `HasInfluenceAt` for a functional.
* `mLocation_influence_bounded` — `|ψ| ≤ c ⟹ |IF| ≤ c/|A|` (`MMY` (3.30)–(3.31) context).
* `huberLocation_influence`, `huberLocation_influence_bounded` — the Huber instance:
  `IF = ψ_c(x₀ - θ₀)/P(|x - θ₀| < c)`, bounded by `c / P(|x - θ₀| < c)`.

**Reference.** R. A. Maronna, R. D. Martin, V. J. Yohai and M. Salibián-Barrera, *Robust
Statistics: Theory and Methods (with R)*, 2nd ed., Wiley, 2019. (`MMY`.) §3.1 (eq. (3.7)),
§3.3 (eq. (3.29)–(3.31)), §3.8.1 (eq. (3.58)–(3.59)).
-/

open MeasureTheory Filter Topology

namespace StatLean.RobustStatistics

/-- **The influence-function formula for M-functionals, Lipschitz engine**
(`MMY §3.8.1`): if `θ t` solves the `δ_{x₀}`-contaminated M-equation for small `t ≥ 0`
and is right-differentiable at `0` with derivative `d`, then
`d = ψ(x₀ - θ₀) / A` with `A = ∫ ψd dP` the mean a.e. derivative of the score along the
shifted data. -/
theorem mLocationRoot_influence_of_lipschitz {P : Measure ℝ} [IsProbabilityMeasure P]
    {ψ ψd : ℝ → ℝ} {L : ℝ≥0} {θ : ℝ → ℝ} {θ₀ x₀ d A : ℝ}
    -- USER-INPUT: Lipschitz score; MMY §3.8.1 (regularity for the interchange)
    (hψlip : LipschitzWith L ψ)
    -- USER-INPUT: ψ differentiable P-a.e. along the θ₀-shifted data, with derivative ψd;
    -- MMY §3.8.1 ("assume ψ' exists"), weakened to the a.e. form the Huber score satisfies
    (hae : ∀ᵐ x ∂P, HasDerivAt ψ (ψd x) (x - θ₀))
    -- LEAN-ONLY: measurability of the chosen a.e. derivative, for the parametric-integral
    -- theorem; no scope change (any version works)
    (hψd_meas : AEStronglyMeasurable ψd P)
    -- USER-INPUT: θ t solves the contaminated M-equation for small t ≥ 0; MMY (3.58)
    (hroot : ∀ᶠ t in 𝓝[Set.Ici (0 : ℝ)] 0,
      IsMLocationRoot ψ (contaminate P (Measure.dirac x₀) t) (θ t))
    (hθ0 : θ 0 = θ₀)
    -- USER-INPUT: the contaminated root path is right-differentiable at 0; MMY §3.8.1
    -- ("it is taken for granted that ∂θ_ε/∂ε exists")
    (hθd : HasDerivWithinAt θ d (Set.Ici 0) 0)
    (hA : A = ∫ x, ψd x ∂P)
    -- USER-INPUT: nondegenerate denominator; MMY Thm 10.7 (B ≠ 0)
    (hA0 : A ≠ 0) :
    d = ψ (x₀ - θ₀) / A := by
  sorry

/-- **The influence-function formula for M-functionals, smooth scores**
(`MMY §3.1`, eq. (3.7)): the specialization of the Lipschitz engine to scores with an
everywhere derivative `ψ'` bounded by a constant. -/
theorem mLocationRoot_influence {P : Measure ℝ} [IsProbabilityMeasure P]
    {ψ ψ' : ℝ → ℝ} {C : ℝ} {θ : ℝ → ℝ} {θ₀ x₀ d A : ℝ}
    -- USER-INPUT: differentiable score with derivative ψ'; MMY §3.8.1
    (hψ : ∀ u, HasDerivAt ψ (ψ' u) u)
    -- USER-INPUT: bounded score derivative (dominates the interchange); MMY (10.8)
    (hψ'b : ∀ u, |ψ' u| ≤ C)
    -- LEAN-ONLY: measurability of ψ'; automatic for continuous derivatives
    (hψ'_meas : Measurable ψ')
    -- USER-INPUT: θ t solves the contaminated M-equation for small t ≥ 0; MMY (3.58)
    (hroot : ∀ᶠ t in 𝓝[Set.Ici (0 : ℝ)] 0,
      IsMLocationRoot ψ (contaminate P (Measure.dirac x₀) t) (θ t))
    (hθ0 : θ 0 = θ₀)
    -- USER-INPUT: the contaminated root path is right-differentiable at 0; MMY §3.8.1
    (hθd : HasDerivWithinAt θ d (Set.Ici 0) 0)
    (hA : A = ∫ x, ψ' (x - θ₀) ∂P)
    -- USER-INPUT: nondegenerate denominator; MMY Thm 10.7 (B ≠ 0)
    (hA0 : A ≠ 0) :
    d = ψ (x₀ - θ₀) / A := by
  sorry

/-- **The influence function of an M-location functional** (`MMY` eq. (3.7)), packaged
for a functional `T : Measure ℝ → ℝ` whose values solve the contaminated M-equation along
the point-mass path: `HasInfluenceAt T P x₀ (ψ(x₀ - T P)/A)`. -/
theorem mLocationFunctional_hasInfluenceAt {P : Measure ℝ} [IsProbabilityMeasure P]
    {T : Measure ℝ → ℝ} {ψ ψd : ℝ → ℝ} {L : ℝ≥0} {x₀ A : ℝ}
    (hψlip : LipschitzWith L ψ)
    (hae : ∀ᵐ x ∂P, HasDerivAt ψ (ψd x) (x - T P))
    (hψd_meas : AEStronglyMeasurable ψd P)
    -- USER-INPUT: T tracks roots of the contaminated M-equation near 0; MMY §3.7 (3.51)
    (hroot : ∀ᶠ t in 𝓝[Set.Ici (0 : ℝ)] 0,
      IsMLocationRoot ψ (contaminate P (Measure.dirac x₀) t)
        (T (contaminate P (Measure.dirac x₀) t)))
    -- USER-INPUT: the contamination curve of T is right-differentiable at 0; MMY §3.8.1
    (hTd : ∃ d, HasDerivWithinAt (fun t : ℝ => T (contaminate P (Measure.dirac x₀) t)) d
      (Set.Ici 0) 0)
    (hA : A = ∫ x, ψd x ∂P) (hA0 : A ≠ 0) :
    HasInfluenceAt T P x₀ (ψ (x₀ - T P) / A) := by
  sorry

/-- **Bounded score ⟹ bounded influence** (`MMY §3.3`, eq. (3.30)–(3.31) context): if
`|ψ| ≤ c` then any influence value produced by the M-functional formula is bounded by
`c/|A|`, uniformly in the contamination point. -/
theorem mLocation_influence_bounded {ψ : ℝ → ℝ} {c A u : ℝ}
    -- USER-INPUT: bounded score; MMY §2.3.2 / Def 2.2
    (hψb : ∀ v, |ψ v| ≤ c) (hA0 : A ≠ 0) :
    |ψ u / A| ≤ c / |A| := by
  sorry

/-! ### The Huber instance (`MMY §2.3.2` + §3.1) -/

/-- **The influence function of the Huber location functional** (`MMY` eq. (3.7) with eq.
(2.29)): `IF(x₀) = ψ_c(x₀ - θ₀) / P(|x - θ₀| < c)`. The denominator is the mass of the
central region, the a.e. derivative of the clipped score. -/
theorem huberLocation_influence {P : Measure ℝ} [IsProbabilityMeasure P] {c : ℝ}
    (hc : 0 < c) {θ : ℝ → ℝ} {θ₀ x₀ d : ℝ}
    -- USER-INPUT: no atoms at the clipping knots (a.e. differentiability of ψ_c along the
    -- shifted data); MMY §10.3 (F continuous at the relevant points)
    (h_atom₊ : P {θ₀ + c} = 0) (h_atom₋ : P {θ₀ - c} = 0)
    -- USER-INPUT: θ t solves the contaminated Huber equation for small t ≥ 0; MMY (3.58)
    (hroot : ∀ᶠ t in 𝓝[Set.Ici (0 : ℝ)] 0,
      IsMLocationRoot (huberPsi c) (contaminate P (Measure.dirac x₀) t) (θ t))
    (hθ0 : θ 0 = θ₀)
    -- USER-INPUT: right-differentiable root path; MMY §3.8.1
    (hθd : HasDerivWithinAt θ d (Set.Ici 0) 0)
    -- USER-INPUT: the central region has positive mass (B ≠ 0); MMY Thm 10.7
    (hmass : 0 < P.real {x | |x - θ₀| < c}) :
    d = huberPsi c (x₀ - θ₀) / P.real {x | |x - θ₀| < c} := by
  sorry

/-- **The Huber location functional has bounded influence** (`MMY §3.3`): the influence
value at any contamination point is bounded by `c / P(|x - θ₀| < c)`. Contrast with the
unbounded influence of the mean (`LocationScale/Mean.lean`). -/
theorem huberLocation_influence_bounded {P : Measure ℝ} [IsProbabilityMeasure P] {c : ℝ}
    (hc : 0 < c) {θ : ℝ → ℝ} {θ₀ x₀ d : ℝ}
    (h_atom₊ : P {θ₀ + c} = 0) (h_atom₋ : P {θ₀ - c} = 0)
    (hroot : ∀ᶠ t in 𝓝[Set.Ici (0 : ℝ)] 0,
      IsMLocationRoot (huberPsi c) (contaminate P (Measure.dirac x₀) t) (θ t))
    (hθ0 : θ 0 = θ₀)
    (hθd : HasDerivWithinAt θ d (Set.Ici 0) 0)
    (hmass : 0 < P.real {x | |x - θ₀| < c}) :
    |d| ≤ c / P.real {x | |x - θ₀| < c} := by
  sorry

end StatLean.RobustStatistics
