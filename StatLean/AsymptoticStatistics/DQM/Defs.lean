import StatLean.AsymptoticStatistics.ParametricFamily.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Asymptotics.Defs

/-!
Asymptotic Statistics — Differentiability in Quadratic Mean (DQM).

The central regularity condition of van der Vaart, §7.2 (Eq. 7.1). Consequences
and discharges of DQM auxiliary hypotheses live in `DQM/Properties.lean`.
-/

open MeasureTheory Asymptotics Filter Topology
open scoped RealInnerProductSpace

namespace AsymptoticStatistics

variable {𝓧 : Type*} [MeasurableSpace 𝓧]
variable {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ]
variable {μ : Measure 𝓧}

/-- Differentiability in quadratic mean (DQM).

The model `M` is **DQM at `θ`** with score `ℓ : 𝓧 → Θ` w.r.t. the dominating measure `μ`
if the L²(μ) Hellinger residual is `o(‖h‖²)` as `h → 0`:
`∫ (√p_{θ+h} − √p_θ − ½⟨h, ℓ(x)⟩√p_θ)² dμ(x) = o(‖h‖²)`.

This is the central regularity condition of LAN (Local Asymptotic Normality);
see van der Vaart §7.2 (Eq. 7.1).

**Note on the conjunction.** In van der Vaart's definition the integral is the
Lebesgue integral of a non-negative function, where finiteness of the integral
is *the same as* `MemLp 2 μ`-membership of the residual.  When formalising with
Lean's Bochner integral `∫`, that equivalence breaks: a non-integrable
non-negative function has Bochner integral `0` by convention, so the
`o(‖h‖²)` rate condition is *trivially* satisfied for pathological models in
which the residual is never in `L²(μ)`.  We therefore record the implicit
"residual is eventually in `L²(μ)`" content of vdV's definition as a separate
conjunct (`mem`), so that our formal definition is *equivalent* to vdV's
informal one — no stronger, no weaker. -/
structure DifferentiableQuadraticMean
    (M : ParametricFamily 𝓧 Θ) (μ : Measure 𝓧) (θ : Θ)
    (ℓ : 𝓧 → Θ) : Prop where
  /-- The Hellinger residual is in `L²(μ)` for every `h` in some neighbourhood
  of `0`. (Implicit in vdV via the Lebesgue interpretation of the integral.) -/
  mem : ∀ᶠ h in 𝓝 (0 : Θ),
    MemLp (fun x => M.sqrtDensity (θ + h) x - M.sqrtDensity θ x
                    - (1/2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ x) 2 μ
  /-- The L²(μ) norm of the Hellinger residual is `o(‖h‖²)` as `h → 0`. -/
  isLittleO :
    (fun h : Θ =>
      ∫ x, (M.sqrtDensity (θ + h) x
            - M.sqrtDensity θ x
            - (1/2 : ℝ) * ⟪h, ℓ x⟫ * M.sqrtDensity θ x) ^ 2 ∂μ)
    =o[𝓝 (0 : Θ)] (fun h : Θ => ‖h‖ ^ 2)

end AsymptoticStatistics
