import StatLean.StatisticalModels.Identifiability.Transfer
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# Worked instance: a location family under right censoring

The second Core regression test, seeding the Survival slice: a location family on `ℝ` (a
nonparametric-in-the-carrier model — the base law `μ₀` is arbitrary), the **right-censoring
observation kernel** carrying a full event time `t` to the censored readout
`(t ∧ C, 1{t ≤ C})` with `C ∼ ν` independent, and the destroy-direction identifiability
transfer instantiated: identification from censored data implies identification from complete
data.

**Reference.** Location families: TPE2 §1.1, §3.1 (verify §). The random-censorship readout
`(T ∧ C, 1{T ≤ C})`: E. L. Kaplan and P. Meier, "Nonparametric estimation from incomplete
observations," *J. Amer. Statist. Assoc.* **53** (1958), 457–481, §2 (verify §).

**Proof formalization notes.** The censoring kernel is built compositionally —
`(deterministic id) ×ₖ (const ν)` mapped through `(t, c) ↦ (t ∧ c, decide (t ≤ c))` — so its
measurability is inherited, never proved by hand; its pointwise form and Markov property are
the two lemmas. Tie convention: `Δ = decide (T ≤ C)` (ties count as events) — Book-vs-Lean
note: the classical treatments assume `P(T = C) = 0`, where the convention is immaterial.
The Survival slice reuses this kernel; here it only exercises `observe` and the transfer
theorems.

**Bibliographic comments.** Random censorship as an explicit observation mechanism goes back
to Kaplan–Meier 1958 and J. Gilbert's 1962 thesis; the kernel packaging is ours.
-/

open MeasureTheory ProbabilityTheory

namespace StatLean.StatisticalModels

open StatLean.PointEstimation

/-! ## The location family -/

/-- The location family of a base law `μ₀`: parameter `θ` shifts the law by `θ`
(TPE2 §3.1 (verify §)). Arbitrary base law — the model structure, not a parametric family. -/
noncomputable def locationFam (μ₀ : Measure ℝ) : ℝ → Measure ℝ :=
  fun θ => μ₀.map (fun x => θ + x)

instance (μ₀ : Measure ℝ) [IsProbabilityMeasure μ₀] (θ : ℝ) :
    IsProbabilityMeasure (locationFam μ₀ θ) := by
  sorry

/-- Shifting the data shifts the parameter: the location model is equivariant under
translation (via `pushforward_pushforward`). -/
theorem pushforward_locationFam_shift (μ₀ : Measure ℝ) (c : ℝ) :
    pushforward (locationFam μ₀) (fun x => c + x) = fun θ => locationFam μ₀ (c + θ) := by
  sorry

/-! ## The right-censoring kernel -/

/-- **Right-censoring observation kernel** with censoring law `ν`: a full event time `t` is
observed as `(t ∧ C, 1{t ≤ C})`, `C ∼ ν` independent of the data (Kaplan–Meier 1958 §2).
Built compositionally so measurability is inherited. -/
noncomputable def rightCensorKernel (ν : Measure ℝ) : Kernel ℝ (ℝ × Bool) :=
  ((Kernel.deterministic id measurable_id) ×ₖ Kernel.const ℝ ν).map
    (fun p => (min p.1 p.2, decide (p.1 ≤ p.2)))

/-- Pointwise form of the censoring kernel: the law of `(t ∧ C, 1{t ≤ C})` under `C ∼ ν`. -/
theorem rightCensorKernel_apply (ν : Measure ℝ) [IsProbabilityMeasure ν] (t : ℝ) :
    rightCensorKernel ν t = ν.map (fun c => (min t c, decide (t ≤ c))) := by
  sorry

instance (ν : Measure ℝ) [IsProbabilityMeasure ν] : IsMarkovKernel (rightCensorKernel ν) := by
  sorry

/-- Identification from right-censored data implies identification from complete data — the
destroy-direction transfer theorem, instantiated. -/
theorem identifiable_of_rightCensored (μ₀ : Measure ℝ) (ν : Measure ℝ)
    [IsProbabilityMeasure ν]
    (h : Identifiable (observe (locationFam μ₀) (rightCensorKernel ν))) :
    Identifiable (locationFam μ₀) :=
  identifiable_of_observe _ h

end StatLean.StatisticalModels
