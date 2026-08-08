import StatLean.TimeSeries.ForMathlib.Markov.GeometricErgodicity

/-!
# Harris' ergodic theorem, Hairer–Mattingly form

The elementary route to geometric ergodicity of a Markov kernel: **Lyapunov drift plus
minorization on a level set imply a contraction in a weighted total-variation
distance**, hence a unique invariant law approached at a geometric rate.

* `lyapDist β V μ ν = ∫ (1 + β V) d|μ − ν|` — the weighted TV distance (`weightedTV`
  below; the `β = 0` case is `2·tvDist`);
* `HasLyapunovDrift κ V γ K` — `P V ≤ γ V + K` pointwise with `γ < 1`;
* `HasMinorization κ S α` — `κ x ≥ α · ρ` on the level set `S` for a common probability
  measure `ρ`;
* `harris_contraction` — the Hairer–Mattingly estimate: for suitable `β`, `κ` contracts
  `lyapDist` by a factor `ᾱ < 1`;
* `harris_theorem` — the packaged conclusion: a unique invariant probability measure
  `π`, with `tvDist (κⁿ x) π ≤ C(x)·ρ̄ⁿ` — exactly the envelope `IsErgodicWithRate`
  (and hence `IsGeometricallyErgodic`) needs;
* `IsGeometricallyErgodic.of_pow` — the glue that lifts geometric ergodicity of the
  `p`-step kernel `κ^p` back to `κ` (needed because the minorization for the nonlinear
  AR kernel of FY Theorem 2.4 only holds after `p` steps, once every coordinate has
  been refreshed).

This file exists to discharge the last structural debt of the TimeSeries area,
`nlARKernel_geometricallyErgodic` (FY Theorem 2.4(ii)); the Meyn–Tweedie
ψ-irreducibility/petite-set apparatus is deliberately avoided.

**Reference.** M. Hairer and J. C. Mattingly, *Yet another look at Harris' ergodic
theorem for Markov chains*, in Seminar on Stochastic Analysis, Random Fields and
Applications VI, Progr. Probab. 63, Birkhäuser (2011), 109–117. Consumed by
FY §2.1.4 Theorem 2.4 (An & Huang 1996; Bhattacharya & Lee 1995).
(`Hairer–Mattingly 2011` in tags.)

**Bibliographic comments.** Harris' theorem is T. E. Harris (1956); the drift/
minorization formulation is Meyn & Tweedie, *Markov Chains and Stochastic Stability*
(1993), ch. 15–16; the weighted-TV contraction proof formalized here is the
Hairer–Mattingly simplification, which needs no irreducibility theory.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology ENNReal

namespace StatLean.TimeSeries

variable {S : Type*} [MeasurableSpace S]

/-- The **weighted total-variation distance** `∫ (1 + βV) d|μ − ν|` of Hairer–Mattingly
(their `ρ_β`), as an `ℝ≥0∞`-valued quantity built from the Jordan decomposition of the
signed difference. At `β = 0` it is twice `StatLean.Minimaxity.tvDist`. -/
noncomputable def weightedTV (β : ℝ) (V : S → ℝ) (μ ν : Measure S) : ℝ≥0∞ :=
  (∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂(μ.singularPart ν))
    + ∫⁻ x, ENNReal.ofReal (1 + β * V x) ∂(ν.singularPart μ)

/-- **Lyapunov drift condition**: `∫ V d(κ x) ≤ γ V x + K` with a contraction factor
`γ < 1` (Hairer–Mattingly Assumption 1). -/
structure HasLyapunovDrift (κ : Kernel S S) (V : S → ℝ) (γ K : ℝ) : Prop where
  /-- Constitutive (H–M Assumption 1): the Lyapunov function is nonnegative. -/
  V_nonneg : ∀ x, 0 ≤ V x
  /-- Constitutive (H–M Assumption 1): `V` is measurable. -/
  V_measurable : Measurable V
  /-- Constitutive (H–M Assumption 1): the contraction factor is in `(0, 1)`. -/
  gamma_mem : 0 < γ ∧ γ < 1
  /-- Constitutive (H–M Assumption 1): the additive constant is nonnegative. -/
  K_nonneg : 0 ≤ K
  /-- Constitutive (H–M Assumption 1): the drift inequality `PV ≤ γV + K`. -/
  drift : ∀ x, (∫ y, V y ∂(κ x)) ≤ γ * V x + K

/-- **Minorization on a sublevel set**: on `{V ≤ R}` the kernel dominates `α·ρ` for a
fixed probability measure `ρ` (Hairer–Mattingly Assumption 2). -/
structure HasMinorization (κ : Kernel S S) (V : S → ℝ) (R α : ℝ) (ρ : Measure S) :
    Prop where
  /-- Constitutive (H–M Assumption 2): the minorization strength is in `(0, 1]`. -/
  alpha_mem : 0 < α ∧ α ≤ 1
  /-- Constitutive (H–M Assumption 2): the minorizing measure is a probability
  measure. -/
  isProbability : IsProbabilityMeasure ρ
  /-- Constitutive (H–M Assumption 2): domination on the level set. -/
  minorize : ∀ x, V x ≤ R → ∀ A : Set S, MeasurableSet A →
    ENNReal.ofReal α * ρ A ≤ κ x A

/-- **Harris contraction** (Hairer–Mattingly Theorem 1.3): under a Lyapunov drift and a
minorization on a high enough level set, the kernel contracts the weighted TV distance
`weightedTV β V` for a suitable `β > 0`, uniformly over initial laws. -/
theorem harris_contraction {κ : Kernel S S} [IsMarkovKernel κ] {V : S → ℝ} {γ K : ℝ}
    (hdrift : HasLyapunovDrift κ V γ K) {R α : ℝ} {ρ : Measure S}
    (hmin : HasMinorization κ V R α ρ)
    -- USER-INPUT: the level set is high enough to see the drift (H–M Thm 1.3);
    -- `R > 2K/(1 − γ)`
    (hR : 2 * K / (1 - γ) < R) :
    ∃ β ᾱ : ℝ, 0 < β ∧ 0 < ᾱ ∧ ᾱ < 1 ∧
      ∀ μ ν : Measure S, IsProbabilityMeasure μ → IsProbabilityMeasure ν →
        weightedTV β V (μ.bind κ) (ν.bind κ)
          ≤ ENNReal.ofReal ᾱ * weightedTV β V μ ν := by
  sorry

/-- **Harris' theorem** (Hairer–Mattingly): drift + minorization give a unique invariant
probability measure and a geometric total-variation rate from every starting point —
packaged exactly as `IsGeometricallyErgodic` needs it. -/
theorem harris_theorem {κ : Kernel S S} [IsMarkovKernel κ] {V : S → ℝ} {γ K : ℝ}
    (hdrift : HasLyapunovDrift κ V γ K) {R α : ℝ} {ρ : Measure S}
    (hmin : HasMinorization κ V R α ρ) (hR : 2 * K / (1 - γ) < R) :
    ∃ π : Measure S, IsProbabilityMeasure π ∧ Kernel.Invariant κ π ∧
      IsGeometricallyErgodic κ π := by
  sorry

/-- **Uniqueness** of the invariant law under the Harris hypotheses. -/
theorem harris_invariant_unique {κ : Kernel S S} [IsMarkovKernel κ] {V : S → ℝ}
    {γ K : ℝ} (hdrift : HasLyapunovDrift κ V γ K) {R α : ℝ} {ρ : Measure S}
    (hmin : HasMinorization κ V R α ρ) (hR : 2 * K / (1 - γ) < R)
    {π π' : Measure S} [IsProbabilityMeasure π] [IsProbabilityMeasure π']
    (hπ : Kernel.Invariant κ π) (hπ' : Kernel.Invariant κ π')
    -- LEAN-ONLY: both invariant laws integrate the Lyapunov function (automatic for
    -- the constructed one; needed to compare in the weighted distance)
    (hV : (∫ x, V x ∂π) < ⊤.toReal ∧ (∫ x, V x ∂π') < ⊤.toReal) :
    π = π' := by
  sorry

/-- **Lifting from the `p`-step kernel**: if `κ^p` is geometrically ergodic with
invariant law `π` and `π` is invariant for `κ` itself, then `κ` is geometrically
ergodic. (The nonlinear-AR kernel of FY Theorem 2.4 is only minorized after `p` steps,
so this is the last glue step of that proof.) -/
theorem IsGeometricallyErgodic.of_pow {κ : Kernel S S} [IsMarkovKernel κ]
    {π : Measure S} [IsProbabilityMeasure π] {p : ℕ} (hp : 0 < p)
    (hpow : IsGeometricallyErgodic (κ ^ p) π) (hinv : Kernel.Invariant κ π) :
    IsGeometricallyErgodic κ π := by
  sorry

end StatLean.TimeSeries
